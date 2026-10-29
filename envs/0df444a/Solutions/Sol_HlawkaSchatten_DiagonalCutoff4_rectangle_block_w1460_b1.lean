-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1460_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:51.441782+00:00
-- url     : https://prove2.me/submissions/a0a080e2-a679-4cd9-b1f5-2d655267f593

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
theorem support_rectangle_w1460_s3_0 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1945371577/10000000000 : ℝ)*x 0 + (5414268339/10000000000 : ℝ)*x 1 + (5240491821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1945371577/10000000000 : ℝ)^1105 ≤ (2968620322481/25000000000000 : ℝ)^849 := by
    have hnat : (1945371577 : ℕ)^1105*25000000000000^849 ≤ 2968620322481^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945371577 10000000000 2968620322481 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414268339/10000000000 : ℝ)^1105 ≤ (4499805080331/10000000000000 : ℝ)^849 := by
    have hnat : (5414268339 : ℕ)^1105*10000000000000^849 ≤ 4499805080331^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414268339 10000000000 4499805080331 10000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240491821/10000000000 : ℝ)^1105 ≤ (2156373394681/5000000000000 : ℝ)^849 := by
    have hnat : (5240491821 : ℕ)^1105*5000000000000^849 ≤ 2156373394681^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240491821 10000000000 2156373394681 5000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1945371577/10000000000 : ℝ), (5414268339/10000000000 : ℝ), (5240491821/10000000000 : ℝ)] ![(2968620322481/25000000000000 : ℝ), (4499805080331/10000000000000 : ℝ), (2156373394681/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1945371577/10000000000 : ℝ)|^1105 ≤ (2968620322481/25000000000000 : ℝ)^849
        have hw : |(-1945371577/10000000000 : ℝ)|=(1945371577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414268339/10000000000 : ℝ)|^1105 ≤ (4499805080331/10000000000000 : ℝ)^849
        have hw : |(5414268339/10000000000 : ℝ)|=(5414268339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240491821/10000000000 : ℝ)|^1105 ≤ (2156373394681/5000000000000 : ℝ)^849
        have hw : |(5240491821/10000000000 : ℝ)|=(5240491821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s3_1 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348639357/10000000000 : ℝ)*x 0 + (-2033964639/10000000000 : ℝ)*x 1 + (1310122967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348639357/10000000000 : ℝ)^1105 ≤ (8857888079787/20000000000000 : ℝ)^849 := by
    have hnat : (5348639357 : ℕ)^1105*20000000000000^849 ≤ 8857888079787^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348639357 10000000000 8857888079787 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033964639/10000000000 : ℝ)^1105 ≤ (1258309119459/10000000000000 : ℝ)^849 := by
    have hnat : (2033964639 : ℕ)^1105*10000000000000^849 ≤ 1258309119459^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033964639 10000000000 1258309119459 10000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310122967/2500000000 : ℝ)^1105 ≤ (10781867099261/25000000000000 : ℝ)^849 := by
    have hnat : (1310122967 : ℕ)^1105*25000000000000^849 ≤ 10781867099261^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310122967 2500000000 10781867099261 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348639357/10000000000 : ℝ), (-2033964639/10000000000 : ℝ), (1310122967/2500000000 : ℝ)] ![(8857888079787/20000000000000 : ℝ), (1258309119459/10000000000000 : ℝ), (10781867099261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348639357/10000000000 : ℝ)|^1105 ≤ (8857888079787/20000000000000 : ℝ)^849
        have hw : |(5348639357/10000000000 : ℝ)|=(5348639357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2033964639/10000000000 : ℝ)|^1105 ≤ (1258309119459/10000000000000 : ℝ)^849
        have hw : |(-2033964639/10000000000 : ℝ)|=(2033964639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310122967/2500000000 : ℝ)|^1105 ≤ (10781867099261/25000000000000 : ℝ)^849
        have hw : |(1310122967/2500000000 : ℝ)|=(1310122967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s3_2 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348637899/10000000000 : ℝ)*x 0 + (2620246251/5000000000 : ℝ)*x 1 + (-1016982873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348637899/10000000000 : ℝ)^1105 ≤ (22144712342789/50000000000000 : ℝ)^849 := by
    have hnat : (5348637899 : ℕ)^1105*50000000000000^849 ≤ 22144712342789^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348637899 10000000000 22144712342789 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620246251/5000000000 : ℝ)^1105 ≤ (539093439849/1250000000000 : ℝ)^849 := by
    have hnat : (2620246251 : ℕ)^1105*1250000000000^849 ≤ 539093439849^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620246251 5000000000 539093439849 1250000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016982873/5000000000 : ℝ)^1105 ≤ (12583100108047/100000000000000 : ℝ)^849 := by
    have hnat : (1016982873 : ℕ)^1105*100000000000000^849 ≤ 12583100108047^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016982873 5000000000 12583100108047 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348637899/10000000000 : ℝ), (2620246251/5000000000 : ℝ), (-1016982873/5000000000 : ℝ)] ![(22144712342789/50000000000000 : ℝ), (539093439849/1250000000000 : ℝ), (12583100108047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348637899/10000000000 : ℝ)|^1105 ≤ (22144712342789/50000000000000 : ℝ)^849
        have hw : |(5348637899/10000000000 : ℝ)|=(5348637899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620246251/5000000000 : ℝ)|^1105 ≤ (539093439849/1250000000000 : ℝ)^849
        have hw : |(2620246251/5000000000 : ℝ)|=(2620246251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1016982873/5000000000 : ℝ)|^1105 ≤ (12583100108047/100000000000000 : ℝ)^849
        have hw : |(-1016982873/5000000000 : ℝ)|=(1016982873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s3_3 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2148070813/5000000000 : ℝ)*x 0 + (4109770129/10000000000 : ℝ)*x 1 + (2244989079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148070813/5000000000 : ℝ)^1105 ≤ (16649850419193/50000000000000 : ℝ)^849 := by
    have hnat : (2148070813 : ℕ)^1105*50000000000000^849 ≤ 16649850419193^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148070813 5000000000 16649850419193 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4109770129/10000000000 : ℝ)^1105 ≤ (7857989996399/25000000000000 : ℝ)^849 := by
    have hnat : (4109770129 : ℕ)^1105*25000000000000^849 ≤ 7857989996399^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109770129 10000000000 7857989996399 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244989079/5000000000 : ℝ)^1105 ≤ (1102135598881/3125000000000 : ℝ)^849 := by
    have hnat : (2244989079 : ℕ)^1105*3125000000000^849 ≤ 1102135598881^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244989079 5000000000 1102135598881 3125000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148070813/5000000000 : ℝ), (4109770129/10000000000 : ℝ), (2244989079/5000000000 : ℝ)] ![(16649850419193/50000000000000 : ℝ), (7857989996399/25000000000000 : ℝ), (1102135598881/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148070813/5000000000 : ℝ)|^1105 ≤ (16649850419193/50000000000000 : ℝ)^849
        have hw : |(2148070813/5000000000 : ℝ)|=(2148070813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4109770129/10000000000 : ℝ)|^1105 ≤ (7857989996399/25000000000000 : ℝ)^849
        have hw : |(4109770129/10000000000 : ℝ)|=(4109770129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244989079/5000000000 : ℝ)|^1105 ≤ (1102135598881/3125000000000 : ℝ)^849
        have hw : |(2244989079/5000000000 : ℝ)|=(2244989079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s3_4 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-972692843/5000000000 : ℝ)*x 0 + (5241178669/10000000000 : ℝ)*x 1 + (216543113/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (972692843/5000000000 : ℝ)^1105 ≤ (11874593379023/100000000000000 : ℝ)^849 := by
    have hnat : (972692843 : ℕ)^1105*100000000000000^849 ≤ 11874593379023^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972692843 5000000000 11874593379023 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241178669/10000000000 : ℝ)^1105 ≤ (43134824977713/100000000000000 : ℝ)^849 := by
    have hnat : (5241178669 : ℕ)^1105*100000000000000^849 ≤ 43134824977713^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241178669 10000000000 43134824977713 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216543113/400000000 : ℝ)^1105 ≤ (44990581628043/100000000000000 : ℝ)^849 := by
    have hnat : (216543113 : ℕ)^1105*100000000000000^849 ≤ 44990581628043^849*400000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216543113 400000000 44990581628043 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-972692843/5000000000 : ℝ), (5241178669/10000000000 : ℝ), (216543113/400000000 : ℝ)] ![(11874593379023/100000000000000 : ℝ), (43134824977713/100000000000000 : ℝ), (44990581628043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-972692843/5000000000 : ℝ)|^1105 ≤ (11874593379023/100000000000000 : ℝ)^849
        have hw : |(-972692843/5000000000 : ℝ)|=(972692843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241178669/10000000000 : ℝ)|^1105 ≤ (43134824977713/100000000000000 : ℝ)^849
        have hw : |(5241178669/10000000000 : ℝ)|=(5241178669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216543113/400000000 : ℝ)|^1105 ≤ (44990581628043/100000000000000 : ℝ)^849
        have hw : |(216543113/400000000 : ℝ)|=(216543113/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s3_5 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (42426633/80000000 : ℝ)*x 0 + (-930439899/5000000000 : ℝ)*x 1 + (541357781/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42426633/80000000 : ℝ)^1105 ≤ (21900870836617/50000000000000 : ℝ)^849 := by
    have hnat : (42426633 : ℕ)^1105*50000000000000^849 ≤ 21900870836617^849*80000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42426633 80000000 21900870836617 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (930439899/5000000000 : ℝ)^1105 ≤ (2801919212899/25000000000000 : ℝ)^849 := by
    have hnat : (930439899 : ℕ)^1105*25000000000000^849 ≤ 2801919212899^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930439899 5000000000 2801919212899 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541357781/1000000000 : ℝ)^1105 ≤ (44990581465793/100000000000000 : ℝ)^849 := by
    have hnat : (541357781 : ℕ)^1105*100000000000000^849 ≤ 44990581465793^849*1000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541357781 1000000000 44990581465793 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42426633/80000000 : ℝ), (-930439899/5000000000 : ℝ), (541357781/1000000000 : ℝ)] ![(21900870836617/50000000000000 : ℝ), (2801919212899/25000000000000 : ℝ), (44990581465793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42426633/80000000 : ℝ)|^1105 ≤ (21900870836617/50000000000000 : ℝ)^849
        have hw : |(42426633/80000000 : ℝ)|=(42426633/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-930439899/5000000000 : ℝ)|^1105 ≤ (2801919212899/25000000000000 : ℝ)^849
        have hw : |(-930439899/5000000000 : ℝ)|=(930439899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541357781/1000000000 : ℝ)|^1105 ≤ (44990581465793/100000000000000 : ℝ)^849
        have hw : |(541357781/1000000000 : ℝ)|=(541357781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s3_6 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530332811/1000000000 : ℝ)*x 0 + (169174331/312500000 : ℝ)*x 1 + (-186088011/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530332811/1000000000 : ℝ)^1105 ≤ (43801730762263/100000000000000 : ℝ)^849 := by
    have hnat : (530332811 : ℕ)^1105*100000000000000^849 ≤ 43801730762263^849*1000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530332811 1000000000 43801730762263 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169174331/312500000 : ℝ)^1105 ≤ (8998117984879/20000000000000 : ℝ)^849 := by
    have hnat : (169174331 : ℕ)^1105*20000000000000^849 ≤ 8998117984879^849*312500000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169174331 312500000 8998117984879 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (186088011/1000000000 : ℝ)^1105 ≤ (5603839648657/50000000000000 : ℝ)^849 := by
    have hnat : (186088011 : ℕ)^1105*50000000000000^849 ≤ 5603839648657^849*1000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186088011 1000000000 5603839648657 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530332811/1000000000 : ℝ), (169174331/312500000 : ℝ), (-186088011/1000000000 : ℝ)] ![(43801730762263/100000000000000 : ℝ), (8998117984879/20000000000000 : ℝ), (5603839648657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530332811/1000000000 : ℝ)|^1105 ≤ (43801730762263/100000000000000 : ℝ)^849
        have hw : |(530332811/1000000000 : ℝ)|=(530332811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169174331/312500000 : ℝ)|^1105 ≤ (8998117984879/20000000000000 : ℝ)^849
        have hw : |(169174331/312500000 : ℝ)|=(169174331/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-186088011/1000000000 : ℝ)|^1105 ≤ (5603839648657/50000000000000 : ℝ)^849
        have hw : |(-186088011/1000000000 : ℝ)|=(186088011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s3_7 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1074043189/2500000000 : ℝ)*x 0 + (2244238613/5000000000 : ℝ)*x 1 + (2055639967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074043189/2500000000 : ℝ)^1105 ≤ (33300014886309/100000000000000 : ℝ)^849 := by
    have hnat : (1074043189 : ℕ)^1105*100000000000000^849 ≤ 33300014886309^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074043189 2500000000 33300014886309 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244238613/5000000000 : ℝ)^1105 ≤ (35252995308871/100000000000000 : ℝ)^849 := by
    have hnat : (2244238613 : ℕ)^1105*100000000000000^849 ≤ 35252995308871^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244238613 5000000000 35252995308871 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055639967/5000000000 : ℝ)^1105 ≤ (31446989793509/100000000000000 : ℝ)^849 := by
    have hnat : (2055639967 : ℕ)^1105*100000000000000^849 ≤ 31446989793509^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055639967 5000000000 31446989793509 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074043189/2500000000 : ℝ), (2244238613/5000000000 : ℝ), (2055639967/5000000000 : ℝ)] ![(33300014886309/100000000000000 : ℝ), (35252995308871/100000000000000 : ℝ), (31446989793509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074043189/2500000000 : ℝ)|^1105 ≤ (33300014886309/100000000000000 : ℝ)^849
        have hw : |(1074043189/2500000000 : ℝ)|=(1074043189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244238613/5000000000 : ℝ)|^1105 ≤ (35252995308871/100000000000000 : ℝ)^849
        have hw : |(2244238613/5000000000 : ℝ)|=(2244238613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2055639967/5000000000 : ℝ)|^1105 ≤ (31446989793509/100000000000000 : ℝ)^849
        have hw : |(2055639967/5000000000 : ℝ)|=(2055639967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1460_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11251/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3733/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (10527/100000 : ℝ) ^ (4419/1024 : ℝ) ≤ (754630505792713/12500000000000000000 : ℝ) := by
    have hpowers : (10527/100000 : ℝ)^4419 ≤ (754630505792713/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10527 : ℕ)^4419*12500000000000000000^1024 ≤ 754630505792713^1024*100000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10527 100000 754630505792713 12500000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10527/100000 : ℝ)) (X := (754630505792713/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15709/100000 : ℝ) ^ (4419/1024 : ℝ) ≤ (1061415842537163/3125000000000000000 : ℝ) := by
    have hpowers : (15709/100000 : ℝ)^4419 ≤ (1061415842537163/3125000000000000000 : ℝ)^1024 := by
      have hnat : (15709 : ℕ)^4419*3125000000000000000^1024 ≤ 1061415842537163^1024*100000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15709 100000 1061415842537163 3125000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15709/100000 : ℝ)) (X := (1061415842537163/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250754630505792713/6250000000000000000 : ℝ) ≤ (10000279775804463/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (6250754630505792713/6250000000000000000 : ℝ)^1024 ≤ (10000279775804463/10000000000000000 : ℝ)^4419 := by
      have hnat : (6250754630505792713 : ℕ)^1024*10000000000000000^4419 ≤ 10000279775804463^4419*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250754630505792713 6250000000000000000 10000279775804463 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000279775804463/10000000000000000 : ℝ)) (X := (6250754630505792713/6250000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501000058775188273/2500000000000000000 : ℝ) ≤ (250023170465309/250000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (2501000058775188273/2500000000000000000 : ℝ)^1024 ≤ (250023170465309/250000000000000 : ℝ)^4419 := by
      have hnat : (2501000058775188273 : ℕ)^1024*250000000000000^4419 ≤ 250023170465309^4419*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501000058775188273 2500000000000000000 250023170465309 250000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250023170465309/250000000000000 : ℝ)) (X := (2501000058775188273/2500000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563561415842537163/1562500000000000000 : ℝ) ≤ (10001573861420257/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (1563561415842537163/1562500000000000000 : ℝ)^1024 ≤ (10001573861420257/10000000000000000 : ℝ)^4419 := by
      have hnat : (1563561415842537163 : ℕ)^1024*10000000000000000^4419 ≤ 10001573861420257^4419*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563561415842537163 1562500000000000000 10001573861420257 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001573861420257/10000000000000000 : ℝ)) (X := (1563561415842537163/1562500000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(754630505792713/12500000000000000000 : ℝ) ≤ ((12951956739735315957/12955000000000000000 : ℝ)+2*(647042807897/518200000000000 : ℝ)*(10527/100000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (12951956739735315957/12955000000000000000 : ℝ)+2*(647042807897/518200000000000 : ℝ)*(10527/100000 : ℝ)=(10000279775804463/10000000000000000 : ℝ) by norm_num, show 1+2*(754630505792713/12500000000000000000 : ℝ)=(6250754630505792713/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1061415842537163/3125000000000000000 : ℝ)+(754630505792713/12500000000000000000 : ℝ) ≤ ((12951956739735315957/12955000000000000000 : ℝ)+(647042807897/518200000000000 : ℝ)*((15709/100000 : ℝ)+(10527/100000 : ℝ)))^(4419/1024 : ℝ) := by
    rw [show (12951956739735315957/12955000000000000000 : ℝ)+(647042807897/518200000000000 : ℝ)*((15709/100000 : ℝ)+(10527/100000 : ℝ))=(250023170465309/250000000000000 : ℝ) by norm_num, show 1+(1061415842537163/3125000000000000000 : ℝ)+(754630505792713/12500000000000000000 : ℝ)=(2501000058775188273/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1061415842537163/3125000000000000000 : ℝ) ≤ ((12951956739735315957/12955000000000000000 : ℝ)+2*(647042807897/518200000000000 : ℝ)*(15709/100000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (12951956739735315957/12955000000000000000 : ℝ)+2*(647042807897/518200000000000 : ℝ)*(15709/100000 : ℝ)=(10001573861420257/10000000000000000 : ℝ) by norm_num, show 1+2*(1061415842537163/3125000000000000000 : ℝ)=(1563561415842537163/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12951956739735315957/12955000000000000000 : ℝ)*(X 1 0+X 2 0)+(647042807897/518200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (10527/100000 : ℝ)) (hi := (15709/100000 : ℝ)) (c := (12951956739735315957/12955000000000000000 : ℝ)) (alpha := (647042807897/518200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12951956739735315957/12955000000000000000 : ℝ)*(X 0 1+X 2 1)+(647042807897/518200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (10527/100000 : ℝ)) (hi := (15709/100000 : ℝ)) (c := (12951956739735315957/12955000000000000000 : ℝ)) (alpha := (647042807897/518200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12951956739735315957/12955000000000000000 : ℝ)*(X 0 2+X 1 2)+(647042807897/518200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (10527/100000 : ℝ)) (hi := (15709/100000 : ℝ)) (c := (12951956739735315957/12955000000000000000 : ℝ)) (alpha := (647042807897/518200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1945371577/10000000000 : ℝ)*X 0 0+(5414268339/10000000000 : ℝ)*X 0 1+(5240491821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348639357/10000000000 : ℝ)*X 1 0+(-2033964639/10000000000 : ℝ)*X 1 1+(1310122967/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348637899/10000000000 : ℝ)*X 2 0+(2620246251/5000000000 : ℝ)*X 2 1+(-1016982873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2148070813/5000000000 : ℝ)*X 0 0+(4109770129/10000000000 : ℝ)*X 0 1+(2244989079/5000000000 : ℝ)*X 0 2+(2148070813/5000000000 : ℝ)*X 1 0+(4109770129/10000000000 : ℝ)*X 1 1+(2244989079/5000000000 : ℝ)*X 1 2+(2148070813/5000000000 : ℝ)*X 2 0+(4109770129/10000000000 : ℝ)*X 2 1+(2244989079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-972692843/5000000000 : ℝ)*X 0 0+(5241178669/10000000000 : ℝ)*X 0 1+(216543113/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42426633/80000000 : ℝ)*X 1 0+(-930439899/5000000000 : ℝ)*X 1 1+(541357781/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530332811/1000000000 : ℝ)*X 2 0+(169174331/312500000 : ℝ)*X 2 1+(-186088011/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1074043189/2500000000 : ℝ)*X 0 0+(2244238613/5000000000 : ℝ)*X 0 1+(2055639967/5000000000 : ℝ)*X 0 2+(1074043189/2500000000 : ℝ)*X 1 0+(2244238613/5000000000 : ℝ)*X 1 1+(2055639967/5000000000 : ℝ)*X 1 2+(1074043189/2500000000 : ℝ)*X 2 0+(2244238613/5000000000 : ℝ)*X 2 1+(2055639967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (224767275932673076209189/25910000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2128217657/100000000000000 : ℝ)*(base19) + (239628557/100000000000000 : ℝ)*(base23) + (171909619/100000000000000 : ℝ)*(upper3) + (13667501/100000000000000 : ℝ)*(lower4) + (419240608497877/10000000000000 : ℝ)*(major0) + (419240608497877/10000000000000 : ℝ)*(major1) + (4192406084978771/100000000000000 : ℝ)*(major2) + (179830842361573/3125000000000 : ℝ)*(sp0) + (359664686220993/6250000000000 : ℝ)*(sp1) + (5754596086728927/100000000000000 : ℝ)*(sp2) + (1315079377303279/50000000000000 : ℝ)*(sp3) + (50152183209/100000000000000 : ℝ)*(sp4) + (40781396061/100000000000000 : ℝ)*(sp6) + (8009216651/50000000000000 : ℝ)*(sp7) + (2630174773039861/100000000000000 : ℝ)*(f.failure) + (1150927421550709/20000000000000 : ℝ)*(f.sum) + (198757709180597/51820000000000000000000000000 : ℝ)*base65 + (129377906393259211/129550000000000000000000000000000 : ℝ)*base68 + (8564881354398298847/1295500000000000000000000000000000 : ℝ)*base69 + (460890670901390789/129550000000000000000000000000000 : ℝ)*base71 + (115617471721637/51820000000000000000000000000 : ℝ)*base73 + (11774723215238201153/1295500000000000000000000000000000 : ℝ)*base76 + (1095929040951798289/129550000000000000000000000000000 : ℝ)*base77 + (1772338402909551711/129550000000000000000000000000000 : ℝ)*base80 + (19580525255489/2591000000000000000000000000 : ℝ)*base81 + (62208863/10000000000000000000000 : ℝ)*base89 + (62208863/10000000000000000000000 : ℝ)*base91 + (37791137/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (599678531043824624588875917/161937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6930789/3125000000000 : ℝ)*(base8) + (463175199/50000000000000 : ℝ)*(base21) + (7319789/5000000000000 : ℝ)*(upper2) + (8964037/50000000000000 : ℝ)*(lower4) + (1056453330464573/25000000000000 : ℝ)*(major0) + (1056453330464573/25000000000000 : ℝ)*(major1) + (1056453330464573/25000000000000 : ℝ)*(major2) + (11843681/25000000000000 : ℝ)*(sp0) + (6481428751/100000000000000 : ℝ)*(sp1) + (4130965291/100000000000000 : ℝ)*(sp2) + (5800492899663969/100000000000000 : ℝ)*(sp4) + (5800486687395189/100000000000000 : ℝ)*(sp5) + (23201952446033/400000000000 : ℝ)*(sp6) + (82847917232949/3125000000000 : ℝ)*(sp7) + (82847917232949/3125000000000 : ℝ)*(f.failure) + (290024658441197/5000000000000 : ℝ)*(f.sum) + (5790070473671/1619375000000000000000000000 : ℝ)*base66 + (2389077751702258639/323875000000000000000000000000000 : ℝ)*base68 + (1240943149733241361/323875000000000000000000000000000 : ℝ)*base69 + (1877474138117883639/323875000000000000000000000000000 : ℝ)*base72 + (31077253879473/12955000000000000000000000000 : ℝ)*base74 + (1780508170078366361/323875000000000000000000000000000 : ℝ)*base75 + (8415422870031241361/323875000000000000000000000000000 : ℝ)*base77 + (2557662238480866361/323875000000000000000000000000000 : ℝ)*base79 + (3544235711023/809687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (181633/312500000000000000000 : ℝ)*base90 + (181633/312500000000000000000 : ℝ)*base92 + (181633/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1460_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3733/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1460_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1460_s4_0 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-973065189/5000000000 : ℝ)*x 0 + (2703859561/5000000000 : ℝ)*x 1 + (5246540681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (973065189/5000000000 : ℝ)^1105 ≤ (475220397613/4000000000000 : ℝ)^849 := by
    have hnat : (973065189 : ℕ)^1105*4000000000000^849 ≤ 475220397613^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973065189 5000000000 475220397613 4000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703859561/5000000000 : ℝ)^1105 ≤ (22463610285831/50000000000000 : ℝ)^849 := by
    have hnat : (2703859561 : ℕ)^1105*50000000000000^849 ≤ 22463610285831^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703859561 5000000000 22463610285831 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246540681/10000000000 : ℝ)^1105 ≤ (8638453894383/20000000000000 : ℝ)^849 := by
    have hnat : (5246540681 : ℕ)^1105*20000000000000^849 ≤ 8638453894383^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246540681 10000000000 8638453894383 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-973065189/5000000000 : ℝ), (2703859561/5000000000 : ℝ), (5246540681/10000000000 : ℝ)] ![(475220397613/4000000000000 : ℝ), (22463610285831/50000000000000 : ℝ), (8638453894383/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-973065189/5000000000 : ℝ)|^1105 ≤ (475220397613/4000000000000 : ℝ)^849
        have hw : |(-973065189/5000000000 : ℝ)|=(973065189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703859561/5000000000 : ℝ)|^1105 ≤ (22463610285831/50000000000000 : ℝ)^849
        have hw : |(2703859561/5000000000 : ℝ)|=(2703859561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246540681/10000000000 : ℝ)|^1105 ≤ (8638453894383/20000000000000 : ℝ)^849
        have hw : |(5246540681/10000000000 : ℝ)|=(5246540681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s4_1 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5346941129/10000000000 : ℝ)*x 0 + (-405637429/2000000000 : ℝ)*x 1 + (524654071/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346941129/10000000000 : ℝ)^1105 ≤ (22135569449789/50000000000000 : ℝ)^849 := by
    have hnat : (5346941129 : ℕ)^1105*50000000000000^849 ≤ 22135569449789^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346941129 10000000000 22135569449789 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405637429/2000000000 : ℝ)^1105 ≤ (3134147827189/25000000000000 : ℝ)^849 := by
    have hnat : (405637429 : ℕ)^1105*25000000000000^849 ≤ 3134147827189^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405637429 2000000000 3134147827189 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524654071/1000000000 : ℝ)^1105 ≤ (43192269782647/100000000000000 : ℝ)^849 := by
    have hnat : (524654071 : ℕ)^1105*100000000000000^849 ≤ 43192269782647^849*1000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524654071 1000000000 43192269782647 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346941129/10000000000 : ℝ), (-405637429/2000000000 : ℝ), (524654071/1000000000 : ℝ)] ![(22135569449789/50000000000000 : ℝ), (3134147827189/25000000000000 : ℝ), (43192269782647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346941129/10000000000 : ℝ)|^1105 ≤ (22135569449789/50000000000000 : ℝ)^849
        have hw : |(5346941129/10000000000 : ℝ)|=(5346941129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405637429/2000000000 : ℝ)|^1105 ≤ (3134147827189/25000000000000 : ℝ)^849
        have hw : |(-405637429/2000000000 : ℝ)|=(405637429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524654071/1000000000 : ℝ)|^1105 ≤ (43192269782647/100000000000000 : ℝ)^849
        have hw : |(524654071/1000000000 : ℝ)|=(524654071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s4_2 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069388239/2000000000 : ℝ)*x 0 + (1311635173/2500000000 : ℝ)*x 1 + (-2028187079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069388239/2000000000 : ℝ)^1105 ≤ (8854227922163/20000000000000 : ℝ)^849 := by
    have hnat : (1069388239 : ℕ)^1105*20000000000000^849 ≤ 8854227922163^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069388239 2000000000 8854227922163 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311635173/2500000000 : ℝ)^1105 ≤ (43192269589779/100000000000000 : ℝ)^849 := by
    have hnat : (1311635173 : ℕ)^1105*100000000000000^849 ≤ 43192269589779^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311635173 2500000000 43192269589779 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2028187079/10000000000 : ℝ)^1105 ≤ (6268295388893/50000000000000 : ℝ)^849 := by
    have hnat : (2028187079 : ℕ)^1105*50000000000000^849 ≤ 6268295388893^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028187079 10000000000 6268295388893 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069388239/2000000000 : ℝ), (1311635173/2500000000 : ℝ), (-2028187079/10000000000 : ℝ)] ![(8854227922163/20000000000000 : ℝ), (43192269589779/100000000000000 : ℝ), (6268295388893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069388239/2000000000 : ℝ)|^1105 ≤ (8854227922163/20000000000000 : ℝ)^849
        have hw : |(1069388239/2000000000 : ℝ)|=(1069388239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311635173/2500000000 : ℝ)|^1105 ≤ (43192269589779/100000000000000 : ℝ)^849
        have hw : |(1311635173/2500000000 : ℝ)|=(1311635173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2028187079/10000000000 : ℝ)|^1105 ≤ (6268295388893/50000000000000 : ℝ)^849
        have hw : |(-2028187079/10000000000 : ℝ)|=(2028187079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s4_3 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4296607333/10000000000 : ℝ)*x 0 + (2061747571/5000000000 : ℝ)*x 1 + (559517721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296607333/10000000000 : ℝ)^1105 ≤ (33304399089151/100000000000000 : ℝ)^849 := by
    have hnat : (4296607333 : ℕ)^1105*100000000000000^849 ≤ 33304399089151^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296607333 10000000000 33304399089151 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061747571/5000000000 : ℝ)^1105 ≤ (631373018483/2000000000000 : ℝ)^849 := by
    have hnat : (2061747571 : ℕ)^1105*2000000000000^849 ≤ 631373018483^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061747571 5000000000 631373018483 2000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559517721/1250000000 : ℝ)^1105 ≤ (7025389995459/20000000000000 : ℝ)^849 := by
    have hnat : (559517721 : ℕ)^1105*20000000000000^849 ≤ 7025389995459^849*1250000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559517721 1250000000 7025389995459 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296607333/10000000000 : ℝ), (2061747571/5000000000 : ℝ), (559517721/1250000000 : ℝ)] ![(33304399089151/100000000000000 : ℝ), (631373018483/2000000000000 : ℝ), (7025389995459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296607333/10000000000 : ℝ)|^1105 ≤ (33304399089151/100000000000000 : ℝ)^849
        have hw : |(4296607333/10000000000 : ℝ)|=(4296607333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2061747571/5000000000 : ℝ)|^1105 ≤ (631373018483/2000000000000 : ℝ)^849
        have hw : |(2061747571/5000000000 : ℝ)|=(2061747571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559517721/1250000000 : ℝ)|^1105 ≤ (7025389995459/20000000000000 : ℝ)^849
        have hw : |(559517721/1250000000 : ℝ)|=(559517721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s4_4 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-486535447/2500000000 : ℝ)*x 0 + (2623565699/5000000000 : ℝ)*x 1 + (2703562683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486535447/2500000000 : ℝ)^1105 ≤ (1188060059783/10000000000000 : ℝ)^849 := by
    have hnat : (486535447 : ℕ)^1105*10000000000000^849 ≤ 1188060059783^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486535447 2500000000 1188060059783 10000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623565699/5000000000 : ℝ)^1105 ≤ (2699912440303/6250000000000 : ℝ)^849 := by
    have hnat : (2623565699 : ℕ)^1105*6250000000000^849 ≤ 2699912440303^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623565699 5000000000 2699912440303 6250000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703562683/5000000000 : ℝ)^1105 ≤ (11230200084497/25000000000000 : ℝ)^849 := by
    have hnat : (2703562683 : ℕ)^1105*25000000000000^849 ≤ 11230200084497^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703562683 5000000000 11230200084497 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-486535447/2500000000 : ℝ), (2623565699/5000000000 : ℝ), (2703562683/5000000000 : ℝ)] ![(1188060059783/10000000000000 : ℝ), (2699912440303/6250000000000 : ℝ), (11230200084497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-486535447/2500000000 : ℝ)|^1105 ≤ (1188060059783/10000000000000 : ℝ)^849
        have hw : |(-486535447/2500000000 : ℝ)|=(486535447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623565699/5000000000 : ℝ)|^1105 ≤ (2699912440303/6250000000000 : ℝ)^849
        have hw : |(2623565699/5000000000 : ℝ)|=(2623565699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703562683/5000000000 : ℝ)|^1105 ≤ (11230200084497/25000000000000 : ℝ)^849
        have hw : |(2703562683/5000000000 : ℝ)|=(2703562683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s4_5 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1060983113/2000000000 : ℝ)*x 0 + (-58362577/312500000 : ℝ)*x 1 + (5407125363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060983113/2000000000 : ℝ)^1105 ≤ (10954699059331/25000000000000 : ℝ)^849 := by
    have hnat : (1060983113 : ℕ)^1105*25000000000000^849 ≤ 10954699059331^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060983113 2000000000 10954699059331 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58362577/312500000 : ℝ)^1105 ≤ (5630201720613/50000000000000 : ℝ)^849 := by
    have hnat : (58362577 : ℕ)^1105*50000000000000^849 ≤ 5630201720613^849*312500000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58362577 312500000 5630201720613 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407125363/10000000000 : ℝ)^1105 ≤ (898416006111/2000000000000 : ℝ)^849 := by
    have hnat : (5407125363 : ℕ)^1105*2000000000000^849 ≤ 898416006111^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407125363 10000000000 898416006111 2000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060983113/2000000000 : ℝ), (-58362577/312500000 : ℝ), (5407125363/10000000000 : ℝ)] ![(10954699059331/25000000000000 : ℝ), (5630201720613/50000000000000 : ℝ), (898416006111/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060983113/2000000000 : ℝ)|^1105 ≤ (10954699059331/25000000000000 : ℝ)^849
        have hw : |(1060983113/2000000000 : ℝ)|=(1060983113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58362577/312500000 : ℝ)|^1105 ≤ (5630201720613/50000000000000 : ℝ)^849
        have hw : |(-58362577/312500000 : ℝ)|=(58362577/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407125363/10000000000 : ℝ)|^1105 ≤ (898416006111/2000000000000 : ℝ)^849
        have hw : |(5407125363/10000000000 : ℝ)|=(5407125363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s4_6 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5304915591/10000000000 : ℝ)*x 0 + (5407125347/10000000000 : ℝ)*x 1 + (-1867602451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304915591/10000000000 : ℝ)^1105 ≤ (21909398258421/50000000000000 : ℝ)^849 := by
    have hnat : (5304915591 : ℕ)^1105*50000000000000^849 ≤ 21909398258421^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304915591 10000000000 21909398258421 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407125347/10000000000 : ℝ)^1105 ≤ (22460400066273/50000000000000 : ℝ)^849 := by
    have hnat : (5407125347 : ℕ)^1105*50000000000000^849 ≤ 22460400066273^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407125347 10000000000 22460400066273 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867602451/10000000000 : ℝ)^1105 ≤ (1126040333921/10000000000000 : ℝ)^849 := by
    have hnat : (1867602451 : ℕ)^1105*10000000000000^849 ≤ 1126040333921^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867602451 10000000000 1126040333921 10000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304915591/10000000000 : ℝ), (5407125347/10000000000 : ℝ), (-1867602451/10000000000 : ℝ)] ![(21909398258421/50000000000000 : ℝ), (22460400066273/50000000000000 : ℝ), (1126040333921/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304915591/10000000000 : ℝ)|^1105 ≤ (21909398258421/50000000000000 : ℝ)^849
        have hw : |(5304915591/10000000000 : ℝ)|=(5304915591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407125347/10000000000 : ℝ)|^1105 ≤ (22460400066273/50000000000000 : ℝ)^849
        have hw : |(5407125347/10000000000 : ℝ)|=(5407125347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1867602451/10000000000 : ℝ)|^1105 ≤ (1126040333921/10000000000000 : ℝ)^849
        have hw : |(-1867602451/10000000000 : ℝ)|=(1867602451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s4_7 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2148316301/5000000000 : ℝ)*x 0 + (2237424763/5000000000 : ℝ)*x 1 + (4124794053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148316301/5000000000 : ℝ)^1105 ≤ (8326163504497/25000000000000 : ℝ)^849 := by
    have hnat : (2148316301 : ℕ)^1105*25000000000000^849 ≤ 8326163504497^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148316301 5000000000 8326163504497 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237424763/5000000000 : ℝ)^1105 ≤ (35113751733547/100000000000000 : ℝ)^849 := by
    have hnat : (2237424763 : ℕ)^1105*100000000000000^849 ≤ 35113751733547^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237424763 5000000000 35113751733547 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4124794053/10000000000 : ℝ)^1105 ≤ (15790797113923/50000000000000 : ℝ)^849 := by
    have hnat : (4124794053 : ℕ)^1105*50000000000000^849 ≤ 15790797113923^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124794053 10000000000 15790797113923 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148316301/5000000000 : ℝ), (2237424763/5000000000 : ℝ), (4124794053/10000000000 : ℝ)] ![(8326163504497/25000000000000 : ℝ), (35113751733547/100000000000000 : ℝ), (15790797113923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148316301/5000000000 : ℝ)|^1105 ≤ (8326163504497/25000000000000 : ℝ)^849
        have hw : |(2148316301/5000000000 : ℝ)|=(2148316301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237424763/5000000000 : ℝ)|^1105 ≤ (35113751733547/100000000000000 : ℝ)^849
        have hw : |(2237424763/5000000000 : ℝ)|=(2237424763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4124794053/10000000000 : ℝ)|^1105 ≤ (15790797113923/50000000000000 : ℝ)^849
        have hw : |(4124794053/10000000000 : ℝ)|=(4124794053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1460_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3733/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (569/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2959/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3733/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3733/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3733/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3733/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3733/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3733/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11251/100000 : ℝ) ^ (4419/1024 : ℝ) ≤ (4022092145945083/50000000000000000000 : ℝ) := by
    have hpowers : (11251/100000 : ℝ)^4419 ≤ (4022092145945083/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11251 : ℕ)^4419*50000000000000000000^1024 ≤ 4022092145945083^1024*100000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11251 100000 4022092145945083 50000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11251/100000 : ℝ)) (X := (4022092145945083/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3733/25000 : ℝ) ^ (4419/1024 : ℝ) ≤ (27287529481636899/100000000000000000000 : ℝ) := by
    have hpowers : (3733/25000 : ℝ)^4419 ≤ (27287529481636899/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3733 : ℕ)^4419*100000000000000000000^1024 ≤ 27287529481636899^1024*25000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3733 25000 27287529481636899 100000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3733/25000 : ℝ)) (X := (27287529481636899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004022092145945083/25000000000000000000 : ℝ) ≤ (2500093196828361/2500000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (25004022092145945083/25000000000000000000 : ℝ)^1024 ≤ (2500093196828361/2500000000000000 : ℝ)^4419 := by
      have hnat : (25004022092145945083 : ℕ)^1024*2500000000000000^4419 ≤ 2500093196828361^4419*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004022092145945083 25000000000000000000 2500093196828361 2500000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500093196828361/2500000000000000 : ℝ)) (X := (25004022092145945083/25000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007066342754705413/20000000000000000000 : ℝ) ≤ (2000163723763503/2000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (20007066342754705413/20000000000000000000 : ℝ)^1024 ≤ (2000163723763503/2000000000000000 : ℝ)^4419 := by
      have hnat : (20007066342754705413 : ℕ)^1024*2000000000000000^4419 ≤ 2000163723763503^4419*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007066342754705413 20000000000000000000 2000163723763503 2000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000163723763503/2000000000000000 : ℝ)) (X := (20007066342754705413/20000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027287529481636899/50000000000000000000 : ℝ) ≤ (5000632225160793/5000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (50027287529481636899/50000000000000000000 : ℝ)^1024 ≤ (5000632225160793/5000000000000000 : ℝ)^4419 := by
      have hnat : (50027287529481636899 : ℕ)^1024*5000000000000000^4419 ≤ 5000632225160793^4419*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027287529481636899 50000000000000000000 5000632225160793 5000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000632225160793/5000000000000000 : ℝ)) (X := (50027287529481636899/50000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4022092145945083/50000000000000000000 : ℝ) ≤ ((6133556688266030287/6135000000000000000 : ℝ)+2*(148610501357/122700000000000 : ℝ)*(11251/100000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (6133556688266030287/6135000000000000000 : ℝ)+2*(148610501357/122700000000000 : ℝ)*(11251/100000 : ℝ)=(2500093196828361/2500000000000000 : ℝ) by norm_num, show 1+2*(4022092145945083/50000000000000000000 : ℝ)=(25004022092145945083/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27287529481636899/100000000000000000000 : ℝ)+(4022092145945083/50000000000000000000 : ℝ) ≤ ((6133556688266030287/6135000000000000000 : ℝ)+(148610501357/122700000000000 : ℝ)*((3733/25000 : ℝ)+(11251/100000 : ℝ)))^(4419/1024 : ℝ) := by
    rw [show (6133556688266030287/6135000000000000000 : ℝ)+(148610501357/122700000000000 : ℝ)*((3733/25000 : ℝ)+(11251/100000 : ℝ))=(2000163723763503/2000000000000000 : ℝ) by norm_num, show 1+(27287529481636899/100000000000000000000 : ℝ)+(4022092145945083/50000000000000000000 : ℝ)=(20007066342754705413/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27287529481636899/100000000000000000000 : ℝ) ≤ ((6133556688266030287/6135000000000000000 : ℝ)+2*(148610501357/122700000000000 : ℝ)*(3733/25000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (6133556688266030287/6135000000000000000 : ℝ)+2*(148610501357/122700000000000 : ℝ)*(3733/25000 : ℝ)=(5000632225160793/5000000000000000 : ℝ) by norm_num, show 1+2*(27287529481636899/100000000000000000000 : ℝ)=(50027287529481636899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6133556688266030287/6135000000000000000 : ℝ)*(X 1 0+X 2 0)+(148610501357/122700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (3733/25000 : ℝ)) (c := (6133556688266030287/6135000000000000000 : ℝ)) (alpha := (148610501357/122700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6133556688266030287/6135000000000000000 : ℝ)*(X 0 1+X 2 1)+(148610501357/122700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (3733/25000 : ℝ)) (c := (6133556688266030287/6135000000000000000 : ℝ)) (alpha := (148610501357/122700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6133556688266030287/6135000000000000000 : ℝ)*(X 0 2+X 1 2)+(148610501357/122700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (3733/25000 : ℝ)) (c := (6133556688266030287/6135000000000000000 : ℝ)) (alpha := (148610501357/122700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-973065189/5000000000 : ℝ)*X 0 0+(2703859561/5000000000 : ℝ)*X 0 1+(5246540681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346941129/10000000000 : ℝ)*X 1 0+(-405637429/2000000000 : ℝ)*X 1 1+(524654071/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069388239/2000000000 : ℝ)*X 2 0+(1311635173/2500000000 : ℝ)*X 2 1+(-2028187079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4296607333/10000000000 : ℝ)*X 0 0+(2061747571/5000000000 : ℝ)*X 0 1+(559517721/1250000000 : ℝ)*X 0 2+(4296607333/10000000000 : ℝ)*X 1 0+(2061747571/5000000000 : ℝ)*X 1 1+(559517721/1250000000 : ℝ)*X 1 2+(4296607333/10000000000 : ℝ)*X 2 0+(2061747571/5000000000 : ℝ)*X 2 1+(559517721/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-486535447/2500000000 : ℝ)*X 0 0+(2623565699/5000000000 : ℝ)*X 0 1+(2703562683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060983113/2000000000 : ℝ)*X 1 0+(-58362577/312500000 : ℝ)*X 1 1+(5407125363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304915591/10000000000 : ℝ)*X 2 0+(5407125347/10000000000 : ℝ)*X 2 1+(-1867602451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148316301/5000000000 : ℝ)*X 0 0+(2237424763/5000000000 : ℝ)*X 0 1+(4124794053/10000000000 : ℝ)*X 0 2+(2148316301/5000000000 : ℝ)*X 1 0+(2237424763/5000000000 : ℝ)*X 1 1+(4124794053/10000000000 : ℝ)*X 1 2+(2148316301/5000000000 : ℝ)*X 2 0+(2237424763/5000000000 : ℝ)*X 2 1+(4124794053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194753716887505324217781189/20450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (209580171/12500000000000 : ℝ)*(base19) + (861204763/50000000000000 : ℝ)*(base23) + (165464051/100000000000000 : ℝ)*(upper3) + (8238467/50000000000000 : ℝ)*(upper4) + (14990703/6250000000000 : ℝ)*(upper5) + (904011199147147/20000000000000 : ℝ)*(major0) + (904011199147147/20000000000000 : ℝ)*(major1) + (565006999466967/12500000000000 : ℝ)*(major2) + (96942811008327/1562500000000 : ℝ)*(sp0) + (6204378674668977/100000000000000 : ℝ)*(sp1) + (6204378628900819/100000000000000 : ℝ)*(sp2) + (1417857947105839/50000000000000 : ℝ)*(sp3) + (40446777417/100000000000000 : ℝ)*(sp4) + (1928562809/12500000000000 : ℝ)*(sp7) + (56714626454283/2000000000000 : ℝ)*(f.failure) + (1240876070262069/20000000000000 : ℝ)*(f.sum) + (29256751575113/12270000000000000000000000000 : ℝ)*base66 + (645516406761838811/122700000000000000000000000000000 : ℝ)*base68 + (85543470055126721/76687500000000000000000000000000 : ℝ)*base70 + (395539355778538811/122700000000000000000000000000000 : ℝ)*base72 + (37215777198263/12270000000000000000000000000 : ℝ)*base74 + (211095276934873279/76687500000000000000000000000000 : ℝ)*base75 + (777233947346508811/122700000000000000000000000000000 : ℝ)*base78 + (305966846176391189/122700000000000000000000000000000 : ℝ)*base79 + (1789846070417/613500000000000000000000000 : ℝ)*base82 + (486689/200000000000000000000 : ℝ)*base89 + (486689/200000000000000000000 : ℝ)*base91 + (1513311/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110701917061966638294203601/25562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34183039/5000000000000 : ℝ)*(base19) + (794746367/100000000000000 : ℝ)*(base23) + (3849993/5000000000000 : ℝ)*(upper3) + (1815791/5000000000000 : ℝ)*(lower4) + (19437811/20000000000000 : ℝ)*(upper5) + (2276731409388977/50000000000000 : ℝ)*(major0) + (2276731409388977/50000000000000 : ℝ)*(major1) + (2276731409388977/50000000000000 : ℝ)*(major2) + (1464161691/10000000000000 : ℝ)*(sp1) + (8077903817/50000000000000 : ℝ)*(sp2) + (97659935182817/1562500000000 : ℝ)*(sp4) + (3125110263211299/50000000000000 : ℝ)*(sp5) + (3125109450573143/50000000000000 : ℝ)*(sp6) + (357086205187629/12500000000000 : ℝ)*(sp7) + (357086205187629/12500000000000 : ℝ)*(f.failure) + (97659935182817/1562500000000 : ℝ)*(f.sum) + (24214658185189/3067500000000000000000000000 : ℝ)*base65 + (2724506734507396399/306750000000000000000000000000000 : ℝ)*base67 + (2657457183766603601/306750000000000000000000000000000 : ℝ)*base70 + (3805947396898396399/306750000000000000000000000000000 : ℝ)*base71 + (143647944193/1533750000000000000000000000 : ℝ)*base74 + (3978387723512896399/306750000000000000000000000000000 : ℝ)*base75 + (105193188925396399/306750000000000000000000000000000 : ℝ)*base77 + (2282691229121896399/306750000000000000000000000000000 : ℝ)*base79 + (4239607717331/3067500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7291193/1250000000000000000000 : ℝ)*base90 + (7291193/1250000000000000000000 : ℝ)*base92 + (7291193/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1460_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3733/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1460_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1460_s5_0 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-48655961/250000000 : ℝ)*x 0 + (5406757901/10000000000 : ℝ)*x 1 + (5247430531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48655961/250000000 : ℝ)^1105 ≤ (5940684273613/50000000000000 : ℝ)^849 := by
    have hnat : (48655961 : ℕ)^1105*50000000000000^849 ≤ 5940684273613^849*250000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48655961 250000000 5940684273613 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406757901/10000000000 : ℝ)^1105 ≤ (11229206769087/25000000000000 : ℝ)^849 := by
    have hnat : (5406757901 : ℕ)^1105*25000000000000^849 ≤ 11229206769087^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406757901 10000000000 11229206769087 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247430531/10000000000 : ℝ)^1105 ≤ (43201804357293/100000000000000 : ℝ)^849 := by
    have hnat : (5247430531 : ℕ)^1105*100000000000000^849 ≤ 43201804357293^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247430531 10000000000 43201804357293 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48655961/250000000 : ℝ), (5406757901/10000000000 : ℝ), (5247430531/10000000000 : ℝ)] ![(5940684273613/50000000000000 : ℝ), (11229206769087/25000000000000 : ℝ), (43201804357293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48655961/250000000 : ℝ)|^1105 ≤ (5940684273613/50000000000000 : ℝ)^849
        have hw : |(-48655961/250000000 : ℝ)|=(48655961/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406757901/10000000000 : ℝ)|^1105 ≤ (11229206769087/25000000000000 : ℝ)^849
        have hw : |(5406757901/10000000000 : ℝ)|=(5406757901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247430531/10000000000 : ℝ)|^1105 ≤ (43201804357293/100000000000000 : ℝ)^849
        have hw : |(5247430531/10000000000 : ℝ)|=(5247430531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s5_1 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673345777/5000000000 : ℝ)*x 0 + (-2027336289/10000000000 : ℝ)*x 1 + (2623715247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673345777/5000000000 : ℝ)^1105 ≤ (5533556177769/12500000000000 : ℝ)^849 := by
    have hnat : (2673345777 : ℕ)^1105*12500000000000^849 ≤ 5533556177769^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673345777 5000000000 5533556177769 12500000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2027336289/10000000000 : ℝ)^1105 ≤ (12529746605511/100000000000000 : ℝ)^849 := by
    have hnat : (2027336289 : ℕ)^1105*100000000000000^849 ≤ 12529746605511^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027336289 10000000000 12529746605511 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623715247/5000000000 : ℝ)^1105 ≤ (21600901980411/50000000000000 : ℝ)^849 := by
    have hnat : (2623715247 : ℕ)^1105*50000000000000^849 ≤ 21600901980411^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623715247 5000000000 21600901980411 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673345777/5000000000 : ℝ), (-2027336289/10000000000 : ℝ), (2623715247/5000000000 : ℝ)] ![(5533556177769/12500000000000 : ℝ), (12529746605511/100000000000000 : ℝ), (21600901980411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673345777/5000000000 : ℝ)|^1105 ≤ (5533556177769/12500000000000 : ℝ)^849
        have hw : |(2673345777/5000000000 : ℝ)|=(2673345777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2027336289/10000000000 : ℝ)|^1105 ≤ (12529746605511/100000000000000 : ℝ)^849
        have hw : |(-2027336289/10000000000 : ℝ)|=(2027336289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623715247/5000000000 : ℝ)|^1105 ≤ (21600901980411/50000000000000 : ℝ)^849
        have hw : |(2623715247/5000000000 : ℝ)|=(2623715247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s5_2 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668336443/1250000000 : ℝ)*x 0 + (262371527/500000000 : ℝ)*x 1 + (-25341703/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668336443/1250000000 : ℝ)^1105 ≤ (44268449314391/100000000000000 : ℝ)^849 := by
    have hnat : (668336443 : ℕ)^1105*100000000000000^849 ≤ 44268449314391^849*1250000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668336443 1250000000 44268449314391 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262371527/500000000 : ℝ)^1105 ≤ (10800451113433/25000000000000 : ℝ)^849 := by
    have hnat : (262371527 : ℕ)^1105*25000000000000^849 ≤ 10800451113433^849*500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262371527 500000000 10800451113433 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25341703/125000000 : ℝ)^1105 ≤ (3132436552839/25000000000000 : ℝ)^849 := by
    have hnat : (25341703 : ℕ)^1105*25000000000000^849 ≤ 3132436552839^849*125000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25341703 125000000 3132436552839 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668336443/1250000000 : ℝ), (262371527/500000000 : ℝ), (-25341703/125000000 : ℝ)] ![(44268449314391/100000000000000 : ℝ), (10800451113433/25000000000000 : ℝ), (3132436552839/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668336443/1250000000 : ℝ)|^1105 ≤ (44268449314391/100000000000000 : ℝ)^849
        have hw : |(668336443/1250000000 : ℝ)|=(668336443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262371527/500000000 : ℝ)|^1105 ≤ (10800451113433/25000000000000 : ℝ)^849
        have hw : |(262371527/500000000 : ℝ)|=(262371527/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25341703/125000000 : ℝ)|^1105 ≤ (3132436552839/25000000000000 : ℝ)^849
        have hw : |(-25341703/125000000 : ℝ)|=(25341703/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s5_3 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (537084113/1250000000 : ℝ)*x 0 + (4125511999/10000000000 : ℝ)*x 1 + (139815911/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537084113/1250000000 : ℝ)^1105 ≤ (33305060609687/100000000000000 : ℝ)^849 := by
    have hnat : (537084113 : ℕ)^1105*100000000000000^849 ≤ 33305060609687^849*1250000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537084113 1250000000 33305060609687 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4125511999/10000000000 : ℝ)^1105 ≤ (31588748896799/100000000000000 : ℝ)^849 := by
    have hnat : (4125511999 : ℕ)^1105*100000000000000^849 ≤ 31588748896799^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125511999 10000000000 31588748896799 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139815911/312500000 : ℝ)^1105 ≤ (35106190481569/100000000000000 : ℝ)^849 := by
    have hnat : (139815911 : ℕ)^1105*100000000000000^849 ≤ 35106190481569^849*312500000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139815911 312500000 35106190481569 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537084113/1250000000 : ℝ), (4125511999/10000000000 : ℝ), (139815911/312500000 : ℝ)] ![(33305060609687/100000000000000 : ℝ), (31588748896799/100000000000000 : ℝ), (35106190481569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537084113/1250000000 : ℝ)|^1105 ≤ (33305060609687/100000000000000 : ℝ)^849
        have hw : |(537084113/1250000000 : ℝ)|=(537084113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4125511999/10000000000 : ℝ)|^1105 ≤ (31588748896799/100000000000000 : ℝ)^849
        have hw : |(4125511999/10000000000 : ℝ)|=(4125511999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(139815911/312500000 : ℝ)|^1105 ≤ (35106190481569/100000000000000 : ℝ)^849
        have hw : |(139815911/312500000 : ℝ)|=(139815911/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s5_4 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-243281197/1250000000 : ℝ)*x 0 + (2624003859/5000000000 : ℝ)*x 1 + (1081235539/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (243281197/1250000000 : ℝ)^1105 ≤ (11881457029159/100000000000000 : ℝ)^849 := by
    have hnat : (243281197 : ℕ)^1105*100000000000000^849 ≤ 11881457029159^849*1250000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243281197 1250000000 11881457029159 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2624003859/5000000000 : ℝ)^1105 ≤ (10801997317301/25000000000000 : ℝ)^849 := by
    have hnat : (2624003859 : ℕ)^1105*25000000000000^849 ≤ 10801997317301^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624003859 5000000000 10801997317301 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081235539/2000000000 : ℝ)^1105 ≤ (22455276845803/50000000000000 : ℝ)^849 := by
    have hnat : (1081235539 : ℕ)^1105*50000000000000^849 ≤ 22455276845803^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081235539 2000000000 22455276845803 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-243281197/1250000000 : ℝ), (2624003859/5000000000 : ℝ), (1081235539/2000000000 : ℝ)] ![(11881457029159/100000000000000 : ℝ), (10801997317301/25000000000000 : ℝ), (22455276845803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-243281197/1250000000 : ℝ)|^1105 ≤ (11881457029159/100000000000000 : ℝ)^849
        have hw : |(-243281197/1250000000 : ℝ)|=(243281197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2624003859/5000000000 : ℝ)|^1105 ≤ (10801997317301/25000000000000 : ℝ)^849
        have hw : |(2624003859/5000000000 : ℝ)|=(2624003859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081235539/2000000000 : ℝ)|^1105 ≤ (22455276845803/50000000000000 : ℝ)^849
        have hw : |(1081235539/2000000000 : ℝ)|=(1081235539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s5_5 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061029693/2000000000 : ℝ)*x 0 + (-934294541/5000000000 : ℝ)*x 1 + (1351544419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061029693/2000000000 : ℝ)^1105 ≤ (43821300090841/100000000000000 : ℝ)^849 := by
    have hnat : (1061029693 : ℕ)^1105*100000000000000^849 ≤ 43821300090841^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061029693 2000000000 43821300090841 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934294541/5000000000 : ℝ)^1105 ≤ (11268146413771/100000000000000 : ℝ)^849 := by
    have hnat : (934294541 : ℕ)^1105*100000000000000^849 ≤ 11268146413771^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934294541 5000000000 11268146413771 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351544419/2500000000 : ℝ)^1105 ≤ (1796422139447/4000000000000 : ℝ)^849 := by
    have hnat : (1351544419 : ℕ)^1105*4000000000000^849 ≤ 1796422139447^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351544419 2500000000 1796422139447 4000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061029693/2000000000 : ℝ), (-934294541/5000000000 : ℝ), (1351544419/2500000000 : ℝ)] ![(43821300090841/100000000000000 : ℝ), (11268146413771/100000000000000 : ℝ), (1796422139447/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061029693/2000000000 : ℝ)|^1105 ≤ (43821300090841/100000000000000 : ℝ)^849
        have hw : |(1061029693/2000000000 : ℝ)|=(1061029693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-934294541/5000000000 : ℝ)|^1105 ≤ (11268146413771/100000000000000 : ℝ)^849
        have hw : |(-934294541/5000000000 : ℝ)|=(934294541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351544419/2500000000 : ℝ)|^1105 ≤ (1796422139447/4000000000000 : ℝ)^849
        have hw : |(1351544419/2500000000 : ℝ)|=(1351544419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s5_6 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305148433/10000000000 : ℝ)*x 0 + (5406177691/10000000000 : ℝ)*x 1 + (-373717821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305148433/10000000000 : ℝ)^1105 ≤ (21910649873407/50000000000000 : ℝ)^849 := by
    have hnat : (5305148433 : ℕ)^1105*50000000000000^849 ≤ 21910649873407^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305148433 10000000000 21910649873407 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406177691/10000000000 : ℝ)^1105 ≤ (44910553648357/100000000000000 : ℝ)^849 := by
    have hnat : (5406177691 : ℕ)^1105*100000000000000^849 ≤ 44910553648357^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406177691 10000000000 44910553648357 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373717821/2000000000 : ℝ)^1105 ≤ (11268146594289/100000000000000 : ℝ)^849 := by
    have hnat : (373717821 : ℕ)^1105*100000000000000^849 ≤ 11268146594289^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373717821 2000000000 11268146594289 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305148433/10000000000 : ℝ), (5406177691/10000000000 : ℝ), (-373717821/2000000000 : ℝ)] ![(21910649873407/50000000000000 : ℝ), (44910553648357/100000000000000 : ℝ), (11268146594289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305148433/10000000000 : ℝ)|^1105 ≤ (21910649873407/50000000000000 : ℝ)^849
        have hw : |(5305148433/10000000000 : ℝ)|=(5305148433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406177691/10000000000 : ℝ)|^1105 ≤ (44910553648357/100000000000000 : ℝ)^849
        have hw : |(5406177691/10000000000 : ℝ)|=(5406177691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-373717821/2000000000 : ℝ)|^1105 ≤ (11268146594289/100000000000000 : ℝ)^849
        have hw : |(-373717821/2000000000 : ℝ)|=(373717821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s5_7 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2148348593/5000000000 : ℝ)*x 0 + (2236423127/5000000000 : ℝ)*x 1 + (128961921/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148348593/5000000000 : ℝ)^1105 ≤ (6661061116439/20000000000000 : ℝ)^849 := by
    have hnat : (2148348593 : ℕ)^1105*20000000000000^849 ≤ 6661061116439^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148348593 5000000000 6661061116439 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236423127/5000000000 : ℝ)^1105 ≤ (17546646847547/50000000000000 : ℝ)^849 := by
    have hnat : (2236423127 : ℕ)^1105*50000000000000^849 ≤ 17546646847547^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236423127 5000000000 17546646847547 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128961921/312500000 : ℝ)^1105 ≤ (1975087544379/6250000000000 : ℝ)^849 := by
    have hnat : (128961921 : ℕ)^1105*6250000000000^849 ≤ 1975087544379^849*312500000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128961921 312500000 1975087544379 6250000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148348593/5000000000 : ℝ), (2236423127/5000000000 : ℝ), (128961921/312500000 : ℝ)] ![(6661061116439/20000000000000 : ℝ), (17546646847547/50000000000000 : ℝ), (1975087544379/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148348593/5000000000 : ℝ)|^1105 ≤ (6661061116439/20000000000000 : ℝ)^849
        have hw : |(2148348593/5000000000 : ℝ)|=(2148348593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236423127/5000000000 : ℝ)|^1105 ≤ (17546646847547/50000000000000 : ℝ)^849
        have hw : |(2236423127/5000000000 : ℝ)|=(2236423127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128961921/312500000 : ℝ)|^1105 ≤ (1975087544379/6250000000000 : ℝ)^849
        have hw : |(128961921/312500000 : ℝ)|=(128961921/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1460_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11399/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (591/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2959/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (569/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2959/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (569/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2959/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (569/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2959/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (569/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2959/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (569/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2959/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (569/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (569/5000 : ℝ) ^ (4419/1024 : ℝ) ≤ (337993453195997/4000000000000000000 : ℝ) := by
    have hpowers : (569/5000 : ℝ)^4419 ≤ (337993453195997/4000000000000000000 : ℝ)^1024 := by
      have hnat : (569 : ℕ)^4419*4000000000000000000^1024 ≤ 337993453195997^1024*5000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        569 5000 337993453195997 4000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (569/5000 : ℝ)) (X := (337993453195997/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2959/20000 : ℝ) ^ (4419/1024 : ℝ) ≤ (13111715174336469/50000000000000000000 : ℝ) := by
    have hpowers : (2959/20000 : ℝ)^4419 ≤ (13111715174336469/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2959 : ℕ)^4419*50000000000000000000^1024 ≤ 13111715174336469^1024*20000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2959 20000 13111715174336469 50000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2959/20000 : ℝ)) (X := (13111715174336469/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000337993453195997/2000000000000000000 : ℝ) ≤ (1000039158500781/1000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (2000337993453195997/2000000000000000000 : ℝ)^1024 ≤ (1000039158500781/1000000000000000 : ℝ)^4419 := by
      have hnat : (2000337993453195997 : ℕ)^1024*1000000000000000^4419 ≤ 1000039158500781^4419*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000337993453195997 2000000000000000000 1000039158500781 1000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000039158500781/1000000000000000 : ℝ)) (X := (2000337993453195997/2000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034673266678572863/100000000000000000000 : ℝ) ≤ (10000803364946377/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (100034673266678572863/100000000000000000000 : ℝ)^1024 ≤ (10000803364946377/10000000000000000 : ℝ)^4419 := by
      have hnat : (100034673266678572863 : ℕ)^1024*10000000000000000^4419 ≤ 10000803364946377^4419*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034673266678572863 100000000000000000000 10000803364946377 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000803364946377/10000000000000000 : ℝ)) (X := (100034673266678572863/100000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013111715174336469/25000000000000000000 : ℝ) ≤ (625075946555309/625000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (25013111715174336469/25000000000000000000 : ℝ)^1024 ≤ (625075946555309/625000000000000 : ℝ)^4419 := by
      have hnat : (25013111715174336469 : ℕ)^1024*625000000000000^4419 ≤ 625075946555309^4419*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013111715174336469 25000000000000000000 625075946555309 625000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625075946555309/625000000000000 : ℝ)) (X := (25013111715174336469/25000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(337993453195997/4000000000000000000 : ℝ) ≤ ((3414196515139988623/3415000000000000000 : ℝ)+2*(411779938567/341500000000000 : ℝ)*(569/5000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (3414196515139988623/3415000000000000000 : ℝ)+2*(411779938567/341500000000000 : ℝ)*(569/5000 : ℝ)=(1000039158500781/1000000000000000 : ℝ) by norm_num, show 1+2*(337993453195997/4000000000000000000 : ℝ)=(2000337993453195997/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13111715174336469/50000000000000000000 : ℝ)+(337993453195997/4000000000000000000 : ℝ) ≤ ((3414196515139988623/3415000000000000000 : ℝ)+(411779938567/341500000000000 : ℝ)*((2959/20000 : ℝ)+(569/5000 : ℝ)))^(4419/1024 : ℝ) := by
    rw [show (3414196515139988623/3415000000000000000 : ℝ)+(411779938567/341500000000000 : ℝ)*((2959/20000 : ℝ)+(569/5000 : ℝ))=(10000803364946377/10000000000000000 : ℝ) by norm_num, show 1+(13111715174336469/50000000000000000000 : ℝ)+(337993453195997/4000000000000000000 : ℝ)=(100034673266678572863/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13111715174336469/50000000000000000000 : ℝ) ≤ ((3414196515139988623/3415000000000000000 : ℝ)+2*(411779938567/341500000000000 : ℝ)*(2959/20000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (3414196515139988623/3415000000000000000 : ℝ)+2*(411779938567/341500000000000 : ℝ)*(2959/20000 : ℝ)=(625075946555309/625000000000000 : ℝ) by norm_num, show 1+2*(13111715174336469/50000000000000000000 : ℝ)=(25013111715174336469/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3414196515139988623/3415000000000000000 : ℝ)*(X 1 0+X 2 0)+(411779938567/341500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (569/5000 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (3414196515139988623/3415000000000000000 : ℝ)) (alpha := (411779938567/341500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3414196515139988623/3415000000000000000 : ℝ)*(X 0 1+X 2 1)+(411779938567/341500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (569/5000 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (3414196515139988623/3415000000000000000 : ℝ)) (alpha := (411779938567/341500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3414196515139988623/3415000000000000000 : ℝ)*(X 0 2+X 1 2)+(411779938567/341500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (569/5000 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (3414196515139988623/3415000000000000000 : ℝ)) (alpha := (411779938567/341500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-48655961/250000000 : ℝ)*X 0 0+(5406757901/10000000000 : ℝ)*X 0 1+(5247430531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673345777/5000000000 : ℝ)*X 1 0+(-2027336289/10000000000 : ℝ)*X 1 1+(2623715247/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668336443/1250000000 : ℝ)*X 2 0+(262371527/500000000 : ℝ)*X 2 1+(-25341703/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((537084113/1250000000 : ℝ)*X 0 0+(4125511999/10000000000 : ℝ)*X 0 1+(139815911/312500000 : ℝ)*X 0 2+(537084113/1250000000 : ℝ)*X 1 0+(4125511999/10000000000 : ℝ)*X 1 1+(139815911/312500000 : ℝ)*X 1 2+(537084113/1250000000 : ℝ)*X 2 0+(4125511999/10000000000 : ℝ)*X 2 1+(139815911/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-243281197/1250000000 : ℝ)*X 0 0+(2624003859/5000000000 : ℝ)*X 0 1+(1081235539/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061029693/2000000000 : ℝ)*X 1 0+(-934294541/5000000000 : ℝ)*X 1 1+(1351544419/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305148433/10000000000 : ℝ)*X 2 0+(5406177691/10000000000 : ℝ)*X 2 1+(-373717821/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148348593/5000000000 : ℝ)*X 0 0+(2236423127/5000000000 : ℝ)*X 0 1+(128961921/312500000 : ℝ)*X 0 2+(2148348593/5000000000 : ℝ)*X 1 0+(2236423127/5000000000 : ℝ)*X 1 1+(128961921/312500000 : ℝ)*X 1 2+(2148348593/5000000000 : ℝ)*X 2 0+(2236423127/5000000000 : ℝ)*X 2 1+(128961921/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (329918482597002847959762099/34150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108131349/6250000000000 : ℝ)*(base19) + (12332937/800000000000 : ℝ)*(base23) + (94500371/100000000000000 : ℝ)*(lower2) + (13927277/6250000000000 : ℝ)*(upper3) + (155457511/100000000000000 : ℝ)*(upper5) + (1143141670618339/25000000000000 : ℝ)*(major0) + (1143141670618339/25000000000000 : ℝ)*(major1) + (4572566682473357/100000000000000 : ℝ)*(major2) + (31382109916397/500000000000 : ℝ)*(sp0) + (784557068606057/12500000000000 : ℝ)*(sp1) + (1569114184333229/25000000000000 : ℝ)*(sp2) + (1434328417323771/50000000000000 : ℝ)*(sp3) + (36295670641/100000000000000 : ℝ)*(sp4) + (17929320341/100000000000000 : ℝ)*(sp7) + (2868674763967883/100000000000000 : ℝ)*(f.failure) + (6276458278950041/100000000000000 : ℝ)*(f.sum) + (23763813698429/34150000000000000000000000000 : ℝ)*base66 + (1090139154757545303/85375000000000000000000000000000 : ℝ)*base68 + (2186478082802637411/341500000000000000000000000000000 : ℝ)*base69 + (917403956178045303/85375000000000000000000000000000 : ℝ)*base72 + (177693610604929/34150000000000000000000000000 : ℝ)*base74 + (12740431982289137411/341500000000000000000000000000000 : ℝ)*base75 + (318155094454462803/85375000000000000000000000000000 : ℝ)*base78 + (1242376950274712803/85375000000000000000000000000000 : ℝ)*base80 + (2742902400413/4268750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (75155489/10000000000000000000000 : ℝ)*base89 + (75155489/10000000000000000000000 : ℝ)*base91 + (24844511/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59532019715723641926851823/10671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (472756339/50000000000000 : ℝ)*(base19) + (995988339/100000000000000 : ℝ)*(base23) + (27839009/25000000000000 : ℝ)*(upper3) + (2770213/6250000000000 : ℝ)*(lower4) + (113691293/100000000000000 : ℝ)*(upper5) + (287873223208171/6250000000000 : ℝ)*(major0) + (287873223208171/6250000000000 : ℝ)*(major1) + (287873223208171/6250000000000 : ℝ)*(major2) + (1958984683/10000000000000 : ℝ)*(sp1) + (5059102761/25000000000000 : ℝ)*(sp2) + (3161155543701271/50000000000000 : ℝ)*(sp4) + (3161145276021517/50000000000000 : ℝ)*(sp5) + (6322289855003159/100000000000000 : ℝ)*(sp6) + (1444815934656079/50000000000000 : ℝ)*(sp7) + (1444815934656079/50000000000000 : ℝ)*(f.failure) + (3161155543701271/50000000000000 : ℝ)*(f.sum) + (3589272956597/4268750000000000000000000000 : ℝ)*base66 + (254497268493041467/21343750000000000000000000000000 : ℝ)*base68 + (173010288210978967/21343750000000000000000000000000 : ℝ)*base70 + (92159453573978967/21343750000000000000000000000000 : ℝ)*base72 + (8923801111619/8537500000000000000000000000 : ℝ)*base74 + (110828310100416467/21343750000000000000000000000000 : ℝ)*base76 + (123923118870822717/21343750000000000000000000000000 : ℝ)*base78 + (125199709848864783/21343750000000000000000000000000 : ℝ)*base79 + (43562091489237/17075000000000000000000000000 : ℝ)*base81 + (7170157/5000000000000000000000 : ℝ)*base89 + (7170157/5000000000000000000000 : ℝ)*base91 + (7170157/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1460_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (591/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1460_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1460_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (591/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1460_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1460_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1460_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (591/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1460_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
