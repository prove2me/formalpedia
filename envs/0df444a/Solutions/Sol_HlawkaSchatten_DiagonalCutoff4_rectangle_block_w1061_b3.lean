-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1061_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:03:27.626129+00:00
-- url     : https://prove2.me/submissions/e7c9d8e0-3cf8-448f-b532-9049d7e8b37f

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
theorem support_rectangle_w1061_s9_0 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-137889531/625000000 : ℝ)*x 0 + (5394416727/10000000000 : ℝ)*x 1 + (1316097101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137889531/625000000 : ℝ)^4127 ≤ (334960882437/2500000000000 : ℝ)^3103 := by
    have hnat : (137889531 : ℕ)^4127*2500000000000^3103 ≤ 334960882437^3103*625000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137889531 625000000 334960882437 2500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394416727/10000000000 : ℝ)^4127 ≤ (44003306577713/100000000000000 : ℝ)^3103 := by
    have hnat : (5394416727 : ℕ)^4127*100000000000000^3103 ≤ 44003306577713^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394416727 10000000000 44003306577713 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316097101/2500000000 : ℝ)^4127 ≤ (5324782263653/12500000000000 : ℝ)^3103 := by
    have hnat : (1316097101 : ℕ)^4127*12500000000000^3103 ≤ 5324782263653^3103*2500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316097101 2500000000 5324782263653 12500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137889531/625000000 : ℝ), (5394416727/10000000000 : ℝ), (1316097101/2500000000 : ℝ)] ![(334960882437/2500000000000 : ℝ), (44003306577713/100000000000000 : ℝ), (5324782263653/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137889531/625000000 : ℝ)|^4127 ≤ (334960882437/2500000000000 : ℝ)^3103
        have hw : |(-137889531/625000000 : ℝ)|=(137889531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394416727/10000000000 : ℝ)|^4127 ≤ (44003306577713/100000000000000 : ℝ)^3103
        have hw : |(5394416727/10000000000 : ℝ)|=(5394416727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316097101/2500000000 : ℝ)|^4127 ≤ (5324782263653/12500000000000 : ℝ)^3103
        have hw : |(1316097101/2500000000 : ℝ)|=(1316097101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s9_1 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068996861/2000000000 : ℝ)*x 0 + (-2272205773/10000000000 : ℝ)*x 1 + (1052877677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068996861/2000000000 : ℝ)^4127 ≤ (434678220893/1000000000000 : ℝ)^3103 := by
    have hnat : (1068996861 : ℕ)^4127*1000000000000^3103 ≤ 434678220893^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068996861 2000000000 434678220893 1000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2272205773/10000000000 : ℝ)^4127 ≤ (13933919988463/100000000000000 : ℝ)^3103 := by
    have hnat : (2272205773 : ℕ)^4127*100000000000000^3103 ≤ 13933919988463^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272205773 10000000000 13933919988463 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052877677/2000000000 : ℝ)^4127 ≤ (5324782238093/12500000000000 : ℝ)^3103 := by
    have hnat : (1052877677 : ℕ)^4127*12500000000000^3103 ≤ 5324782238093^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052877677 2000000000 5324782238093 12500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068996861/2000000000 : ℝ), (-2272205773/10000000000 : ℝ), (1052877677/2000000000 : ℝ)] ![(434678220893/1000000000000 : ℝ), (13933919988463/100000000000000 : ℝ), (5324782238093/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068996861/2000000000 : ℝ)|^4127 ≤ (434678220893/1000000000000 : ℝ)^3103
        have hw : |(1068996861/2000000000 : ℝ)|=(1068996861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2272205773/10000000000 : ℝ)|^4127 ≤ (13933919988463/100000000000000 : ℝ)^3103
        have hw : |(-2272205773/10000000000 : ℝ)|=(2272205773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052877677/2000000000 : ℝ)|^4127 ≤ (5324782238093/12500000000000 : ℝ)^3103
        have hw : |(1052877677/2000000000 : ℝ)|=(1052877677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s9_2 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-275779697/1250000000 : ℝ)*x 0 + (1316178381/2500000000 : ℝ)*x 1 + (2697045213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275779697/1250000000 : ℝ)^4127 ≤ (13398476329167/100000000000000 : ℝ)^3103 := by
    have hnat : (275779697 : ℕ)^4127*100000000000000^3103 ≤ 13398476329167^3103*1250000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275779697 1250000000 13398476329167 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316178381/2500000000 : ℝ)^4127 ≤ (2662609819719/6250000000000 : ℝ)^3103 := by
    have hnat : (1316178381 : ℕ)^4127*6250000000000^3103 ≤ 2662609819719^3103*2500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316178381 2500000000 2662609819719 6250000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697045213/5000000000 : ℝ)^4127 ≤ (43999766542497/100000000000000 : ℝ)^3103 := by
    have hnat : (2697045213 : ℕ)^4127*100000000000000^3103 ≤ 43999766542497^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697045213 5000000000 43999766542497 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275779697/1250000000 : ℝ), (1316178381/2500000000 : ℝ), (2697045213/5000000000 : ℝ)] ![(13398476329167/100000000000000 : ℝ), (2662609819719/6250000000000 : ℝ), (43999766542497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275779697/1250000000 : ℝ)|^4127 ≤ (13398476329167/100000000000000 : ℝ)^3103
        have hw : |(-275779697/1250000000 : ℝ)|=(275779697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316178381/2500000000 : ℝ)|^4127 ≤ (2662609819719/6250000000000 : ℝ)^3103
        have hw : |(1316178381/2500000000 : ℝ)|=(1316178381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697045213/5000000000 : ℝ)|^4127 ≤ (43999766542497/100000000000000 : ℝ)^3103
        have hw : |(2697045213/5000000000 : ℝ)|=(2697045213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s9_3 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656122997/5000000000 : ℝ)*x 0 + (-2142504029/10000000000 : ℝ)*x 1 + (2697044901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656122997/5000000000 : ℝ)^4127 ≤ (10778519199347/25000000000000 : ℝ)^3103 := by
    have hnat : (2656122997 : ℕ)^4127*25000000000000^3103 ≤ 10778519199347^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656122997 5000000000 10778519199347 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142504029/10000000000 : ℝ)^4127 ≤ (6443081709659/50000000000000 : ℝ)^3103 := by
    have hnat : (2142504029 : ℕ)^4127*50000000000000^3103 ≤ 6443081709659^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142504029 10000000000 6443081709659 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697044901/5000000000 : ℝ)^4127 ≤ (43999759772797/100000000000000 : ℝ)^3103 := by
    have hnat : (2697044901 : ℕ)^4127*100000000000000^3103 ≤ 43999759772797^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697044901 5000000000 43999759772797 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656122997/5000000000 : ℝ), (-2142504029/10000000000 : ℝ), (2697044901/5000000000 : ℝ)] ![(10778519199347/25000000000000 : ℝ), (6443081709659/50000000000000 : ℝ), (43999759772797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656122997/5000000000 : ℝ)|^4127 ≤ (10778519199347/25000000000000 : ℝ)^3103
        have hw : |(2656122997/5000000000 : ℝ)|=(2656122997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142504029/10000000000 : ℝ)|^4127 ≤ (6443081709659/50000000000000 : ℝ)^3103
        have hw : |(-2142504029/10000000000 : ℝ)|=(2142504029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697044901/5000000000 : ℝ)|^4127 ≤ (43999759772797/100000000000000 : ℝ)^3103
        have hw : |(2697044901/5000000000 : ℝ)|=(2697044901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s9_4 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062449109/2000000000 : ℝ)*x 0 + (1078818027/2000000000 : ℝ)*x 1 + (-2142504183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062449109/2000000000 : ℝ)^4127 ≤ (43114071950757/100000000000000 : ℝ)^3103 := by
    have hnat : (1062449109 : ℕ)^4127*100000000000000^3103 ≤ 43114071950757^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062449109 2000000000 43114071950757 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078818027/2000000000 : ℝ)^4127 ≤ (21999881692737/50000000000000 : ℝ)^3103 := by
    have hnat : (1078818027 : ℕ)^4127*50000000000000^3103 ≤ 21999881692737^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078818027 2000000000 21999881692737 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2142504183/10000000000 : ℝ)^4127 ≤ (6443082325609/50000000000000 : ℝ)^3103 := by
    have hnat : (2142504183 : ℕ)^4127*50000000000000^3103 ≤ 6443082325609^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142504183 10000000000 6443082325609 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062449109/2000000000 : ℝ), (1078818027/2000000000 : ℝ), (-2142504183/10000000000 : ℝ)] ![(43114071950757/100000000000000 : ℝ), (21999881692737/50000000000000 : ℝ), (6443082325609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062449109/2000000000 : ℝ)|^4127 ≤ (43114071950757/100000000000000 : ℝ)^3103
        have hw : |(1062449109/2000000000 : ℝ)|=(1062449109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078818027/2000000000 : ℝ)|^4127 ≤ (21999881692737/50000000000000 : ℝ)^3103
        have hw : |(1078818027/2000000000 : ℝ)|=(1078818027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2142504183/10000000000 : ℝ)|^4127 ≤ (6443082325609/50000000000000 : ℝ)^3103
        have hw : |(-2142504183/10000000000 : ℝ)|=(2142504183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s9_5 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4376223609/10000000000 : ℝ)*x 0 + (4504745459/10000000000 : ℝ)*x 1 + (2125719163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376223609/10000000000 : ℝ)^4127 ≤ (33316639123017/100000000000000 : ℝ)^3103 := by
    have hnat : (4376223609 : ℕ)^4127*100000000000000^3103 ≤ 33316639123017^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376223609 10000000000 33316639123017 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504745459/10000000000 : ℝ)^4127 ≤ (34624245991079/100000000000000 : ℝ)^3103 := by
    have hnat : (4504745459 : ℕ)^4127*100000000000000^3103 ≤ 34624245991079^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504745459 10000000000 34624245991079 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125719163/5000000000 : ℝ)^4127 ≤ (32059114875949/100000000000000 : ℝ)^3103 := by
    have hnat : (2125719163 : ℕ)^4127*100000000000000^3103 ≤ 32059114875949^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125719163 5000000000 32059114875949 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376223609/10000000000 : ℝ), (4504745459/10000000000 : ℝ), (2125719163/5000000000 : ℝ)] ![(33316639123017/100000000000000 : ℝ), (34624245991079/100000000000000 : ℝ), (32059114875949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376223609/10000000000 : ℝ)|^4127 ≤ (33316639123017/100000000000000 : ℝ)^3103
        have hw : |(4376223609/10000000000 : ℝ)|=(4376223609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504745459/10000000000 : ℝ)|^4127 ≤ (34624245991079/100000000000000 : ℝ)^3103
        have hw : |(4504745459/10000000000 : ℝ)|=(4504745459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125719163/5000000000 : ℝ)|^4127 ≤ (32059114875949/100000000000000 : ℝ)^3103
        have hw : |(2125719163/5000000000 : ℝ)|=(2125719163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1061_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2249/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13999/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7/50 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2249/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7/50 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2249/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7/50 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2249/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7/50 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2249/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7/50 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2249/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7/50 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2249/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2249/20000 : ℝ) ^ (8253/2048 : ℝ) ≤ (14982025030363303/100000000000000000000 : ℝ) := by
    have hpowers : (2249/20000 : ℝ)^8253 ≤ (14982025030363303/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2249 : ℕ)^8253*100000000000000000000^2048 ≤ 14982025030363303^2048*20000^8253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2249 20000 14982025030363303 100000000000000000000 8253 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2249/20000 : ℝ)) (X := (14982025030363303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7/50 : ℝ) ^ (8253/2048 : ℝ) ≤ (9057731475881729/25000000000000000000 : ℝ) := by
    have hpowers : (7/50 : ℝ)^8253 ≤ (9057731475881729/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7 : ℕ)^8253*25000000000000000000^2048 ≤ 9057731475881729^2048*50^8253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7 50 9057731475881729 25000000000000000000 8253 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7/50 : ℝ)) (X := (9057731475881729/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014982025030363303/50000000000000000000 : ℝ) ≤ (1000074348071369/1000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (50014982025030363303/50000000000000000000 : ℝ)^2048 ≤ (1000074348071369/1000000000000000 : ℝ)^8253 := by
      have hnat : (50014982025030363303 : ℕ)^2048*1000000000000000^8253 ≤ 1000074348071369^8253*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014982025030363303 50000000000000000000 1000074348071369 1000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000074348071369/1000000000000000 : ℝ)) (X := (50014982025030363303/50000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051212950933890219/100000000000000000000 : ℝ) ≤ (10001270615982997/10000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (100051212950933890219/100000000000000000000 : ℝ)^2048 ≤ (10001270615982997/10000000000000000 : ℝ)^8253 := by
      have hnat : (100051212950933890219 : ℕ)^2048*10000000000000000^8253 ≤ 10001270615982997^8253*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051212950933890219 100000000000000000000 10001270615982997 10000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001270615982997/10000000000000000 : ℝ)) (X := (100051212950933890219/100000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509057731475881729/12500000000000000000 : ℝ) ≤ (625112359453269/625000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (12509057731475881729/12500000000000000000 : ℝ)^2048 ≤ (625112359453269/625000000000000 : ℝ)^8253 := by
      have hnat : (12509057731475881729 : ℕ)^2048*625000000000000^8253 ≤ 625112359453269^8253*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509057731475881729 12500000000000000000 625112359453269 625000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625112359453269/625000000000000 : ℝ)) (X := (12509057731475881729/12500000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14982025030363303/100000000000000000000 : ℝ) ≤ ((344252412714493769/344375000000000000 : ℝ)+2*(527135269307/275500000000000 : ℝ)*(2249/20000 : ℝ))^(8253/2048 : ℝ) := by
    rw [show (344252412714493769/344375000000000000 : ℝ)+2*(527135269307/275500000000000 : ℝ)*(2249/20000 : ℝ)=(1000074348071369/1000000000000000 : ℝ) by norm_num, show 1+2*(14982025030363303/100000000000000000000 : ℝ)=(50014982025030363303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9057731475881729/25000000000000000000 : ℝ)+(14982025030363303/100000000000000000000 : ℝ) ≤ ((344252412714493769/344375000000000000 : ℝ)+(527135269307/275500000000000 : ℝ)*((7/50 : ℝ)+(2249/20000 : ℝ)))^(8253/2048 : ℝ) := by
    rw [show (344252412714493769/344375000000000000 : ℝ)+(527135269307/275500000000000 : ℝ)*((7/50 : ℝ)+(2249/20000 : ℝ))=(10001270615982997/10000000000000000 : ℝ) by norm_num, show 1+(9057731475881729/25000000000000000000 : ℝ)+(14982025030363303/100000000000000000000 : ℝ)=(100051212950933890219/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9057731475881729/25000000000000000000 : ℝ) ≤ ((344252412714493769/344375000000000000 : ℝ)+2*(527135269307/275500000000000 : ℝ)*(7/50 : ℝ))^(8253/2048 : ℝ) := by
    rw [show (344252412714493769/344375000000000000 : ℝ)+2*(527135269307/275500000000000 : ℝ)*(7/50 : ℝ)=(625112359453269/625000000000000 : ℝ) by norm_num, show 1+2*(9057731475881729/25000000000000000000 : ℝ)=(12509057731475881729/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (344252412714493769/344375000000000000 : ℝ)*(X 1 0+X 2 0)+(527135269307/275500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (7/50 : ℝ)) (c := (344252412714493769/344375000000000000 : ℝ)) (alpha := (527135269307/275500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (344252412714493769/344375000000000000 : ℝ)*(X 0 1+X 2 1)+(527135269307/275500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (7/50 : ℝ)) (c := (344252412714493769/344375000000000000 : ℝ)) (alpha := (527135269307/275500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (344252412714493769/344375000000000000 : ℝ)*(X 0 2+X 1 2)+(527135269307/275500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (7/50 : ℝ)) (c := (344252412714493769/344375000000000000 : ℝ)) (alpha := (527135269307/275500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-137889531/625000000 : ℝ)*X 0 0+(5394416727/10000000000 : ℝ)*X 0 1+(1316097101/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068996861/2000000000 : ℝ)*X 1 0+(-2272205773/10000000000 : ℝ)*X 1 1+(1052877677/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-275779697/1250000000 : ℝ)*X 0 0+(1316178381/2500000000 : ℝ)*X 0 1+(2697045213/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656122997/5000000000 : ℝ)*X 1 0+(-2142504029/10000000000 : ℝ)*X 1 1+(2697044901/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1062449109/2000000000 : ℝ)*X 2 0+(1078818027/2000000000 : ℝ)*X 2 1+(-2142504183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4376223609/10000000000 : ℝ)*X 0 0+(4504745459/10000000000 : ℝ)*X 0 1+(2125719163/5000000000 : ℝ)*X 0 2+(4376223609/10000000000 : ℝ)*X 1 0+(4504745459/10000000000 : ℝ)*X 1 1+(2125719163/5000000000 : ℝ)*X 1 2+(4376223609/10000000000 : ℝ)*X 2 0+(4504745459/10000000000 : ℝ)*X 2 1+(2125719163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4050784723269263271695001/1721875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1207381139/100000000000000 : ℝ)*(base19) + (226122413/25000000000000 : ℝ)*(base23) + (38153843/25000000000000 : ℝ)*(lower1) + (28341339/12500000000000 : ℝ)*(lower4) + (133740227/50000000000000 : ℝ)*(upper5) + (1167713863590943/20000000000000 : ℝ)*(major0) + (1167713863590943/20000000000000 : ℝ)*(major1) + (1167713863590943/20000000000000 : ℝ)*(major2) + (9236863797/50000000000000 : ℝ)*(sp0) + (6198399927/50000000000000 : ℝ)*(sp1) + (154587217443823/2000000000000 : ℝ)*(sp2) + (966170717717219/12500000000000 : ℝ)*(sp3) + (7729378441429093/100000000000000 : ℝ)*(sp4) + (493469901446573/12500000000000 : ℝ)*(sp5) + (493469901446573/12500000000000 : ℝ)*(f.failure) + (966172418239843/12500000000000 : ℝ)*(f.sum) + (2442720594659/2755000000000000000000000000 : ℝ)*base66 + (1320556593464583/6887500000000000000000000000000 : ℝ)*base68 + (61253727244289583/6887500000000000000000000000000 : ℝ)*base70 + (93562909532464583/6887500000000000000000000000000 : ℝ)*base72 + (7148681114471/2755000000000000000000000000 : ℝ)*base73 + (7459065119235417/6887500000000000000000000000000 : ℝ)*base75 + (88092744952177083/6887500000000000000000000000000 : ℝ)*base78 + (81633899302083/6887500000000000000000000000000 : ℝ)*base80 + (6080120145463/1377500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6108513/1250000000000000000000 : ℝ)*base89 + (6108513/1250000000000000000000 : ℝ)*base91 + (6108513/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1061_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1061_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1061_box_0 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-415321113/2000000000 : ℝ)*x 0 + (5377432709/10000000000 : ℝ)*x 1 + (5377433191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415321113/2000000000 : ℝ)^4127 ≤ (3090428119133/25000000000000 : ℝ)^3103 := by
    have hnat : (415321113 : ℕ)^4127*25000000000000^3103 ≤ 3090428119133^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415321113 2000000000 3090428119133 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377432709/10000000000 : ℝ)^4127 ≤ (43819141143687/100000000000000 : ℝ)^3103 := by
    have hnat : (5377432709 : ℕ)^4127*100000000000000^3103 ≤ 43819141143687^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377432709 10000000000 43819141143687 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377433191/10000000000 : ℝ)^4127 ≤ (5477393295939/12500000000000 : ℝ)^3103 := by
    have hnat : (5377433191 : ℕ)^4127*12500000000000^3103 ≤ 5477393295939^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377433191 10000000000 5477393295939 12500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415321113/2000000000 : ℝ), (5377432709/10000000000 : ℝ), (5377433191/10000000000 : ℝ)] ![(3090428119133/25000000000000 : ℝ), (43819141143687/100000000000000 : ℝ), (5477393295939/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415321113/2000000000 : ℝ)|^4127 ≤ (3090428119133/25000000000000 : ℝ)^3103
        have hw : |(-415321113/2000000000 : ℝ)|=(415321113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377432709/10000000000 : ℝ)|^4127 ≤ (43819141143687/100000000000000 : ℝ)^3103
        have hw : |(5377432709/10000000000 : ℝ)|=(5377432709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377433191/10000000000 : ℝ)|^4127 ≤ (5477393295939/12500000000000 : ℝ)^3103
        have hw : |(5377433191/10000000000 : ℝ)|=(5377433191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_1 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295147157/10000000000 : ℝ)*x 0 + (-136749071/625000000 : ℝ)*x 1 + (268871647/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295147157/10000000000 : ℝ)^4127 ≤ (42929605289589/100000000000000 : ℝ)^3103 := by
    have hnat : (5295147157 : ℕ)^4127*100000000000000^3103 ≤ 42929605289589^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295147157 10000000000 42929605289589 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136749071/625000000 : ℝ)^4127 ≤ (13251251042591/100000000000000 : ℝ)^3103 := by
    have hnat : (136749071 : ℕ)^4127*100000000000000^3103 ≤ 13251251042591^3103*625000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136749071 625000000 13251251042591 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268871647/500000000 : ℝ)^4127 ≤ (21909571823611/50000000000000 : ℝ)^3103 := by
    have hnat : (268871647 : ℕ)^4127*50000000000000^3103 ≤ 21909571823611^3103*500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268871647 500000000 21909571823611 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295147157/10000000000 : ℝ), (-136749071/625000000 : ℝ), (268871647/500000000 : ℝ)] ![(42929605289589/100000000000000 : ℝ), (13251251042591/100000000000000 : ℝ), (21909571823611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295147157/10000000000 : ℝ)|^4127 ≤ (42929605289589/100000000000000 : ℝ)^3103
        have hw : |(5295147157/10000000000 : ℝ)|=(5295147157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136749071/625000000 : ℝ)|^4127 ≤ (13251251042591/100000000000000 : ℝ)^3103
        have hw : |(-136749071/625000000 : ℝ)|=(136749071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(268871647/500000000 : ℝ)|^4127 ≤ (21909571823611/50000000000000 : ℝ)^3103
        have hw : |(268871647/500000000 : ℝ)|=(268871647/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_2 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295147247/10000000000 : ℝ)*x 0 + (336089567/625000000 : ℝ)*x 1 + (-2187984839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295147247/10000000000 : ℝ)^4127 ≤ (42929606260041/100000000000000 : ℝ)^3103 := by
    have hnat : (5295147247 : ℕ)^4127*100000000000000^3103 ≤ 42929606260041^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295147247 10000000000 42929606260041 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336089567/625000000 : ℝ)^4127 ≤ (43819145077813/100000000000000 : ℝ)^3103 := by
    have hnat : (336089567 : ℕ)^4127*100000000000000^3103 ≤ 43819145077813^3103*625000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336089567 625000000 43819145077813 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187984839/10000000000 : ℝ)^4127 ≤ (6625624325129/50000000000000 : ℝ)^3103 := by
    have hnat : (2187984839 : ℕ)^4127*50000000000000^3103 ≤ 6625624325129^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187984839 10000000000 6625624325129 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295147247/10000000000 : ℝ), (336089567/625000000 : ℝ), (-2187984839/10000000000 : ℝ)] ![(42929606260041/100000000000000 : ℝ), (43819145077813/100000000000000 : ℝ), (6625624325129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295147247/10000000000 : ℝ)|^4127 ≤ (42929606260041/100000000000000 : ℝ)^3103
        have hw : |(5295147247/10000000000 : ℝ)|=(5295147247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336089567/625000000 : ℝ)|^4127 ≤ (43819145077813/100000000000000 : ℝ)^3103
        have hw : |(336089567/625000000 : ℝ)|=(336089567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187984839/10000000000 : ℝ)|^4127 ≤ (6625624325129/50000000000000 : ℝ)^3103
        have hw : |(-2187984839/10000000000 : ℝ)|=(2187984839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_3 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (560581687/1250000000 : ℝ)*x 0 + (1081039713/2500000000 : ℝ)*x 1 + (4324158871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560581687/1250000000 : ℝ)^4127 ≤ (537796945901/1562500000000 : ℝ)^3103 := by
    have hnat : (560581687 : ℕ)^4127*1562500000000^3103 ≤ 537796945901^3103*1250000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560581687 1250000000 537796945901 1562500000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081039713/2500000000 : ℝ)^4127 ≤ (32790497626181/100000000000000 : ℝ)^3103 := by
    have hnat : (1081039713 : ℕ)^4127*100000000000000^3103 ≤ 32790497626181^3103*2500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081039713 2500000000 32790497626181 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4324158871/10000000000 : ℝ)^4127 ≤ (16395248908903/50000000000000 : ℝ)^3103 := by
    have hnat : (4324158871 : ℕ)^4127*50000000000000^3103 ≤ 16395248908903^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324158871 10000000000 16395248908903 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(560581687/1250000000 : ℝ), (1081039713/2500000000 : ℝ), (4324158871/10000000000 : ℝ)] ![(537796945901/1562500000000 : ℝ), (32790497626181/100000000000000 : ℝ), (16395248908903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(560581687/1250000000 : ℝ)|^4127 ≤ (537796945901/1562500000000 : ℝ)^3103
        have hw : |(560581687/1250000000 : ℝ)|=(560581687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081039713/2500000000 : ℝ)|^4127 ≤ (32790497626181/100000000000000 : ℝ)^3103
        have hw : |(1081039713/2500000000 : ℝ)|=(1081039713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4324158871/10000000000 : ℝ)|^4127 ≤ (16395248908903/50000000000000 : ℝ)^3103
        have hw : |(4324158871/10000000000 : ℝ)|=(4324158871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_4 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2337252643/10000000000 : ℝ)*x 0 + (2640008331/5000000000 : ℝ)*x 1 + (2640008327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2337252643/10000000000 : ℝ)^4127 ≤ (1808366719143/12500000000000 : ℝ)^3103 := by
    have hnat : (2337252643 : ℕ)^4127*12500000000000^3103 ≤ 1808366719143^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337252643 10000000000 1808366719143 12500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640008331/5000000000 : ℝ)^4127 ≤ (42766533157021/100000000000000 : ℝ)^3103 := by
    have hnat : (2640008331 : ℕ)^4127*100000000000000^3103 ≤ 42766533157021^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640008331 5000000000 42766533157021 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640008327/5000000000 : ℝ)^4127 ≤ (1069163326771/2500000000000 : ℝ)^3103 := by
    have hnat : (2640008327 : ℕ)^4127*2500000000000^3103 ≤ 1069163326771^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640008327 5000000000 1069163326771 2500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2337252643/10000000000 : ℝ), (2640008331/5000000000 : ℝ), (2640008327/5000000000 : ℝ)] ![(1808366719143/12500000000000 : ℝ), (42766533157021/100000000000000 : ℝ), (1069163326771/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2337252643/10000000000 : ℝ)|^4127 ≤ (1808366719143/12500000000000 : ℝ)^3103
        have hw : |(-2337252643/10000000000 : ℝ)|=(2337252643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640008331/5000000000 : ℝ)|^4127 ≤ (42766533157021/100000000000000 : ℝ)^3103
        have hw : |(2640008331/5000000000 : ℝ)|=(2640008331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640008327/5000000000 : ℝ)|^4127 ≤ (1069163326771/2500000000000 : ℝ)^3103
        have hw : |(2640008327/5000000000 : ℝ)|=(2640008327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_5 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364098287/10000000000 : ℝ)*x 0 + (-2226055217/10000000000 : ℝ)*x 1 + (5280016677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364098287/10000000000 : ℝ)^4127 ≤ (21837342180729/50000000000000 : ℝ)^3103 := by
    have hnat : (5364098287 : ℕ)^4127*50000000000000^3103 ≤ 21837342180729^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364098287 10000000000 21837342180729 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2226055217/10000000000 : ℝ)^4127 ≤ (6779391151819/50000000000000 : ℝ)^3103 := by
    have hnat : (2226055217 : ℕ)^4127*50000000000000^3103 ≤ 6779391151819^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226055217 10000000000 6779391151819 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280016677/10000000000 : ℝ)^4127 ≤ (42766533318611/100000000000000 : ℝ)^3103 := by
    have hnat : (5280016677 : ℕ)^4127*100000000000000^3103 ≤ 42766533318611^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280016677 10000000000 42766533318611 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364098287/10000000000 : ℝ), (-2226055217/10000000000 : ℝ), (5280016677/10000000000 : ℝ)] ![(21837342180729/50000000000000 : ℝ), (6779391151819/50000000000000 : ℝ), (42766533318611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364098287/10000000000 : ℝ)|^4127 ≤ (21837342180729/50000000000000 : ℝ)^3103
        have hw : |(5364098287/10000000000 : ℝ)|=(5364098287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2226055217/10000000000 : ℝ)|^4127 ≤ (6779391151819/50000000000000 : ℝ)^3103
        have hw : |(-2226055217/10000000000 : ℝ)|=(2226055217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280016677/10000000000 : ℝ)|^4127 ≤ (42766533318611/100000000000000 : ℝ)^3103
        have hw : |(5280016677/10000000000 : ℝ)|=(5280016677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_6 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364098317/10000000000 : ℝ)*x 0 + (5280016647/10000000000 : ℝ)*x 1 + (-2226055217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364098317/10000000000 : ℝ)^4127 ≤ (21837342343163/50000000000000 : ℝ)^3103 := by
    have hnat : (5364098317 : ℕ)^4127*50000000000000^3103 ≤ 21837342343163^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364098317 10000000000 21837342343163 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280016647/10000000000 : ℝ)^4127 ≤ (5345816624429/12500000000000 : ℝ)^3103 := by
    have hnat : (5280016647 : ℕ)^4127*12500000000000^3103 ≤ 5345816624429^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280016647 10000000000 5345816624429 12500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2226055217/10000000000 : ℝ)^4127 ≤ (6779391151819/50000000000000 : ℝ)^3103 := by
    have hnat : (2226055217 : ℕ)^4127*50000000000000^3103 ≤ 6779391151819^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226055217 10000000000 6779391151819 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364098317/10000000000 : ℝ), (5280016647/10000000000 : ℝ), (-2226055217/10000000000 : ℝ)] ![(21837342343163/50000000000000 : ℝ), (5345816624429/12500000000000 : ℝ), (6779391151819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364098317/10000000000 : ℝ)|^4127 ≤ (21837342343163/50000000000000 : ℝ)^3103
        have hw : |(5364098317/10000000000 : ℝ)|=(5364098317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280016647/10000000000 : ℝ)|^4127 ≤ (5345816624429/12500000000000 : ℝ)^3103
        have hw : |(5280016647/10000000000 : ℝ)|=(5280016647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2226055217/10000000000 : ℝ)|^4127 ≤ (6779391151819/50000000000000 : ℝ)^3103
        have hw : |(-2226055217/10000000000 : ℝ)|=(2226055217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_7 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34139567/80000000 : ℝ)*x 0 + (2216370611/5000000000 : ℝ)*x 1 + (4432741121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34139567/80000000 : ℝ)^4127 ≤ (16109879099537/50000000000000 : ℝ)^3103 := by
    have hnat : (34139567 : ℕ)^4127*50000000000000^3103 ≤ 16109879099537^3103*80000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34139567 80000000 16109879099537 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216370611/5000000000 : ℝ)^4127 ≤ (16945060705163/50000000000000 : ℝ)^3103 := by
    have hnat : (2216370611 : ℕ)^4127*50000000000000^3103 ≤ 16945060705163^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216370611 5000000000 16945060705163 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4432741121/10000000000 : ℝ)^4127 ≤ (8472530095829/25000000000000 : ℝ)^3103 := by
    have hnat : (4432741121 : ℕ)^4127*25000000000000^3103 ≤ 8472530095829^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432741121 10000000000 8472530095829 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34139567/80000000 : ℝ), (2216370611/5000000000 : ℝ), (4432741121/10000000000 : ℝ)] ![(16109879099537/50000000000000 : ℝ), (16945060705163/50000000000000 : ℝ), (8472530095829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34139567/80000000 : ℝ)|^4127 ≤ (16109879099537/50000000000000 : ℝ)^3103
        have hw : |(34139567/80000000 : ℝ)|=(34139567/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2216370611/5000000000 : ℝ)|^4127 ≤ (16945060705163/50000000000000 : ℝ)^3103
        have hw : |(2216370611/5000000000 : ℝ)|=(2216370611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4432741121/10000000000 : ℝ)|^4127 ≤ (8472530095829/25000000000000 : ℝ)^3103
        have hw : |(4432741121/10000000000 : ℝ)|=(4432741121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_8 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1141423341/5000000000 : ℝ)*x 0 + (2606961827/5000000000 : ℝ)*x 1 + (2693516259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1141423341/5000000000 : ℝ)^4127 ≤ (2804154891997/20000000000000 : ℝ)^3103 := by
    have hnat : (1141423341 : ℕ)^4127*20000000000000^3103 ≤ 2804154891997^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141423341 5000000000 2804154891997 20000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606961827/5000000000 : ℝ)^4127 ≤ (42056012825689/100000000000000 : ℝ)^3103 := by
    have hnat : (2606961827 : ℕ)^4127*100000000000000^3103 ≤ 42056012825689^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606961827 5000000000 42056012825689 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693516259/5000000000 : ℝ)^4127 ≤ (1756928507709/4000000000000 : ℝ)^3103 := by
    have hnat : (2693516259 : ℕ)^4127*4000000000000^3103 ≤ 1756928507709^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693516259 5000000000 1756928507709 4000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1141423341/5000000000 : ℝ), (2606961827/5000000000 : ℝ), (2693516259/5000000000 : ℝ)] ![(2804154891997/20000000000000 : ℝ), (42056012825689/100000000000000 : ℝ), (1756928507709/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1141423341/5000000000 : ℝ)|^4127 ≤ (2804154891997/20000000000000 : ℝ)^3103
        have hw : |(-1141423341/5000000000 : ℝ)|=(1141423341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606961827/5000000000 : ℝ)|^4127 ≤ (42056012825689/100000000000000 : ℝ)^3103
        have hw : |(2606961827/5000000000 : ℝ)|=(2606961827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693516259/5000000000 : ℝ)|^4127 ≤ (1756928507709/4000000000000 : ℝ)^3103
        have hw : |(2693516259/5000000000 : ℝ)|=(2693516259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_9 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288349451/10000000000 : ℝ)*x 0 + (-1092080911/5000000000 : ℝ)*x 1 + (1346758167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288349451/10000000000 : ℝ)^4127 ≤ (42856322515237/100000000000000 : ℝ)^3103 := by
    have hnat : (5288349451 : ℕ)^4127*100000000000000^3103 ≤ 42856322515237^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288349451 10000000000 42856322515237 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092080911/5000000000 : ℝ)^4127 ≤ (13220463155201/100000000000000 : ℝ)^3103 := by
    have hnat : (1092080911 : ℕ)^4127*100000000000000^3103 ≤ 13220463155201^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092080911 5000000000 13220463155201 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346758167/2500000000 : ℝ)^4127 ≤ (21961607159677/50000000000000 : ℝ)^3103 := by
    have hnat : (1346758167 : ℕ)^4127*50000000000000^3103 ≤ 21961607159677^3103*2500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346758167 2500000000 21961607159677 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288349451/10000000000 : ℝ), (-1092080911/5000000000 : ℝ), (1346758167/2500000000 : ℝ)] ![(42856322515237/100000000000000 : ℝ), (13220463155201/100000000000000 : ℝ), (21961607159677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288349451/10000000000 : ℝ)|^4127 ≤ (42856322515237/100000000000000 : ℝ)^3103
        have hw : |(5288349451/10000000000 : ℝ)|=(5288349451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092080911/5000000000 : ℝ)|^4127 ≤ (13220463155201/100000000000000 : ℝ)^3103
        have hw : |(-1092080911/5000000000 : ℝ)|=(1092080911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346758167/2500000000 : ℝ)|^4127 ≤ (21961607159677/50000000000000 : ℝ)^3103
        have hw : |(1346758167/2500000000 : ℝ)|=(1346758167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_10 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057669871/2000000000 : ℝ)*x 0 + (2693515913/5000000000 : ℝ)*x 1 + (-546040771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057669871/2000000000 : ℝ)^4127 ≤ (42856321480527/100000000000000 : ℝ)^3103 := by
    have hnat : (1057669871 : ℕ)^4127*100000000000000^3103 ≤ 42856321480527^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057669871 2000000000 42856321480527 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693515913/5000000000 : ℝ)^4127 ≤ (686300081071/1562500000000 : ℝ)^3103 := by
    have hnat : (2693515913 : ℕ)^4127*1562500000000^3103 ≤ 686300081071^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693515913 5000000000 686300081071 1562500000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546040771/2500000000 : ℝ)^4127 ≤ (13220473314739/100000000000000 : ℝ)^3103 := by
    have hnat : (546040771 : ℕ)^4127*100000000000000^3103 ≤ 13220473314739^3103*2500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546040771 2500000000 13220473314739 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057669871/2000000000 : ℝ), (2693515913/5000000000 : ℝ), (-546040771/2500000000 : ℝ)] ![(42856321480527/100000000000000 : ℝ), (686300081071/1562500000000 : ℝ), (13220473314739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057669871/2000000000 : ℝ)|^4127 ≤ (42856321480527/100000000000000 : ℝ)^3103
        have hw : |(1057669871/2000000000 : ℝ)|=(1057669871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693515913/5000000000 : ℝ)|^4127 ≤ (686300081071/1562500000000 : ℝ)^3103
        have hw : |(2693515913/5000000000 : ℝ)|=(2693515913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-546040771/2500000000 : ℝ)|^4127 ≤ (13220473314739/100000000000000 : ℝ)^3103
        have hw : |(-546040771/2500000000 : ℝ)|=(546040771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_11 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2252892333/5000000000 : ℝ)*x 0 + (4313452341/10000000000 : ℝ)*x 1 + (4313453181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2252892333/5000000000 : ℝ)^4127 ≤ (34634869827013/100000000000000 : ℝ)^3103 := by
    have hnat : (2252892333 : ℕ)^4127*100000000000000^3103 ≤ 34634869827013^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252892333 5000000000 34634869827013 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4313452341/10000000000 : ℝ)^4127 ≤ (16341280421909/50000000000000 : ℝ)^3103 := by
    have hnat : (4313452341 : ℕ)^4127*50000000000000^3103 ≤ 16341280421909^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313452341 10000000000 16341280421909 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4313453181/10000000000 : ℝ)^4127 ≤ (16341284654371/50000000000000 : ℝ)^3103 := by
    have hnat : (4313453181 : ℕ)^4127*50000000000000^3103 ≤ 16341284654371^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313453181 10000000000 16341284654371 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2252892333/5000000000 : ℝ), (4313452341/10000000000 : ℝ), (4313453181/10000000000 : ℝ)] ![(34634869827013/100000000000000 : ℝ), (16341280421909/50000000000000 : ℝ), (16341284654371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2252892333/5000000000 : ℝ)|^4127 ≤ (34634869827013/100000000000000 : ℝ)^3103
        have hw : |(2252892333/5000000000 : ℝ)|=(2252892333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4313452341/10000000000 : ℝ)|^4127 ≤ (16341280421909/50000000000000 : ℝ)^3103
        have hw : |(4313452341/10000000000 : ℝ)|=(4313452341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4313453181/10000000000 : ℝ)|^4127 ≤ (16341284654371/50000000000000 : ℝ)^3103
        have hw : |(4313453181/10000000000 : ℝ)|=(4313453181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_12 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-266422943/1250000000 : ℝ)*x 0 + (85034167/156250000 : ℝ)*x 1 + (5272018521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266422943/1250000000 : ℝ)^4127 ≤ (639864152239/5000000000000 : ℝ)^3103 := by
    have hnat : (266422943 : ℕ)^4127*5000000000000^3103 ≤ 639864152239^3103*1250000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266422943 1250000000 639864152239 5000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85034167/156250000 : ℝ)^4127 ≤ (44522323194179/100000000000000 : ℝ)^3103 := by
    have hnat : (85034167 : ℕ)^4127*100000000000000^3103 ≤ 44522323194179^3103*156250000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85034167 156250000 44522323194179 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272018521/10000000000 : ℝ)^4127 ≤ (533504921813/1250000000000 : ℝ)^3103 := by
    have hnat : (5272018521 : ℕ)^4127*1250000000000^3103 ≤ 533504921813^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272018521 10000000000 533504921813 1250000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266422943/1250000000 : ℝ), (85034167/156250000 : ℝ), (5272018521/10000000000 : ℝ)] ![(639864152239/5000000000000 : ℝ), (44522323194179/100000000000000 : ℝ), (533504921813/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266422943/1250000000 : ℝ)|^4127 ≤ (639864152239/5000000000000 : ℝ)^3103
        have hw : |(-266422943/1250000000 : ℝ)|=(266422943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85034167/156250000 : ℝ)|^4127 ≤ (44522323194179/100000000000000 : ℝ)^3103
        have hw : |(85034167/156250000 : ℝ)|=(85034167/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272018521/10000000000 : ℝ)|^4127 ≤ (533504921813/1250000000000 : ℝ)^3103
        have hw : |(5272018521/10000000000 : ℝ)|=(5272018521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_13 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671219633/1250000000 : ℝ)*x 0 + (-2229121643/10000000000 : ℝ)*x 1 + (329501179/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671219633/1250000000 : ℝ)^4127 ≤ (10933993388249/25000000000000 : ℝ)^3103 := by
    have hnat : (671219633 : ℕ)^4127*25000000000000^3103 ≤ 10933993388249^3103*1250000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671219633 1250000000 10933993388249 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2229121643/10000000000 : ℝ)^4127 ≤ (6791814498699/50000000000000 : ℝ)^3103 := by
    have hnat : (2229121643 : ℕ)^4127*50000000000000^3103 ≤ 6791814498699^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229121643 10000000000 6791814498699 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329501179/625000000 : ℝ)^4127 ≤ (21340198719101/50000000000000 : ℝ)^3103 := by
    have hnat : (329501179 : ℕ)^4127*50000000000000^3103 ≤ 21340198719101^3103*625000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329501179 625000000 21340198719101 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671219633/1250000000 : ℝ), (-2229121643/10000000000 : ℝ), (329501179/625000000 : ℝ)] ![(10933993388249/25000000000000 : ℝ), (6791814498699/50000000000000 : ℝ), (21340198719101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671219633/1250000000 : ℝ)|^4127 ≤ (10933993388249/25000000000000 : ℝ)^3103
        have hw : |(671219633/1250000000 : ℝ)|=(671219633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2229121643/10000000000 : ℝ)|^4127 ≤ (6791814498699/50000000000000 : ℝ)^3103
        have hw : |(-2229121643/10000000000 : ℝ)|=(2229121643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329501179/625000000 : ℝ)|^4127 ≤ (21340198719101/50000000000000 : ℝ)^3103
        have hw : |(329501179/625000000 : ℝ)|=(329501179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_14 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073951429/2000000000 : ℝ)*x 0 + (5272018413/10000000000 : ℝ)*x 1 + (-2229122133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073951429/2000000000 : ℝ)^4127 ≤ (8747194886089/20000000000000 : ℝ)^3103 := by
    have hnat : (1073951429 : ℕ)^4127*20000000000000^3103 ≤ 8747194886089^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073951429 2000000000 8747194886089 20000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272018413/10000000000 : ℝ)^4127 ≤ (42680392582179/100000000000000 : ℝ)^3103 := by
    have hnat : (5272018413 : ℕ)^4127*100000000000000^3103 ≤ 42680392582179^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272018413 10000000000 42680392582179 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229122133/10000000000 : ℝ)^4127 ≤ (13583632968681/100000000000000 : ℝ)^3103 := by
    have hnat : (2229122133 : ℕ)^4127*100000000000000^3103 ≤ 13583632968681^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229122133 10000000000 13583632968681 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073951429/2000000000 : ℝ), (5272018413/10000000000 : ℝ), (-2229122133/10000000000 : ℝ)] ![(8747194886089/20000000000000 : ℝ), (42680392582179/100000000000000 : ℝ), (13583632968681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073951429/2000000000 : ℝ)|^4127 ≤ (8747194886089/20000000000000 : ℝ)^3103
        have hw : |(1073951429/2000000000 : ℝ)|=(1073951429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272018413/10000000000 : ℝ)|^4127 ≤ (42680392582179/100000000000000 : ℝ)^3103
        have hw : |(5272018413/10000000000 : ℝ)|=(5272018413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2229122133/10000000000 : ℝ)|^4127 ≤ (13583632968681/100000000000000 : ℝ)^3103
        have hw : |(-2229122133/10000000000 : ℝ)|=(2229122133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_box_15 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249382961/10000000000 : ℝ)*x 0 + (4441650963/10000000000 : ℝ)*x 1 + (1110412701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249382961/10000000000 : ℝ)^4127 ≤ (16019251378369/50000000000000 : ℝ)^3103 := by
    have hnat : (4249382961 : ℕ)^4127*50000000000000^3103 ≤ 16019251378369^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249382961 10000000000 16019251378369 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4441650963/10000000000 : ℝ)^4127 ≤ (6796149884933/20000000000000 : ℝ)^3103 := by
    have hnat : (4441650963 : ℕ)^4127*20000000000000^3103 ≤ 6796149884933^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4441650963 10000000000 6796149884933 20000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110412701/2500000000 : ℝ)^4127 ≤ (6796149561363/20000000000000 : ℝ)^3103 := by
    have hnat : (1110412701 : ℕ)^4127*20000000000000^3103 ≤ 6796149561363^3103*2500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110412701 2500000000 6796149561363 20000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249382961/10000000000 : ℝ), (4441650963/10000000000 : ℝ), (1110412701/2500000000 : ℝ)] ![(16019251378369/50000000000000 : ℝ), (6796149884933/20000000000000 : ℝ), (6796149561363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249382961/10000000000 : ℝ)|^4127 ≤ (16019251378369/50000000000000 : ℝ)^3103
        have hw : |(4249382961/10000000000 : ℝ)|=(4249382961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4441650963/10000000000 : ℝ)|^4127 ≤ (6796149884933/20000000000000 : ℝ)^3103
        have hw : |(4441650963/10000000000 : ℝ)|=(4441650963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1110412701/2500000000 : ℝ)|^4127 ≤ (6796149561363/20000000000000 : ℝ)^3103
        have hw : |(1110412701/2500000000 : ℝ)|=(1110412701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1061_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59237/100000 : ℝ) ∧ (79557/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82941/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2249/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2249/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2249/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2249/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2249/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2249/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2249/20000 : ℝ) ^ (8253/2048 : ℝ) ≤ (14982025030363303/100000000000000000000 : ℝ) := by
    have hpowers : (2249/20000 : ℝ)^8253 ≤ (14982025030363303/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2249 : ℕ)^8253*100000000000000000000^2048 ≤ 14982025030363303^2048*20000^8253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2249 20000 14982025030363303 100000000000000000000 8253 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2249/20000 : ℝ)) (X := (14982025030363303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13999/100000 : ℝ) ^ (8253/2048 : ℝ) ≤ (18110249128560131/50000000000000000000 : ℝ) := by
    have hpowers : (13999/100000 : ℝ)^8253 ≤ (18110249128560131/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13999 : ℕ)^8253*50000000000000000000^2048 ≤ 18110249128560131^2048*100000^8253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13999 100000 18110249128560131 50000000000000000000 8253 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13999/100000 : ℝ)) (X := (18110249128560131/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014982025030363303/50000000000000000000 : ℝ) ≤ (1000074348071369/1000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (50014982025030363303/50000000000000000000 : ℝ)^2048 ≤ (1000074348071369/1000000000000000 : ℝ)^8253 := by
      have hnat : (50014982025030363303 : ℕ)^2048*1000000000000000^8253 ≤ 1000074348071369^8253*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014982025030363303 50000000000000000000 1000074348071369 1000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000074348071369/1000000000000000 : ℝ)) (X := (50014982025030363303/50000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010240504657496713/20000000000000000000 : ℝ) ≤ (2500317589329563/2500000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (20010240504657496713/20000000000000000000 : ℝ)^2048 ≤ (2500317589329563/2500000000000000 : ℝ)^8253 := by
      have hnat : (20010240504657496713 : ℕ)^2048*2500000000000000^8253 ≤ 2500317589329563^8253*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010240504657496713 20000000000000000000 2500317589329563 2500000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500317589329563/2500000000000000 : ℝ)) (X := (20010240504657496713/20000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018110249128560131/25000000000000000000 : ℝ) ≤ (5000898616961407/5000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (25018110249128560131/25000000000000000000 : ℝ)^2048 ≤ (5000898616961407/5000000000000000 : ℝ)^8253 := by
      have hnat : (25018110249128560131 : ℕ)^2048*5000000000000000^8253 ≤ 5000898616961407^8253*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018110249128560131 25000000000000000000 5000898616961407 5000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000898616961407/5000000000000000 : ℝ)) (X := (25018110249128560131/25000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14982025030363303/100000000000000000000 : ℝ) ≤ ((57354579356351881/57375000000000000 : ℝ)+2*(87812767427/45900000000000 : ℝ)*(2249/20000 : ℝ))^(8253/2048 : ℝ) := by
    rw [show (57354579356351881/57375000000000000 : ℝ)+2*(87812767427/45900000000000 : ℝ)*(2249/20000 : ℝ)=(1000074348071369/1000000000000000 : ℝ) by norm_num, show 1+2*(14982025030363303/100000000000000000000 : ℝ)=(50014982025030363303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18110249128560131/50000000000000000000 : ℝ)+(14982025030363303/100000000000000000000 : ℝ) ≤ ((57354579356351881/57375000000000000 : ℝ)+(87812767427/45900000000000 : ℝ)*((13999/100000 : ℝ)+(2249/20000 : ℝ)))^(8253/2048 : ℝ) := by
    rw [show (57354579356351881/57375000000000000 : ℝ)+(87812767427/45900000000000 : ℝ)*((13999/100000 : ℝ)+(2249/20000 : ℝ))=(2500317589329563/2500000000000000 : ℝ) by norm_num, show 1+(18110249128560131/50000000000000000000 : ℝ)+(14982025030363303/100000000000000000000 : ℝ)=(20010240504657496713/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18110249128560131/50000000000000000000 : ℝ) ≤ ((57354579356351881/57375000000000000 : ℝ)+2*(87812767427/45900000000000 : ℝ)*(13999/100000 : ℝ))^(8253/2048 : ℝ) := by
    rw [show (57354579356351881/57375000000000000 : ℝ)+2*(87812767427/45900000000000 : ℝ)*(13999/100000 : ℝ)=(5000898616961407/5000000000000000 : ℝ) by norm_num, show 1+2*(18110249128560131/50000000000000000000 : ℝ)=(25018110249128560131/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57354579356351881/57375000000000000 : ℝ)*(X 1 0+X 2 0)+(87812767427/45900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (57354579356351881/57375000000000000 : ℝ)) (alpha := (87812767427/45900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57354579356351881/57375000000000000 : ℝ)*(X 0 1+X 2 1)+(87812767427/45900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (57354579356351881/57375000000000000 : ℝ)) (alpha := (87812767427/45900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57354579356351881/57375000000000000 : ℝ)*(X 0 2+X 1 2)+(87812767427/45900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (57354579356351881/57375000000000000 : ℝ)) (alpha := (87812767427/45900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-415321113/2000000000 : ℝ)*X 0 0+(5377432709/10000000000 : ℝ)*X 0 1+(5377433191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295147157/10000000000 : ℝ)*X 1 0+(-136749071/625000000 : ℝ)*X 1 1+(268871647/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295147247/10000000000 : ℝ)*X 2 0+(336089567/625000000 : ℝ)*X 2 1+(-2187984839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((560581687/1250000000 : ℝ)*X 0 0+(1081039713/2500000000 : ℝ)*X 0 1+(4324158871/10000000000 : ℝ)*X 0 2+(560581687/1250000000 : ℝ)*X 1 0+(1081039713/2500000000 : ℝ)*X 1 1+(4324158871/10000000000 : ℝ)*X 1 2+(560581687/1250000000 : ℝ)*X 2 0+(1081039713/2500000000 : ℝ)*X 2 1+(4324158871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2337252643/10000000000 : ℝ)*X 0 0+(2640008331/5000000000 : ℝ)*X 0 1+(2640008327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364098287/10000000000 : ℝ)*X 1 0+(-2226055217/10000000000 : ℝ)*X 1 1+(5280016677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364098317/10000000000 : ℝ)*X 2 0+(5280016647/10000000000 : ℝ)*X 2 1+(-2226055217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34139567/80000000 : ℝ)*X 0 0+(2216370611/5000000000 : ℝ)*X 0 1+(4432741121/10000000000 : ℝ)*X 0 2+(34139567/80000000 : ℝ)*X 1 0+(2216370611/5000000000 : ℝ)*X 1 1+(4432741121/10000000000 : ℝ)*X 1 2+(34139567/80000000 : ℝ)*X 2 0+(2216370611/5000000000 : ℝ)*X 2 1+(4432741121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1141423341/5000000000 : ℝ)*X 0 0+(2606961827/5000000000 : ℝ)*X 0 1+(2693516259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288349451/10000000000 : ℝ)*X 1 0+(-1092080911/5000000000 : ℝ)*X 1 1+(1346758167/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057669871/2000000000 : ℝ)*X 2 0+(2693515913/5000000000 : ℝ)*X 2 1+(-546040771/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2252892333/5000000000 : ℝ)*X 0 0+(4313452341/10000000000 : ℝ)*X 0 1+(4313453181/10000000000 : ℝ)*X 0 2+(2252892333/5000000000 : ℝ)*X 1 0+(4313452341/10000000000 : ℝ)*X 1 1+(4313453181/10000000000 : ℝ)*X 1 2+(2252892333/5000000000 : ℝ)*X 2 0+(4313452341/10000000000 : ℝ)*X 2 1+(4313453181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-266422943/1250000000 : ℝ)*X 0 0+(85034167/156250000 : ℝ)*X 0 1+(5272018521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671219633/1250000000 : ℝ)*X 1 0+(-2229121643/10000000000 : ℝ)*X 1 1+(329501179/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1073951429/2000000000 : ℝ)*X 2 0+(5272018413/10000000000 : ℝ)*X 2 1+(-2229122133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4249382961/10000000000 : ℝ)*X 0 0+(4441650963/10000000000 : ℝ)*X 0 1+(1110412701/2500000000 : ℝ)*X 0 2+(4249382961/10000000000 : ℝ)*X 1 0+(4441650963/10000000000 : ℝ)*X 1 1+(1110412701/2500000000 : ℝ)*X 1 2+(4249382961/10000000000 : ℝ)*X 2 0+(4441650963/10000000000 : ℝ)*X 2 1+(1110412701/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-37187212710076835716812393737/59765625000000000000000000000 : ℝ) := by norm_num
    linear_combination (11121953/12500000000000 : ℝ)*(upper0) + (15502949/12500000000000 : ℝ)*(upper1) + (83266547/100000000000000 : ℝ)*(upper3) + (100330207/100000000000000 : ℝ)*(upper5) + (963126341489171/25000000000000 : ℝ)*(major0) + (963126341489171/25000000000000 : ℝ)*(major1) + (963126341489171/25000000000000 : ℝ)*(major2) + (5867231223/50000000000000 : ℝ)*(sp3) + (1280217489102027/25000000000000 : ℝ)*(sp4) + (5120845688272499/100000000000000 : ℝ)*(sp5) + (5120872836574409/100000000000000 : ℝ)*(sp6) + (2604866741385817/100000000000000 : ℝ)*(sp7) + (2880166301/100000000000000 : ℝ)*(sp8) + (2714830191/10000000000000 : ℝ)*(sp13) + (1302439237924131/50000000000000 : ℝ)*(f.failure) + (5120872836574409/100000000000000 : ℝ)*(f.sum) + (8310325240607/2295000000000000000000000000 : ℝ)*base66 + (22820358936885599/1434375000000000000000000000000 : ℝ)*base68 + (26676767727916237/717187500000000000000000000000 : ℝ)*base70 + (5808625290173099/1434375000000000000000000000000 : ℝ)*base72 + (29007220264933/2295000000000000000000000000 : ℝ)*base73 + (50674538226041849/1434375000000000000000000000000 : ℝ)*base76 + (3886373739548099/1434375000000000000000000000000 : ℝ)*base78 + (37484288284202513/717187500000000000000000000000 : ℝ)*base79 + (9487737645541/1147500000000000000000000000 : ℝ)*base82 + (27008689/5000000000000000000000 : ℝ)*base90 + (27008689/5000000000000000000000 : ℝ)*base92 + (27008689/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59237/100000 : ℝ) ≤ (94413111338656690704145950977/159375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112999351/100000000000000 : ℝ)*(lower3) + (56082669/50000000000000 : ℝ)*(upper4) + (2279057/25000000000000 : ℝ)*(upper5) + (1957663542983037/50000000000000 : ℝ)*(major0) + (1957663542983037/50000000000000 : ℝ)*(major1) + (1957663542983037/50000000000000 : ℝ)*(major2) + (5163546142639073/100000000000000 : ℝ)*(sp0) + (2581773677287581/50000000000000 : ℝ)*(sp1) + (1290884456759189/25000000000000 : ℝ)*(sp2) + (1323675469537069/50000000000000 : ℝ)*(sp3) + (2394366391/50000000000000 : ℝ)*(sp5) + (3579067797/25000000000000 : ℝ)*(sp6) + (4556459621/100000000000000 : ℝ)*(sp7) + (600066887/10000000000000 : ℝ)*(sp12) + (8272985923543/312500000000 : ℝ)*(f.failure) + (645444017913493/12500000000000 : ℝ)*(f.sum) + (14202740653/23906250000000000000000000 : ℝ)*base65 + (6470557461211699/956250000000000000000000000000 : ℝ)*base67 + (4971866236580449/956250000000000000000000000000 : ℝ)*base69 + (2821363128661699/956250000000000000000000000000 : ℝ)*base71 + (432670935407/382500000000000000000000000 : ℝ)*base74 + (1156975251624199/956250000000000000000000000000 : ℝ)*base75 + (9387413151286699/956250000000000000000000000000 : ℝ)*base77 + (2077188925682051/956250000000000000000000000000 : ℝ)*base80 + (4166160630731/765000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (147083/31250000000000000000 : ℝ)*base89 + (147083/31250000000000000000 : ℝ)*base91 + (147083/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79557/100000 : ℝ) ≤ (4226573053299049805920252889/5312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (136843909/20000000000000 : ℝ)*(upper0) + (19771291/100000000000000 : ℝ)*(lower1) + (46113137/25000000000000 : ℝ)*(upper2) + (115291567/100000000000000 : ℝ)*(lower3) + (613389327/50000000000000 : ℝ)*(lower5) + (438354194712771/10000000000000 : ℝ)*(major0) + (438354194712771/10000000000000 : ℝ)*(major1) + (438354194712771/10000000000000 : ℝ)*(major2) + (11860338863/6250000000000 : ℝ)*(sp1) + (5104104863/4000000000000 : ℝ)*(sp3) + (1155324879772869/20000000000000 : ℝ)*(sp8) + (722054329180317/12500000000000 : ℝ)*(sp9) + (1155324879772869/20000000000000 : ℝ)*(sp10) + (370476527338697/12500000000000 : ℝ)*(sp11) + (2963939821331151/100000000000000 : ℝ)*(f.failure) + (1155324879772869/20000000000000 : ℝ)*(f.sum) + (894932041/153000000000000000000000 : ℝ)*base65 + (4035678624391333/191250000000000000000000000000 : ℝ)*base68 + (3862713624747583/191250000000000000000000000000 : ℝ)*base70 + (370529096498833/191250000000000000000000000000 : ℝ)*base72 + (1034728043/15300000000000000000000000 : ℝ)*base74 + (282618976340083/191250000000000000000000000000 : ℝ)*base76 + (283431175877417/191250000000000000000000000000 : ℝ)*base77 + (3201623478166333/191250000000000000000000000000 : ℝ)*base80 + (8586668761/6120000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (36773931/10000000000000000000000 : ℝ)*base89 + (36773931/10000000000000000000000 : ℝ)*base91 + (36773931/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82941/100000 : ℝ) ≤ (-44061075194499445524217330717/53125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (390153/400000000000 : ℝ)*(lower0) + (4475779/20000000000000 : ℝ)*(lower1) + (26567609/20000000000000 : ℝ)*(upper3) + (187563071/100000000000000 : ℝ)*(lower4) + (552263600481111/12500000000000 : ℝ)*(major0) + (552263600481111/12500000000000 : ℝ)*(major1) + (552263600481111/12500000000000 : ℝ)*(major2) + (4396805587/100000000000000 : ℝ)*(sp0) + (51946078339/12500000000000 : ℝ)*(sp6) + (83293604683/100000000000000 : ℝ)*(sp7) + (2938273555827151/50000000000000 : ℝ)*(sp12) + (5876551508459889/100000000000000 : ℝ)*(sp13) + (5876135939833177/100000000000000 : ℝ)*(sp14) + (298722897046111/10000000000000 : ℝ)*(sp15) + (2987312264065793/100000000000000 : ℝ)*(f.failure) + (5876551508459889/100000000000000 : ℝ)*(f.sum) + (220415336437/31875000000000000000000000 : ℝ)*base66 + (2228263774658773/159375000000000000000000000000 : ℝ)*base67 + (636456813471169/19921875000000000000000000000 : ℝ)*base70 + (758727985546273/159375000000000000000000000000 : ℝ)*base71 + (1129732488431/255000000000000000000000000 : ℝ)*base74 + (1698679828208773/159375000000000000000000000000 : ℝ)*base75 + (265742569143449/79687500000000000000000000000 : ℝ)*base77 + (804871974327523/159375000000000000000000000000 : ℝ)*base79 + (2127802695613/127500000000000000000000000 : ℝ)*base82 + (108880667/10000000000000000000000 : ℝ)*base90 + (108880667/10000000000000000000000 : ℝ)*base92 + (108880667/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1061_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59237/100000 : ℝ) else (79557/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82941/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1061_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1061_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59237/100000 : ℝ) else (79557/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82941/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1061_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1061_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59237/100000 : ℝ) else (79557/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82941/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1061_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
