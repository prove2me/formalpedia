-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1224_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:20.009042+00:00
-- url     : https://prove2.me/submissions/a4e61f63-277b-4b3e-93f4-4688a81d616a

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
theorem support_rectangle_w1224_s0_0 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-466531711/2500000000 : ℝ)*x 0 + (6035571373/10000000000 : ℝ)*x 1 + (4790754659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466531711/2500000000 : ℝ)^8417 ≤ (10876941430389/100000000000000 : ℝ)^6369 := by
    have hnat : (466531711 : ℕ)^8417*100000000000000^6369 ≤ 10876941430389^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466531711 2500000000 10876941430389 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6035571373/10000000000 : ℝ)^8417 ≤ (10262111513547/20000000000000 : ℝ)^6369 := by
    have hnat : (6035571373 : ℕ)^8417*20000000000000^6369 ≤ 10262111513547^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6035571373 10000000000 10262111513547 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4790754659/10000000000 : ℝ)^8417 ≤ (7562500198003/20000000000000 : ℝ)^6369 := by
    have hnat : (4790754659 : ℕ)^8417*20000000000000^6369 ≤ 7562500198003^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790754659 10000000000 7562500198003 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-466531711/2500000000 : ℝ), (6035571373/10000000000 : ℝ), (4790754659/10000000000 : ℝ)] ![(10876941430389/100000000000000 : ℝ), (10262111513547/20000000000000 : ℝ), (7562500198003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-466531711/2500000000 : ℝ)|^8417 ≤ (10876941430389/100000000000000 : ℝ)^6369
        have hw : |(-466531711/2500000000 : ℝ)|=(466531711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6035571373/10000000000 : ℝ)|^8417 ≤ (10262111513547/20000000000000 : ℝ)^6369
        have hw : |(6035571373/10000000000 : ℝ)|=(6035571373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4790754659/10000000000 : ℝ)|^8417 ≤ (7562500198003/20000000000000 : ℝ)^6369
        have hw : |(4790754659/10000000000 : ℝ)|=(4790754659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s0_1 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5512173589/10000000000 : ℝ)*x 0 + (-644561651/2500000000 : ℝ)*x 1 + (598844327/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512173589/10000000000 : ℝ)^8417 ≤ (45513822167379/100000000000000 : ℝ)^6369 := by
    have hnat : (5512173589 : ℕ)^8417*100000000000000^6369 ≤ 45513822167379^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512173589 10000000000 45513822167379 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644561651/2500000000 : ℝ)^8417 ≤ (2084209660297/12500000000000 : ℝ)^6369 := by
    have hnat : (644561651 : ℕ)^8417*12500000000000^6369 ≤ 2084209660297^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644561651 2500000000 2084209660297 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598844327/1250000000 : ℝ)^8417 ≤ (3781250054149/10000000000000 : ℝ)^6369 := by
    have hnat : (598844327 : ℕ)^8417*10000000000000^6369 ≤ 3781250054149^6369*1250000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598844327 1250000000 3781250054149 10000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512173589/10000000000 : ℝ), (-644561651/2500000000 : ℝ), (598844327/1250000000 : ℝ)] ![(45513822167379/100000000000000 : ℝ), (2084209660297/12500000000000 : ℝ), (3781250054149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512173589/10000000000 : ℝ)|^8417 ≤ (45513822167379/100000000000000 : ℝ)^6369
        have hw : |(5512173589/10000000000 : ℝ)|=(5512173589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-644561651/2500000000 : ℝ)|^8417 ≤ (2084209660297/12500000000000 : ℝ)^6369
        have hw : |(-644561651/2500000000 : ℝ)|=(644561651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598844327/1250000000 : ℝ)|^8417 ≤ (3781250054149/10000000000000 : ℝ)^6369
        have hw : |(598844327/1250000000 : ℝ)|=(598844327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s0_2 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (110243471/200000000 : ℝ)*x 0 + (4790754663/10000000000 : ℝ)*x 1 + (-515649319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110243471/200000000 : ℝ)^8417 ≤ (45513821741809/100000000000000 : ℝ)^6369 := by
    have hnat : (110243471 : ℕ)^8417*100000000000000^6369 ≤ 45513821741809^6369*200000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110243471 200000000 45513821741809 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4790754663/10000000000 : ℝ)^8417 ≤ (18906250515869/50000000000000 : ℝ)^6369 := by
    have hnat : (4790754663 : ℕ)^8417*50000000000000^6369 ≤ 18906250515869^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790754663 10000000000 18906250515869 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515649319/2000000000 : ℝ)^8417 ≤ (1042104825341/6250000000000 : ℝ)^6369 := by
    have hnat : (515649319 : ℕ)^8417*6250000000000^6369 ≤ 1042104825341^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515649319 2000000000 1042104825341 6250000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(110243471/200000000 : ℝ), (4790754663/10000000000 : ℝ), (-515649319/2000000000 : ℝ)] ![(45513821741809/100000000000000 : ℝ), (18906250515869/50000000000000 : ℝ), (1042104825341/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(110243471/200000000 : ℝ)|^8417 ≤ (45513821741809/100000000000000 : ℝ)^6369
        have hw : |(110243471/200000000 : ℝ)|=(110243471/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4790754663/10000000000 : ℝ)|^8417 ≤ (18906250515869/50000000000000 : ℝ)^6369
        have hw : |(4790754663/10000000000 : ℝ)|=(4790754663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515649319/2000000000 : ℝ)|^8417 ≤ (1042104825341/6250000000000 : ℝ)^6369
        have hw : |(-515649319/2000000000 : ℝ)|=(515649319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s0_3 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4194438939/10000000000 : ℝ)*x 0 + (1558790081/5000000000 : ℝ)*x 1 + (1408501231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4194438939/10000000000 : ℝ)^8417 ≤ (6344126154631/20000000000000 : ℝ)^6369 := by
    have hnat : (4194438939 : ℕ)^8417*20000000000000^6369 ≤ 6344126154631^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194438939 10000000000 6344126154631 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1558790081/5000000000 : ℝ)^8417 ≤ (4286283227339/20000000000000 : ℝ)^6369 := by
    have hnat : (1558790081 : ℕ)^8417*20000000000000^6369 ≤ 4286283227339^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558790081 5000000000 4286283227339 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1408501231/2500000000 : ℝ)^8417 ≤ (46847953081443/100000000000000 : ℝ)^6369 := by
    have hnat : (1408501231 : ℕ)^8417*100000000000000^6369 ≤ 46847953081443^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408501231 2500000000 46847953081443 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4194438939/10000000000 : ℝ), (1558790081/5000000000 : ℝ), (1408501231/2500000000 : ℝ)] ![(6344126154631/20000000000000 : ℝ), (4286283227339/20000000000000 : ℝ), (46847953081443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4194438939/10000000000 : ℝ)|^8417 ≤ (6344126154631/20000000000000 : ℝ)^6369
        have hw : |(4194438939/10000000000 : ℝ)|=(4194438939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1558790081/5000000000 : ℝ)|^8417 ≤ (4286283227339/20000000000000 : ℝ)^6369
        have hw : |(1558790081/5000000000 : ℝ)|=(1558790081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1408501231/2500000000 : ℝ)|^8417 ≤ (46847953081443/100000000000000 : ℝ)^6369
        have hw : |(1408501231/2500000000 : ℝ)|=(1408501231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s0_4 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1871035873/10000000000 : ℝ)*x 0 + (2411411407/5000000000 : ℝ)*x 1 + (6002370253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1871035873/10000000000 : ℝ)^8417 ≤ (1364346368901/12500000000000 : ℝ)^6369 := by
    have hnat : (1871035873 : ℕ)^8417*12500000000000^6369 ≤ 1364346368901^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871035873 10000000000 1364346368901 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2411411407/5000000000 : ℝ)^8417 ≤ (596052451497/1562500000000 : ℝ)^6369 := by
    have hnat : (2411411407 : ℕ)^8417*1562500000000^6369 ≤ 596052451497^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411411407 5000000000 596052451497 1562500000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6002370253/10000000000 : ℝ)^8417 ≤ (25468936073121/50000000000000 : ℝ)^6369 := by
    have hnat : (6002370253 : ℕ)^8417*50000000000000^6369 ≤ 25468936073121^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6002370253 10000000000 25468936073121 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1871035873/10000000000 : ℝ), (2411411407/5000000000 : ℝ), (6002370253/10000000000 : ℝ)] ![(1364346368901/12500000000000 : ℝ), (596052451497/1562500000000 : ℝ), (25468936073121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1871035873/10000000000 : ℝ)|^8417 ≤ (1364346368901/12500000000000 : ℝ)^6369
        have hw : |(-1871035873/10000000000 : ℝ)|=(1871035873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2411411407/5000000000 : ℝ)|^8417 ≤ (596052451497/1562500000000 : ℝ)^6369
        have hw : |(2411411407/5000000000 : ℝ)|=(2411411407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6002370253/10000000000 : ℝ)|^8417 ≤ (25468936073121/50000000000000 : ℝ)^6369
        have hw : |(6002370253/10000000000 : ℝ)|=(6002370253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s0_5 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1034710779/2000000000 : ℝ)*x 0 + (-1366629091/10000000000 : ℝ)*x 1 + (3001186093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034710779/2000000000 : ℝ)^8417 ≤ (20927900821111/50000000000000 : ℝ)^6369 := by
    have hnat : (1034710779 : ℕ)^8417*50000000000000^6369 ≤ 20927900821111^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034710779 2000000000 20927900821111 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366629091/10000000000 : ℝ)^8417 ≤ (3603152259729/50000000000000 : ℝ)^6369 := by
    have hnat : (1366629091 : ℕ)^8417*50000000000000^6369 ≤ 3603152259729^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366629091 10000000000 3603152259729 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3001186093/5000000000 : ℝ)^8417 ≤ (50937893825079/100000000000000 : ℝ)^6369 := by
    have hnat : (3001186093 : ℕ)^8417*100000000000000^6369 ≤ 50937893825079^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3001186093 5000000000 50937893825079 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034710779/2000000000 : ℝ), (-1366629091/10000000000 : ℝ), (3001186093/5000000000 : ℝ)] ![(20927900821111/50000000000000 : ℝ), (3603152259729/50000000000000 : ℝ), (50937893825079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034710779/2000000000 : ℝ)|^8417 ≤ (20927900821111/50000000000000 : ℝ)^6369
        have hw : |(1034710779/2000000000 : ℝ)|=(1034710779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1366629091/10000000000 : ℝ)|^8417 ≤ (3603152259729/50000000000000 : ℝ)^6369
        have hw : |(-1366629091/10000000000 : ℝ)|=(1366629091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3001186093/5000000000 : ℝ)|^8417 ≤ (50937893825079/100000000000000 : ℝ)^6369
        have hw : |(3001186093/5000000000 : ℝ)|=(3001186093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s0_6 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173554889/10000000000 : ℝ)*x 0 + (6002370681/10000000000 : ℝ)*x 1 + (-341657497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173554889/10000000000 : ℝ)^8417 ≤ (41855812269919/100000000000000 : ℝ)^6369 := by
    have hnat : (5173554889 : ℕ)^8417*100000000000000^6369 ≤ 41855812269919^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173554889 10000000000 41855812269919 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6002370681/10000000000 : ℝ)^8417 ≤ (12734469236579/25000000000000 : ℝ)^6369 := by
    have hnat : (6002370681 : ℕ)^8417*25000000000000^6369 ≤ 12734469236579^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6002370681 10000000000 12734469236579 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341657497/2500000000 : ℝ)^8417 ≤ (900788846291/12500000000000 : ℝ)^6369 := by
    have hnat : (341657497 : ℕ)^8417*12500000000000^6369 ≤ 900788846291^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341657497 2500000000 900788846291 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173554889/10000000000 : ℝ), (6002370681/10000000000 : ℝ), (-341657497/2500000000 : ℝ)] ![(41855812269919/100000000000000 : ℝ), (12734469236579/25000000000000 : ℝ), (900788846291/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173554889/10000000000 : ℝ)|^8417 ≤ (41855812269919/100000000000000 : ℝ)^6369
        have hw : |(5173554889/10000000000 : ℝ)|=(5173554889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6002370681/10000000000 : ℝ)|^8417 ≤ (12734469236579/25000000000000 : ℝ)^6369
        have hw : |(6002370681/10000000000 : ℝ)|=(6002370681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-341657497/2500000000 : ℝ)|^8417 ≤ (900788846291/12500000000000 : ℝ)^6369
        have hw : |(-341657497/2500000000 : ℝ)|=(341657497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s0_7 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4204361941/10000000000 : ℝ)*x 0 + (222767319/400000000 : ℝ)*x 1 + (1592345707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204361941/10000000000 : ℝ)^8417 ≤ (1272793692291/4000000000000 : ℝ)^6369 := by
    have hnat : (4204361941 : ℕ)^8417*4000000000000^6369 ≤ 1272793692291^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204361941 10000000000 1272793692291 4000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222767319/400000000 : ℝ)^8417 ≤ (46136943687977/100000000000000 : ℝ)^6369 := by
    have hnat : (222767319 : ℕ)^8417*100000000000000^6369 ≤ 46136943687977^6369*400000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222767319 400000000 46136943687977 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592345707/5000000000 : ℝ)^8417 ≤ (2755401748369/12500000000000 : ℝ)^6369 := by
    have hnat : (1592345707 : ℕ)^8417*12500000000000^6369 ≤ 2755401748369^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592345707 5000000000 2755401748369 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204361941/10000000000 : ℝ), (222767319/400000000 : ℝ), (1592345707/5000000000 : ℝ)] ![(1272793692291/4000000000000 : ℝ), (46136943687977/100000000000000 : ℝ), (2755401748369/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204361941/10000000000 : ℝ)|^8417 ≤ (1272793692291/4000000000000 : ℝ)^6369
        have hw : |(4204361941/10000000000 : ℝ)|=(4204361941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(222767319/400000000 : ℝ)|^8417 ≤ (46136943687977/100000000000000 : ℝ)^6369
        have hw : |(222767319/400000000 : ℝ)|=(222767319/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592345707/5000000000 : ℝ)|^8417 ≤ (2755401748369/12500000000000 : ℝ)^6369
        have hw : |(1592345707/5000000000 : ℝ)|=(1592345707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1224_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (373/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1719/6250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (263/64 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^263 ≤ (0 : ℝ)^64 := by
      have hnat : (0 : ℕ)^263*1^64 ≤ 0^64*1^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (263/64 : ℝ) ≤ (2315875865685111413/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^263 ≤ (2315875865685111413/100000000000000000000 : ℝ)^64 := by
      have hnat : (2 : ℕ)^263*100000000000000000000^64 ≤ 2315875865685111413^64*5^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2315875865685111413 100000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2315875865685111413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (1 : ℝ)^64 ≤ (1 : ℝ)^263 := by
      have hnat : (1 : ℕ)^64*1^263 ≤ 1^263*1^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (102315875865685111413/100000000000000000000 : ℝ) ≤ (2011173747660663/2000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (102315875865685111413/100000000000000000000 : ℝ)^64 ≤ (2011173747660663/2000000000000000 : ℝ)^263 := by
      have hnat : (102315875865685111413 : ℕ)^64*2000000000000000^263 ≤ 2011173747660663^263*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102315875865685111413 100000000000000000000 2011173747660663 2000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011173747660663/2000000000000000 : ℝ)) (X := (102315875865685111413/100000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (52315875865685111413/50000000000000000000 : ℝ) ≤ (1011173747660663/1000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (52315875865685111413/50000000000000000000 : ℝ)^64 ≤ (1011173747660663/1000000000000000 : ℝ)^263 := by
      have hnat : (52315875865685111413 : ℕ)^64*1000000000000000^263 ≤ 1011173747660663^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52315875865685111413 50000000000000000000 1011173747660663 1000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011173747660663/1000000000000000 : ℝ)) (X := (52315875865685111413/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11173747660663/800000000000000 : ℝ)*(0 : ℝ))^(263/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(11173747660663/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2315875865685111413/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11173747660663/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(263/64 : ℝ) := by
    rw [show (1 : ℝ)+(11173747660663/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011173747660663/2000000000000000 : ℝ) by norm_num, show 1+(2315875865685111413/100000000000000000000 : ℝ)+(0 : ℝ)=(102315875865685111413/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2315875865685111413/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11173747660663/800000000000000 : ℝ)*(2/5 : ℝ))^(263/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(11173747660663/800000000000000 : ℝ)*(2/5 : ℝ)=(1011173747660663/1000000000000000 : ℝ) by norm_num, show 1+2*(2315875865685111413/100000000000000000000 : ℝ)=(52315875865685111413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11173747660663/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11173747660663/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11173747660663/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11173747660663/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11173747660663/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11173747660663/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-466531711/2500000000 : ℝ)*X 0 0+(6035571373/10000000000 : ℝ)*X 0 1+(4790754659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512173589/10000000000 : ℝ)*X 1 0+(-644561651/2500000000 : ℝ)*X 1 1+(598844327/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((110243471/200000000 : ℝ)*X 2 0+(4790754663/10000000000 : ℝ)*X 2 1+(-515649319/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4194438939/10000000000 : ℝ)*X 0 0+(1558790081/5000000000 : ℝ)*X 0 1+(1408501231/2500000000 : ℝ)*X 0 2+(4194438939/10000000000 : ℝ)*X 1 0+(1558790081/5000000000 : ℝ)*X 1 1+(1408501231/2500000000 : ℝ)*X 1 2+(4194438939/10000000000 : ℝ)*X 2 0+(1558790081/5000000000 : ℝ)*X 2 1+(1408501231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1871035873/10000000000 : ℝ)*X 0 0+(2411411407/5000000000 : ℝ)*X 0 1+(6002370253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1034710779/2000000000 : ℝ)*X 1 0+(-1366629091/10000000000 : ℝ)*X 1 1+(3001186093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173554889/10000000000 : ℝ)*X 2 0+(6002370681/10000000000 : ℝ)*X 2 1+(-341657497/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4204361941/10000000000 : ℝ)*X 0 0+(222767319/400000000 : ℝ)*X 0 1+(1592345707/5000000000 : ℝ)*X 0 2+(4204361941/10000000000 : ℝ)*X 1 0+(222767319/400000000 : ℝ)*X 1 1+(1592345707/5000000000 : ℝ)*X 1 2+(4204361941/10000000000 : ℝ)*X 2 0+(222767319/400000000 : ℝ)*X 2 1+(1592345707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52903441215612283903617/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19228479/25000000000000 : ℝ)*(base1) + (1615086659/100000000000000 : ℝ)*(base19) + (1499309057/100000000000000 : ℝ)*(base23) + (55046891/50000000000000 : ℝ)*(base24) + (183429283/50000000000000 : ℝ)*(upper3) + (600367014127853/100000000000000 : ℝ)*(major0) + (600367014127853/100000000000000 : ℝ)*(major1) + (600367014127853/100000000000000 : ℝ)*(major2) + (803336580729/100000000000 : ℝ)*(sp0) + (160667694437969/20000000000000 : ℝ)*(sp1) + (160667695574733/20000000000000 : ℝ)*(sp2) + (397390834909259/100000000000000 : ℝ)*(sp3) + (179173071/5000000000000 : ℝ)*(sp4) + (1404362509/50000000000000 : ℝ)*(sp7) + (397393720548193/100000000000000 : ℝ)*(f.failure) + (100417510909563/12500000000000 : ℝ)*(f.sum) + (15237278413461/40000000000000000000000000000 : ℝ)*base66 + (250414629706539/80000000000000000000000000000 : ℝ)*base67 + (228937021493461/80000000000000000000000000000 : ℝ)*base70 + (32108446773461/80000000000000000000000000000 : ℝ)*base72 + (4916144373461/40000000000000000000000000000 : ℝ)*base74 + (310098962293461/80000000000000000000000000000 : ℝ)*base76 + (180233010373461/80000000000000000000000000000 : ℝ)*base78 + (356617131493461/80000000000000000000000000000 : ℝ)*base80 + (303644702973461/40000000000000000000000000000 : ℝ)*base82 + (713721/250000000000000000000 : ℝ)*base90 + (713721/250000000000000000000 : ℝ)*base92 + (713721/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138286502726129094751653/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29695159/100000000000000 : ℝ)*(base1) + (1914683147/100000000000000 : ℝ)*(base19) + (2099813387/100000000000000 : ℝ)*(base23) + (3133167/800000000000 : ℝ)*(upper3) + (3219809/4000000000000 : ℝ)*(upper5) + (633579352358859/100000000000000 : ℝ)*(major0) + (633579352358859/100000000000000 : ℝ)*(major1) + (633579352358859/100000000000000 : ℝ)*(major2) + (858067949/20000000000000 : ℝ)*(sp1) + (144694723/3125000000000 : ℝ)*(sp2) + (847780939593063/100000000000000 : ℝ)*(sp4) + (211943676218753/25000000000000 : ℝ)*(sp5) + (847774179853381/100000000000000 : ℝ)*(sp6) + (419377534647147/100000000000000 : ℝ)*(sp7) + (209688782171153/50000000000000 : ℝ)*(f.failure) + (52986306868619/6250000000000 : ℝ)*(f.sum) + (93301199256483/40000000000000000000000000000 : ℝ)*base66 + (126038794696483/80000000000000000000000000000 : ℝ)*base68 + (448405929896483/80000000000000000000000000000 : ℝ)*base70 + (441281775896483/80000000000000000000000000000 : ℝ)*base72 + (30020756256483/40000000000000000000000000000 : ℝ)*base74 + (202475866936483/80000000000000000000000000000 : ℝ)*base76 + (343251053016483/80000000000000000000000000000 : ℝ)*base78 + (161268422456483/80000000000000000000000000000 : ℝ)*base80 + (228566846536483/40000000000000000000000000000 : ℝ)*base82 + (529159/125000000000000000000 : ℝ)*base89 + (529159/125000000000000000000 : ℝ)*base91 + (529159/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1224_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (373/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1719/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1224_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1224_s1_0 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-412968797/2000000000 : ℝ)*x 0 + (5680156191/10000000000 : ℝ)*x 1 + (5018968209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412968797/2000000000 : ℝ)^8417 ≤ (12433232847933/100000000000000 : ℝ)^6369 := by
    have hnat : (412968797 : ℕ)^8417*100000000000000^6369 ≤ 12433232847933^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412968797 2000000000 12433232847933 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5680156191/10000000000 : ℝ)^8417 ≤ (9471155516783/20000000000000 : ℝ)^6369 := by
    have hnat : (5680156191 : ℕ)^8417*20000000000000^6369 ≤ 9471155516783^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680156191 10000000000 9471155516783 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5018968209/10000000000 : ℝ)^8417 ≤ (20105494778951/50000000000000 : ℝ)^6369 := by
    have hnat : (5018968209 : ℕ)^8417*50000000000000^6369 ≤ 20105494778951^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018968209 10000000000 20105494778951 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412968797/2000000000 : ℝ), (5680156191/10000000000 : ℝ), (5018968209/10000000000 : ℝ)] ![(12433232847933/100000000000000 : ℝ), (9471155516783/20000000000000 : ℝ), (20105494778951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412968797/2000000000 : ℝ)|^8417 ≤ (12433232847933/100000000000000 : ℝ)^6369
        have hw : |(-412968797/2000000000 : ℝ)|=(412968797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5680156191/10000000000 : ℝ)|^8417 ≤ (9471155516783/20000000000000 : ℝ)^6369
        have hw : |(5680156191/10000000000 : ℝ)|=(5680156191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5018968209/10000000000 : ℝ)|^8417 ≤ (20105494778951/50000000000000 : ℝ)^6369
        have hw : |(5018968209/10000000000 : ℝ)|=(5018968209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s1_1 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5414638991/10000000000 : ℝ)*x 0 + (-75631367/312500000 : ℝ)*x 1 + (156842757/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414638991/10000000000 : ℝ)^8417 ≤ (1778102376231/4000000000000 : ℝ)^6369 := by
    have hnat : (5414638991 : ℕ)^8417*4000000000000^6369 ≤ 1778102376231^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414638991 10000000000 1778102376231 4000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75631367/312500000 : ℝ)^8417 ≤ (15336450866381/100000000000000 : ℝ)^6369 := by
    have hnat : (75631367 : ℕ)^8417*100000000000000^6369 ≤ 15336450866381^6369*312500000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75631367 312500000 15336450866381 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156842757/312500000 : ℝ)^8417 ≤ (40210989716723/100000000000000 : ℝ)^6369 := by
    have hnat : (156842757 : ℕ)^8417*100000000000000^6369 ≤ 40210989716723^6369*312500000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156842757 312500000 40210989716723 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414638991/10000000000 : ℝ), (-75631367/312500000 : ℝ), (156842757/312500000 : ℝ)] ![(1778102376231/4000000000000 : ℝ), (15336450866381/100000000000000 : ℝ), (40210989716723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414638991/10000000000 : ℝ)|^8417 ≤ (1778102376231/4000000000000 : ℝ)^6369
        have hw : |(5414638991/10000000000 : ℝ)|=(5414638991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75631367/312500000 : ℝ)|^8417 ≤ (15336450866381/100000000000000 : ℝ)^6369
        have hw : |(-75631367/312500000 : ℝ)|=(75631367/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(156842757/312500000 : ℝ)|^8417 ≤ (40210989716723/100000000000000 : ℝ)^6369
        have hw : |(156842757/312500000 : ℝ)|=(156842757/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s1_2 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5414639011/10000000000 : ℝ)*x 0 + (2509484111/5000000000 : ℝ)*x 1 + (-2420203721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414639011/10000000000 : ℝ)^8417 ≤ (44452559622767/100000000000000 : ℝ)^6369 := by
    have hnat : (5414639011 : ℕ)^8417*100000000000000^6369 ≤ 44452559622767^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414639011 10000000000 44452559622767 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2509484111/5000000000 : ℝ)^8417 ≤ (40210989695547/100000000000000 : ℝ)^6369 := by
    have hnat : (2509484111 : ℕ)^8417*100000000000000^6369 ≤ 40210989695547^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509484111 5000000000 40210989695547 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2420203721/10000000000 : ℝ)^8417 ≤ (15336450673767/100000000000000 : ℝ)^6369 := by
    have hnat : (2420203721 : ℕ)^8417*100000000000000^6369 ≤ 15336450673767^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420203721 10000000000 15336450673767 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414639011/10000000000 : ℝ), (2509484111/5000000000 : ℝ), (-2420203721/10000000000 : ℝ)] ![(44452559622767/100000000000000 : ℝ), (40210989695547/100000000000000 : ℝ), (15336450673767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414639011/10000000000 : ℝ)|^8417 ≤ (44452559622767/100000000000000 : ℝ)^6369
        have hw : |(5414639011/10000000000 : ℝ)|=(5414639011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2509484111/5000000000 : ℝ)|^8417 ≤ (40210989695547/100000000000000 : ℝ)^6369
        have hw : |(2509484111/5000000000 : ℝ)|=(2509484111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2420203721/10000000000 : ℝ)|^8417 ≤ (15336450673767/100000000000000 : ℝ)^6369
        have hw : |(-2420203721/10000000000 : ℝ)|=(2420203721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s1_3 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1077603407/2500000000 : ℝ)*x 0 + (3692174683/10000000000 : ℝ)*x 1 + (502878137/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077603407/2500000000 : ℝ)^8417 ≤ (32884841825213/100000000000000 : ℝ)^6369 := by
    have hnat : (1077603407 : ℕ)^8417*100000000000000^6369 ≤ 32884841825213^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077603407 2500000000 32884841825213 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3692174683/10000000000 : ℝ)^8417 ≤ (2680023361529/10000000000000 : ℝ)^6369 := by
    have hnat : (3692174683 : ℕ)^8417*10000000000000^6369 ≤ 2680023361529^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3692174683 10000000000 2680023361529 10000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502878137/1000000000 : ℝ)^8417 ≤ (40314924543519/100000000000000 : ℝ)^6369 := by
    have hnat : (502878137 : ℕ)^8417*100000000000000^6369 ≤ 40314924543519^6369*1000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502878137 1000000000 40314924543519 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077603407/2500000000 : ℝ), (3692174683/10000000000 : ℝ), (502878137/1000000000 : ℝ)] ![(32884841825213/100000000000000 : ℝ), (2680023361529/10000000000000 : ℝ), (40314924543519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077603407/2500000000 : ℝ)|^8417 ≤ (32884841825213/100000000000000 : ℝ)^6369
        have hw : |(1077603407/2500000000 : ℝ)|=(1077603407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3692174683/10000000000 : ℝ)|^8417 ≤ (2680023361529/10000000000000 : ℝ)^6369
        have hw : |(3692174683/10000000000 : ℝ)|=(3692174683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502878137/1000000000 : ℝ)|^8417 ≤ (40314924543519/100000000000000 : ℝ)^6369
        have hw : |(502878137/1000000000 : ℝ)|=(502878137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s1_4 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-103276891/500000000 : ℝ)*x 0 + (5027712153/10000000000 : ℝ)*x 1 + (5671247627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103276891/500000000 : ℝ)^8417 ≤ (2487750883547/20000000000000 : ℝ)^6369 := by
    have hnat : (103276891 : ℕ)^8417*20000000000000^6369 ≤ 2487750883547^6369*500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103276891 500000000 2487750883547 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5027712153/10000000000 : ℝ)^8417 ≤ (40303596884103/100000000000000 : ℝ)^6369 := by
    have hnat : (5027712153 : ℕ)^8417*100000000000000^6369 ≤ 40303596884103^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027712153 10000000000 40303596884103 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5671247627/10000000000 : ℝ)^8417 ≤ (47257648687999/100000000000000 : ℝ)^6369 := by
    have hnat : (5671247627 : ℕ)^8417*100000000000000^6369 ≤ 47257648687999^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671247627 10000000000 47257648687999 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103276891/500000000 : ℝ), (5027712153/10000000000 : ℝ), (5671247627/10000000000 : ℝ)] ![(2487750883547/20000000000000 : ℝ), (40303596884103/100000000000000 : ℝ), (47257648687999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103276891/500000000 : ℝ)|^8417 ≤ (2487750883547/20000000000000 : ℝ)^6369
        have hw : |(-103276891/500000000 : ℝ)|=(103276891/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5027712153/10000000000 : ℝ)|^8417 ≤ (40303596884103/100000000000000 : ℝ)^6369
        have hw : |(5027712153/10000000000 : ℝ)|=(5027712153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5671247627/10000000000 : ℝ)|^8417 ≤ (47257648687999/100000000000000 : ℝ)^6369
        have hw : |(5671247627/10000000000 : ℝ)|=(5671247627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s1_5 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2622221533/5000000000 : ℝ)*x 0 + (-70717219/400000000 : ℝ)*x 1 + (28356203/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622221533/5000000000 : ℝ)^8417 ≤ (2130770123623/5000000000000 : ℝ)^6369 := by
    have hnat : (2622221533 : ℕ)^8417*5000000000000^6369 ≤ 2130770123623^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622221533 5000000000 2130770123623 5000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70717219/400000000 : ℝ)^8417 ≤ (2025405242141/20000000000000 : ℝ)^6369 := by
    have hnat : (70717219 : ℕ)^8417*20000000000000^6369 ≤ 2025405242141^6369*400000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70717219 400000000 2025405242141 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28356203/50000000 : ℝ)^8417 ≤ (47257571304307/100000000000000 : ℝ)^6369 := by
    have hnat : (28356203 : ℕ)^8417*100000000000000^6369 ≤ 47257571304307^6369*50000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28356203 50000000 47257571304307 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622221533/5000000000 : ℝ), (-70717219/400000000 : ℝ), (28356203/50000000 : ℝ)] ![(2130770123623/5000000000000 : ℝ), (2025405242141/20000000000000 : ℝ), (47257571304307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622221533/5000000000 : ℝ)|^8417 ≤ (2130770123623/5000000000000 : ℝ)^6369
        have hw : |(2622221533/5000000000 : ℝ)|=(2622221533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70717219/400000000 : ℝ)|^8417 ≤ (2025405242141/20000000000000 : ℝ)^6369
        have hw : |(-70717219/400000000 : ℝ)|=(70717219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28356203/50000000 : ℝ)|^8417 ≤ (47257571304307/100000000000000 : ℝ)^6369
        have hw : |(28356203/50000000 : ℝ)|=(28356203/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s1_6 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5244443141/10000000000 : ℝ)*x 0 + (5671241109/10000000000 : ℝ)*x 1 + (-441982407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244443141/10000000000 : ℝ)^8417 ≤ (21307701638933/50000000000000 : ℝ)^6369 := by
    have hnat : (5244443141 : ℕ)^8417*50000000000000^6369 ≤ 21307701638933^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244443141 10000000000 21307701638933 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5671241109/10000000000 : ℝ)^8417 ≤ (23628788454793/50000000000000 : ℝ)^6369 := by
    have hnat : (5671241109 : ℕ)^8417*50000000000000^6369 ≤ 23628788454793^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671241109 10000000000 23628788454793 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441982407/2500000000 : ℝ)^8417 ≤ (10127019798813/100000000000000 : ℝ)^6369 := by
    have hnat : (441982407 : ℕ)^8417*100000000000000^6369 ≤ 10127019798813^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441982407 2500000000 10127019798813 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244443141/10000000000 : ℝ), (5671241109/10000000000 : ℝ), (-441982407/2500000000 : ℝ)] ![(21307701638933/50000000000000 : ℝ), (23628788454793/50000000000000 : ℝ), (10127019798813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244443141/10000000000 : ℝ)|^8417 ≤ (21307701638933/50000000000000 : ℝ)^6369
        have hw : |(5244443141/10000000000 : ℝ)|=(5244443141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5671241109/10000000000 : ℝ)|^8417 ≤ (23628788454793/50000000000000 : ℝ)^6369
        have hw : |(5671241109/10000000000 : ℝ)|=(5671241109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441982407/2500000000 : ℝ)|^8417 ≤ (10127019798813/100000000000000 : ℝ)^6369
        have hw : |(-441982407/2500000000 : ℝ)|=(441982407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s1_7 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2155911783/5000000000 : ℝ)*x 0 + (5011098537/10000000000 : ℝ)*x 1 + (3710197357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155911783/5000000000 : ℝ)^8417 ≤ (16449529048891/50000000000000 : ℝ)^6369 := by
    have hnat : (2155911783 : ℕ)^8417*50000000000000^6369 ≤ 16449529048891^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155911783 5000000000 16449529048891 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5011098537/10000000000 : ℝ)^8417 ≤ (40127686011939/100000000000000 : ℝ)^6369 := by
    have hnat : (5011098537 : ℕ)^8417*100000000000000^6369 ≤ 40127686011939^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011098537 10000000000 40127686011939 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3710197357/10000000000 : ℝ)^8417 ≤ (26973255873451/100000000000000 : ℝ)^6369 := by
    have hnat : (3710197357 : ℕ)^8417*100000000000000^6369 ≤ 26973255873451^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3710197357 10000000000 26973255873451 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155911783/5000000000 : ℝ), (5011098537/10000000000 : ℝ), (3710197357/10000000000 : ℝ)] ![(16449529048891/50000000000000 : ℝ), (40127686011939/100000000000000 : ℝ), (26973255873451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155911783/5000000000 : ℝ)|^8417 ≤ (16449529048891/50000000000000 : ℝ)^6369
        have hw : |(2155911783/5000000000 : ℝ)|=(2155911783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5011098537/10000000000 : ℝ)|^8417 ≤ (40127686011939/100000000000000 : ℝ)^6369
        have hw : |(5011098537/10000000000 : ℝ)|=(5011098537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3710197357/10000000000 : ℝ)|^8417 ≤ (26973255873451/100000000000000 : ℝ)^6369
        have hw : |(3710197357/10000000000 : ℝ)|=(3710197357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1224_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1719/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (381/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5019/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1719/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (373/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1719/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (373/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1719/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (373/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1719/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (373/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1719/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (373/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1719/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (373/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (373/50000 : ℝ) ^ (263/64 : ℝ) ≤ (181253382143/100000000000000000000 : ℝ) := by
    have hpowers : (373/50000 : ℝ)^263 ≤ (181253382143/100000000000000000000 : ℝ)^64 := by
      have hnat : (373 : ℕ)^263*100000000000000000000^64 ≤ 181253382143^64*50000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        373 50000 181253382143 100000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (373/50000 : ℝ)) (X := (181253382143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hpowhi : (1719/6250 : ℝ) ^ (263/64 : ℝ) ≤ (496898126727385279/100000000000000000000 : ℝ) := by
    have hpowers : (1719/6250 : ℝ)^263 ≤ (496898126727385279/100000000000000000000 : ℝ)^64 := by
      have hnat : (1719 : ℕ)^263*100000000000000000000^64 ≤ 496898126727385279^64*6250^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1719 6250 496898126727385279 100000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1719/6250 : ℝ)) (X := (496898126727385279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000181253382143/50000000000000000000 : ℝ) ≤ (5000000004410729/5000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (50000000181253382143/50000000000000000000 : ℝ)^64 ≤ (5000000004410729/5000000000000000 : ℝ)^263 := by
      have hnat : (50000000181253382143 : ℕ)^64*5000000000000000^263 ≤ 5000000004410729^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000181253382143 50000000000000000000 5000000004410729 5000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000004410729/5000000000000000 : ℝ)) (X := (50000000181253382143/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50248449153990383711/50000000000000000000 : ℝ) ≤ (10012069156435409/10000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (50248449153990383711/50000000000000000000 : ℝ)^64 ≤ (10012069156435409/10000000000000000 : ℝ)^263 := by
      have hnat : (50248449153990383711 : ℕ)^64*10000000000000000^263 ≤ 10012069156435409^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50248449153990383711 50000000000000000000 10012069156435409 10000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012069156435409/10000000000000000 : ℝ)) (X := (50248449153990383711/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50496898126727385279/50000000000000000000 : ℝ) ≤ (125301728800617/125000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (50496898126727385279/50000000000000000000 : ℝ)^64 ≤ (125301728800617/125000000000000 : ℝ)^263 := by
      have hnat : (50496898126727385279 : ℕ)^64*125000000000000^263 ≤ 125301728800617^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50496898126727385279 50000000000000000000 125301728800617 125000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125301728800617/125000000000000 : ℝ)) (X := (50496898126727385279/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(181253382143/100000000000000000000 : ℝ) ≤ ((4180656141684446223/4180937500000000000 : ℝ)+2*(12069147613951/2675800000000000 : ℝ)*(373/50000 : ℝ))^(263/64 : ℝ) := by
    rw [show (4180656141684446223/4180937500000000000 : ℝ)+2*(12069147613951/2675800000000000 : ℝ)*(373/50000 : ℝ)=(5000000004410729/5000000000000000 : ℝ) by norm_num, show 1+2*(181253382143/100000000000000000000 : ℝ)=(50000000181253382143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(496898126727385279/100000000000000000000 : ℝ)+(181253382143/100000000000000000000 : ℝ) ≤ ((4180656141684446223/4180937500000000000 : ℝ)+(12069147613951/2675800000000000 : ℝ)*((1719/6250 : ℝ)+(373/50000 : ℝ)))^(263/64 : ℝ) := by
    rw [show (4180656141684446223/4180937500000000000 : ℝ)+(12069147613951/2675800000000000 : ℝ)*((1719/6250 : ℝ)+(373/50000 : ℝ))=(10012069156435409/10000000000000000 : ℝ) by norm_num, show 1+(496898126727385279/100000000000000000000 : ℝ)+(181253382143/100000000000000000000 : ℝ)=(50248449153990383711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(496898126727385279/100000000000000000000 : ℝ) ≤ ((4180656141684446223/4180937500000000000 : ℝ)+2*(12069147613951/2675800000000000 : ℝ)*(1719/6250 : ℝ))^(263/64 : ℝ) := by
    rw [show (4180656141684446223/4180937500000000000 : ℝ)+2*(12069147613951/2675800000000000 : ℝ)*(1719/6250 : ℝ)=(125301728800617/125000000000000 : ℝ) by norm_num, show 1+2*(496898126727385279/100000000000000000000 : ℝ)=(50496898126727385279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4180656141684446223/4180937500000000000 : ℝ)*(X 1 0+X 2 0)+(12069147613951/2675800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (373/50000 : ℝ)) (hi := (1719/6250 : ℝ)) (c := (4180656141684446223/4180937500000000000 : ℝ)) (alpha := (12069147613951/2675800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4180656141684446223/4180937500000000000 : ℝ)*(X 0 1+X 2 1)+(12069147613951/2675800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (373/50000 : ℝ)) (hi := (1719/6250 : ℝ)) (c := (4180656141684446223/4180937500000000000 : ℝ)) (alpha := (12069147613951/2675800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4180656141684446223/4180937500000000000 : ℝ)*(X 0 2+X 1 2)+(12069147613951/2675800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (373/50000 : ℝ)) (hi := (1719/6250 : ℝ)) (c := (4180656141684446223/4180937500000000000 : ℝ)) (alpha := (12069147613951/2675800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-412968797/2000000000 : ℝ)*X 0 0+(5680156191/10000000000 : ℝ)*X 0 1+(5018968209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5414638991/10000000000 : ℝ)*X 1 0+(-75631367/312500000 : ℝ)*X 1 1+(156842757/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5414639011/10000000000 : ℝ)*X 2 0+(2509484111/5000000000 : ℝ)*X 2 1+(-2420203721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077603407/2500000000 : ℝ)*X 0 0+(3692174683/10000000000 : ℝ)*X 0 1+(502878137/1000000000 : ℝ)*X 0 2+(1077603407/2500000000 : ℝ)*X 1 0+(3692174683/10000000000 : ℝ)*X 1 1+(502878137/1000000000 : ℝ)*X 1 2+(1077603407/2500000000 : ℝ)*X 2 0+(3692174683/10000000000 : ℝ)*X 2 1+(502878137/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-103276891/500000000 : ℝ)*X 0 0+(5027712153/10000000000 : ℝ)*X 0 1+(5671247627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622221533/5000000000 : ℝ)*X 1 0+(-70717219/400000000 : ℝ)*X 1 1+(28356203/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5244443141/10000000000 : ℝ)*X 2 0+(5671241109/10000000000 : ℝ)*X 2 1+(-441982407/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155911783/5000000000 : ℝ)*X 0 0+(5011098537/10000000000 : ℝ)*X 0 1+(3710197357/10000000000 : ℝ)*X 0 2+(2155911783/5000000000 : ℝ)*X 1 0+(5011098537/10000000000 : ℝ)*X 1 1+(3710197357/10000000000 : ℝ)*X 1 2+(2155911783/5000000000 : ℝ)*X 2 0+(5011098537/10000000000 : ℝ)*X 2 1+(3710197357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1214181894035880802752732369/209046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33544509/50000000000000 : ℝ)*(base1) + (315990611/25000000000000 : ℝ)*(base19) + (253909787/20000000000000 : ℝ)*(base23) + (27650123/20000000000000 : ℝ)*(upper3) + (148335063/100000000000000 : ℝ)*(upper5) + (141288340833647/12500000000000 : ℝ)*(major0) + (141288340833647/12500000000000 : ℝ)*(major1) + (141288340833647/12500000000000 : ℝ)*(major2) + (756217965863209/50000000000000 : ℝ)*(sp0) + (756220825897089/50000000000000 : ℝ)*(sp1) + (756220823103843/50000000000000 : ℝ)*(sp2) + (149633346938617/20000000000000 : ℝ)*(sp3) + (3525559611/50000000000000 : ℝ)*(sp4) + (3542193621/100000000000000 : ℝ)*(sp7) + (748170343975723/100000000000000 : ℝ)*(f.failure) + (756221457878311/50000000000000 : ℝ)*(f.sum) + (57943308917433/16723750000000000000000000000 : ℝ)*base66 + (502036612916766313/104523437500000000000000000000000 : ℝ)*base68 + (135245014444360751/209046875000000000000000000000000 : ℝ)*base70 + (266584078898891313/104523437500000000000000000000000 : ℝ)*base72 + (19343382585457/4180937500000000000000000000 : ℝ)*base74 + (152212997253173251/209046875000000000000000000000000 : ℝ)*base76 + (201885353475389937/104523437500000000000000000000000 : ℝ)*base77 + (373462623536733687/104523437500000000000000000000000 : ℝ)*base79 + (153848818523007/66895000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (125869/250000000000000000000 : ℝ)*base89 + (125869/250000000000000000000 : ℝ)*base91 + (125869/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1068542808208606337775479481/104523437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (277384253/50000000000000 : ℝ)*(base19) + (15571209/781250000000 : ℝ)*(base23) + (1442511/20000000000000 : ℝ)*(lower2) + (42469603/25000000000000 : ℝ)*(lower3) + (630598963/100000000000000 : ℝ)*(lower4) + (580658077630263/50000000000000 : ℝ)*(major0) + (580658077630263/50000000000000 : ℝ)*(major1) + (580658077630263/50000000000000 : ℝ)*(major2) + (10454513923/100000000000000 : ℝ)*(sp0) + (7009076499/100000000000000 : ℝ)*(sp2) + (77696273648347/5000000000000 : ℝ)*(sp4) + (388483843178089/25000000000000 : ℝ)*(sp5) + (388481731322403/25000000000000 : ℝ)*(sp6) + (768696042273607/100000000000000 : ℝ)*(sp7) + (768696042273607/100000000000000 : ℝ)*(f.failure) + (776967963740431/50000000000000 : ℝ)*(f.sum) + (57731126754231/8361875000000000000000000000 : ℝ)*base65 + (1041200324558671423/418093750000000000000000000000000 : ℝ)*base67 + (350342248014733923/418093750000000000000000000000000 : ℝ)*base69 + (4068130513036983923/418093750000000000000000000000000 : ℝ)*base71 + (16582826562827/16723750000000000000000000000 : ℝ)*base73 + (2750397582401390173/418093750000000000000000000000000 : ℝ)*base75 + (1298706660442765173/418093750000000000000000000000000 : ℝ)*base77 + (4194882618734047327/418093750000000000000000000000000 : ℝ)*base80 + (11495388672567/66895000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1900879/250000000000000000000 : ℝ)*base90 + (1900879/250000000000000000000 : ℝ)*base92 + (1900879/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1224_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1719/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (381/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5019/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1224_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1224_s2_0 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113793631/10000000000 : ℝ)*x 0 + (5495897561/10000000000 : ℝ)*x 1 + (5172025991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113793631/10000000000 : ℝ)^8417 ≤ (6412116016533/50000000000000 : ℝ)^6369 := by
    have hnat : (2113793631 : ℕ)^8417*50000000000000^6369 ≤ 6412116016533^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113793631 10000000000 6412116016533 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5495897561/10000000000 : ℝ)^8417 ≤ (45336301645521/100000000000000 : ℝ)^6369 := by
    have hnat : (5495897561 : ℕ)^8417*100000000000000^6369 ≤ 45336301645521^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495897561 10000000000 45336301645521 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172025991/10000000000 : ℝ)^8417 ≤ (41839466301053/100000000000000 : ℝ)^6369 := by
    have hnat : (5172025991 : ℕ)^8417*100000000000000^6369 ≤ 41839466301053^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172025991 10000000000 41839466301053 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113793631/10000000000 : ℝ), (5495897561/10000000000 : ℝ), (5172025991/10000000000 : ℝ)] ![(6412116016533/50000000000000 : ℝ), (45336301645521/100000000000000 : ℝ), (41839466301053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113793631/10000000000 : ℝ)|^8417 ≤ (6412116016533/50000000000000 : ℝ)^6369
        have hw : |(-2113793631/10000000000 : ℝ)|=(2113793631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5495897561/10000000000 : ℝ)|^8417 ≤ (45336301645521/100000000000000 : ℝ)^6369
        have hw : |(5495897561/10000000000 : ℝ)|=(5495897561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172025991/10000000000 : ℝ)|^8417 ≤ (41839466301053/100000000000000 : ℝ)^6369
        have hw : |(5172025991/10000000000 : ℝ)|=(5172025991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s2_1 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342605893/2500000000 : ℝ)*x 0 + (-35650989/156250000 : ℝ)*x 1 + (2586012963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342605893/2500000000 : ℝ)^8417 ≤ (43973471212297/100000000000000 : ℝ)^6369 := by
    have hnat : (1342605893 : ℕ)^8417*100000000000000^6369 ≤ 43973471212297^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342605893 2500000000 43973471212297 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35650989/156250000 : ℝ)^8417 ≤ (14187063169467/100000000000000 : ℝ)^6369 := by
    have hnat : (35650989 : ℕ)^8417*100000000000000^6369 ≤ 14187063169467^6369*156250000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35650989 156250000 14187063169467 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586012963/5000000000 : ℝ)^8417 ≤ (41839465606149/100000000000000 : ℝ)^6369 := by
    have hnat : (2586012963 : ℕ)^8417*100000000000000^6369 ≤ 41839465606149^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586012963 5000000000 41839465606149 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342605893/2500000000 : ℝ), (-35650989/156250000 : ℝ), (2586012963/5000000000 : ℝ)] ![(43973471212297/100000000000000 : ℝ), (14187063169467/100000000000000 : ℝ), (41839465606149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342605893/2500000000 : ℝ)|^8417 ≤ (43973471212297/100000000000000 : ℝ)^6369
        have hw : |(1342605893/2500000000 : ℝ)|=(1342605893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35650989/156250000 : ℝ)|^8417 ≤ (14187063169467/100000000000000 : ℝ)^6369
        have hw : |(-35650989/156250000 : ℝ)|=(35650989/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2586012963/5000000000 : ℝ)|^8417 ≤ (41839465606149/100000000000000 : ℝ)^6369
        have hw : |(2586012963/5000000000 : ℝ)|=(2586012963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s2_2 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685211689/5000000000 : ℝ)*x 0 + (2586013049/5000000000 : ℝ)*x 1 + (-71301979/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685211689/5000000000 : ℝ)^8417 ≤ (43973469113019/100000000000000 : ℝ)^6369 := by
    have hnat : (2685211689 : ℕ)^8417*100000000000000^6369 ≤ 43973469113019^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685211689 5000000000 43973469113019 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586013049/5000000000 : ℝ)^8417 ≤ (10459866861243/25000000000000 : ℝ)^6369 := by
    have hnat : (2586013049 : ℕ)^8417*25000000000000^6369 ≤ 10459866861243^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586013049 5000000000 10459866861243 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71301979/312500000 : ℝ)^8417 ≤ (14187063432419/100000000000000 : ℝ)^6369 := by
    have hnat : (71301979 : ℕ)^8417*100000000000000^6369 ≤ 14187063432419^6369*312500000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71301979 312500000 14187063432419 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685211689/5000000000 : ℝ), (2586013049/5000000000 : ℝ), (-71301979/312500000 : ℝ)] ![(43973469113019/100000000000000 : ℝ), (10459866861243/25000000000000 : ℝ), (14187063432419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685211689/5000000000 : ℝ)|^8417 ≤ (43973469113019/100000000000000 : ℝ)^6369
        have hw : |(2685211689/5000000000 : ℝ)|=(2685211689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586013049/5000000000 : ℝ)|^8417 ≤ (10459866861243/25000000000000 : ℝ)^6369
        have hw : |(2586013049/5000000000 : ℝ)|=(2586013049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71301979/312500000 : ℝ)|^8417 ≤ (14187063432419/100000000000000 : ℝ)^6369
        have hw : |(-71301979/312500000 : ℝ)|=(71301979/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s2_3 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086046557/2500000000 : ℝ)*x 0 + (1007206129/2500000000 : ℝ)*x 1 + (4683538413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086046557/2500000000 : ℝ)^8417 ≤ (33225778063571/100000000000000 : ℝ)^6369 := by
    have hnat : (1086046557 : ℕ)^8417*100000000000000^6369 ≤ 33225778063571^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086046557 2500000000 33225778063571 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007206129/2500000000 : ℝ)^8417 ≤ (3759503420879/12500000000000 : ℝ)^6369 := by
    have hnat : (1007206129 : ℕ)^8417*12500000000000^6369 ≤ 3759503420879^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007206129 2500000000 3759503420879 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4683538413/10000000000 : ℝ)^8417 ≤ (36698194555819/100000000000000 : ℝ)^6369 := by
    have hnat : (4683538413 : ℕ)^8417*100000000000000^6369 ≤ 36698194555819^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4683538413 10000000000 36698194555819 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086046557/2500000000 : ℝ), (1007206129/2500000000 : ℝ), (4683538413/10000000000 : ℝ)] ![(33225778063571/100000000000000 : ℝ), (3759503420879/12500000000000 : ℝ), (36698194555819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086046557/2500000000 : ℝ)|^8417 ≤ (33225778063571/100000000000000 : ℝ)^6369
        have hw : |(1086046557/2500000000 : ℝ)|=(1086046557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007206129/2500000000 : ℝ)|^8417 ≤ (3759503420879/12500000000000 : ℝ)^6369
        have hw : |(1007206129/2500000000 : ℝ)|=(1007206129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4683538413/10000000000 : ℝ)|^8417 ≤ (36698194555819/100000000000000 : ℝ)^6369
        have hw : |(4683538413/10000000000 : ℝ)|=(4683538413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s2_4 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113875897/10000000000 : ℝ)*x 0 + (1293533573/2500000000 : ℝ)*x 1 + (1098753853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113875897/10000000000 : ℝ)^8417 ≤ (1603111453623/12500000000000 : ℝ)^6369 := by
    have hnat : (2113875897 : ℕ)^8417*12500000000000^6369 ≤ 1603111453623^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113875897 10000000000 1603111453623 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293533573/2500000000 : ℝ)^8417 ≤ (41862007270491/100000000000000 : ℝ)^6369 := by
    have hnat : (1293533573 : ℕ)^8417*100000000000000^6369 ≤ 41862007270491^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293533573 2500000000 41862007270491 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098753853/2000000000 : ℝ)^8417 ≤ (22656550541261/50000000000000 : ℝ)^6369 := by
    have hnat : (1098753853 : ℕ)^8417*50000000000000^6369 ≤ 22656550541261^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098753853 2000000000 22656550541261 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113875897/10000000000 : ℝ), (1293533573/2500000000 : ℝ), (1098753853/2000000000 : ℝ)] ![(1603111453623/12500000000000 : ℝ), (41862007270491/100000000000000 : ℝ), (22656550541261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113875897/10000000000 : ℝ)|^8417 ≤ (1603111453623/12500000000000 : ℝ)^6369
        have hw : |(-2113875897/10000000000 : ℝ)|=(2113875897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293533573/2500000000 : ℝ)|^8417 ≤ (41862007270491/100000000000000 : ℝ)^6369
        have hw : |(1293533573/2500000000 : ℝ)|=(1293533573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098753853/2000000000 : ℝ)|^8417 ≤ (22656550541261/50000000000000 : ℝ)^6369
        have hw : |(1098753853/2000000000 : ℝ)|=(1098753853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s2_5 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287808491/10000000000 : ℝ)*x 0 + (-1959919789/10000000000 : ℝ)*x 1 + (2746884651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287808491/10000000000 : ℝ)^8417 ≤ (43081710423541/100000000000000 : ℝ)^6369 := by
    have hnat : (5287808491 : ℕ)^8417*100000000000000^6369 ≤ 43081710423541^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287808491 10000000000 43081710423541 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1959919789/10000000000 : ℝ)^8417 ≤ (11605188073781/100000000000000 : ℝ)^6369 := by
    have hnat : (1959919789 : ℕ)^8417*100000000000000^6369 ≤ 11605188073781^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959919789 10000000000 11605188073781 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746884651/5000000000 : ℝ)^8417 ≤ (22656550742917/50000000000000 : ℝ)^6369 := by
    have hnat : (2746884651 : ℕ)^8417*50000000000000^6369 ≤ 22656550742917^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746884651 5000000000 22656550742917 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287808491/10000000000 : ℝ), (-1959919789/10000000000 : ℝ), (2746884651/5000000000 : ℝ)] ![(43081710423541/100000000000000 : ℝ), (11605188073781/100000000000000 : ℝ), (22656550742917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287808491/10000000000 : ℝ)|^8417 ≤ (43081710423541/100000000000000 : ℝ)^6369
        have hw : |(5287808491/10000000000 : ℝ)|=(5287808491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1959919789/10000000000 : ℝ)|^8417 ≤ (11605188073781/100000000000000 : ℝ)^6369
        have hw : |(-1959919789/10000000000 : ℝ)|=(1959919789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746884651/5000000000 : ℝ)|^8417 ≤ (22656550742917/50000000000000 : ℝ)^6369
        have hw : |(2746884651/5000000000 : ℝ)|=(2746884651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s2_6 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165244021/312500000 : ℝ)*x 0 + (2746884677/5000000000 : ℝ)*x 1 + (-489979867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165244021/312500000 : ℝ)^8417 ≤ (43081712372407/100000000000000 : ℝ)^6369 := by
    have hnat : (165244021 : ℕ)^8417*100000000000000^6369 ≤ 43081712372407^6369*312500000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165244021 312500000 43081712372407 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746884677/5000000000 : ℝ)^8417 ≤ (906262041053/2000000000000 : ℝ)^6369 := by
    have hnat : (2746884677 : ℕ)^8417*2000000000000^6369 ≤ 906262041053^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746884677 5000000000 906262041053 2000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (489979867/2500000000 : ℝ)^8417 ≤ (5802592780933/50000000000000 : ℝ)^6369 := by
    have hnat : (489979867 : ℕ)^8417*50000000000000^6369 ≤ 5802592780933^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489979867 2500000000 5802592780933 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165244021/312500000 : ℝ), (2746884677/5000000000 : ℝ), (-489979867/2500000000 : ℝ)] ![(43081712372407/100000000000000 : ℝ), (906262041053/2000000000000 : ℝ), (5802592780933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165244021/312500000 : ℝ)|^8417 ≤ (43081712372407/100000000000000 : ℝ)^6369
        have hw : |(165244021/312500000 : ℝ)|=(165244021/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746884677/5000000000 : ℝ)|^8417 ≤ (906262041053/2000000000000 : ℝ)^6369
        have hw : |(2746884677/5000000000 : ℝ)|=(2746884677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-489979867/2500000000 : ℝ)|^8417 ≤ (5802592780933/50000000000000 : ℝ)^6369
        have hw : |(-489979867/2500000000 : ℝ)|=(489979867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s2_7 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086087999/2500000000 : ℝ)*x 0 + (4679276569/10000000000 : ℝ)*x 1 + (2016563283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086087999/2500000000 : ℝ)^8417 ≤ (830686340221/2500000000000 : ℝ)^6369 := by
    have hnat : (1086087999 : ℕ)^8417*2500000000000^6369 ≤ 830686340221^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086087999 2500000000 830686340221 2500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4679276569/10000000000 : ℝ)^8417 ≤ (18327034474893/50000000000000 : ℝ)^6369 := by
    have hnat : (4679276569 : ℕ)^8417*50000000000000^6369 ≤ 18327034474893^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4679276569 10000000000 18327034474893 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016563283/5000000000 : ℝ)^8417 ≤ (15059238707649/50000000000000 : ℝ)^6369 := by
    have hnat : (2016563283 : ℕ)^8417*50000000000000^6369 ≤ 15059238707649^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016563283 5000000000 15059238707649 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086087999/2500000000 : ℝ), (4679276569/10000000000 : ℝ), (2016563283/5000000000 : ℝ)] ![(830686340221/2500000000000 : ℝ), (18327034474893/50000000000000 : ℝ), (15059238707649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086087999/2500000000 : ℝ)|^8417 ≤ (830686340221/2500000000000 : ℝ)^6369
        have hw : |(1086087999/2500000000 : ℝ)|=(1086087999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4679276569/10000000000 : ℝ)|^8417 ≤ (18327034474893/50000000000000 : ℝ)^6369
        have hw : |(4679276569/10000000000 : ℝ)|=(4679276569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016563283/5000000000 : ℝ)|^8417 ≤ (15059238707649/50000000000000 : ℝ)^6369
        have hw : |(2016563283/5000000000 : ℝ)|=(2016563283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1224_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5019/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (381/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (377/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16271/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5019/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (381/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5019/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (381/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5019/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (381/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5019/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (381/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5019/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (381/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5019/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (381/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (381/6250 : ℝ) ^ (263/64 : ℝ) ≤ (1016937179721873/100000000000000000000 : ℝ) := by
    have hpowers : (381/6250 : ℝ)^263 ≤ (1016937179721873/100000000000000000000 : ℝ)^64 := by
      have hnat : (381 : ℕ)^263*100000000000000000000^64 ≤ 1016937179721873^64*6250^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        381 6250 1016937179721873 100000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (381/6250 : ℝ)) (X := (1016937179721873/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hpowhi : (5019/25000 : ℝ) ^ (263/64 : ℝ) ≤ (1090257423298157/800000000000000000 : ℝ) := by
    have hpowers : (5019/25000 : ℝ)^263 ≤ (1090257423298157/800000000000000000 : ℝ)^64 := by
      have hnat : (5019 : ℕ)^263*800000000000000000^64 ≤ 1090257423298157^64*25000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5019 25000 1090257423298157 800000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5019/25000 : ℝ)) (X := (1090257423298157/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001016937179721873/50000000000000000000 : ℝ) ≤ (10000049493139701/10000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (50001016937179721873/50000000000000000000 : ℝ)^64 ≤ (10000049493139701/10000000000000000 : ℝ)^263 := by
      have hnat : (50001016937179721873 : ℕ)^64*10000000000000000^263 ≤ 10000049493139701^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001016937179721873 50000000000000000000 10000049493139701 10000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000049493139701/10000000000000000 : ℝ)) (X := (50001016937179721873/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50068649557545995749/50000000000000000000 : ℝ) ≤ (10003339385034829/10000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (50068649557545995749/50000000000000000000 : ℝ)^64 ≤ (10003339385034829/10000000000000000 : ℝ)^263 := by
      have hnat : (50068649557545995749 : ℕ)^64*10000000000000000^263 ≤ 10003339385034829^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50068649557545995749 50000000000000000000 10003339385034829 10000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003339385034829/10000000000000000 : ℝ)) (X := (50068649557545995749/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (401090257423298157/400000000000000000 : ℝ) ≤ (10006629276929957/10000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (401090257423298157/400000000000000000 : ℝ)^64 ≤ (10006629276929957/10000000000000000 : ℝ)^263 := by
      have hnat : (401090257423298157 : ℕ)^64*10000000000000000^263 ≤ 10006629276929957^263*400000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        401090257423298157 400000000000000000 10006629276929957 10000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006629276929957/10000000000000000 : ℝ)) (X := (401090257423298157/400000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1016937179721873/100000000000000000000 : ℝ) ≤ ((11646715129342301617/11650000000000000000 : ℝ)+2*(411236486891/174750000000000 : ℝ)*(381/6250 : ℝ))^(263/64 : ℝ) := by
    rw [show (11646715129342301617/11650000000000000000 : ℝ)+2*(411236486891/174750000000000 : ℝ)*(381/6250 : ℝ)=(10000049493139701/10000000000000000 : ℝ) by norm_num, show 1+2*(1016937179721873/100000000000000000000 : ℝ)=(50001016937179721873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1090257423298157/800000000000000000 : ℝ)+(1016937179721873/100000000000000000000 : ℝ) ≤ ((11646715129342301617/11650000000000000000 : ℝ)+(411236486891/174750000000000 : ℝ)*((5019/25000 : ℝ)+(381/6250 : ℝ)))^(263/64 : ℝ) := by
    rw [show (11646715129342301617/11650000000000000000 : ℝ)+(411236486891/174750000000000 : ℝ)*((5019/25000 : ℝ)+(381/6250 : ℝ))=(10003339385034829/10000000000000000 : ℝ) by norm_num, show 1+(1090257423298157/800000000000000000 : ℝ)+(1016937179721873/100000000000000000000 : ℝ)=(50068649557545995749/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1090257423298157/800000000000000000 : ℝ) ≤ ((11646715129342301617/11650000000000000000 : ℝ)+2*(411236486891/174750000000000 : ℝ)*(5019/25000 : ℝ))^(263/64 : ℝ) := by
    rw [show (11646715129342301617/11650000000000000000 : ℝ)+2*(411236486891/174750000000000 : ℝ)*(5019/25000 : ℝ)=(10006629276929957/10000000000000000 : ℝ) by norm_num, show 1+2*(1090257423298157/800000000000000000 : ℝ)=(401090257423298157/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11646715129342301617/11650000000000000000 : ℝ)*(X 1 0+X 2 0)+(411236486891/174750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (381/6250 : ℝ)) (hi := (5019/25000 : ℝ)) (c := (11646715129342301617/11650000000000000000 : ℝ)) (alpha := (411236486891/174750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11646715129342301617/11650000000000000000 : ℝ)*(X 0 1+X 2 1)+(411236486891/174750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (381/6250 : ℝ)) (hi := (5019/25000 : ℝ)) (c := (11646715129342301617/11650000000000000000 : ℝ)) (alpha := (411236486891/174750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11646715129342301617/11650000000000000000 : ℝ)*(X 0 2+X 1 2)+(411236486891/174750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (381/6250 : ℝ)) (hi := (5019/25000 : ℝ)) (c := (11646715129342301617/11650000000000000000 : ℝ)) (alpha := (411236486891/174750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2113793631/10000000000 : ℝ)*X 0 0+(5495897561/10000000000 : ℝ)*X 0 1+(5172025991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1342605893/2500000000 : ℝ)*X 1 0+(-35650989/156250000 : ℝ)*X 1 1+(2586012963/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685211689/5000000000 : ℝ)*X 2 0+(2586013049/5000000000 : ℝ)*X 2 1+(-71301979/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086046557/2500000000 : ℝ)*X 0 0+(1007206129/2500000000 : ℝ)*X 0 1+(4683538413/10000000000 : ℝ)*X 0 2+(1086046557/2500000000 : ℝ)*X 1 0+(1007206129/2500000000 : ℝ)*X 1 1+(4683538413/10000000000 : ℝ)*X 1 2+(1086046557/2500000000 : ℝ)*X 2 0+(1007206129/2500000000 : ℝ)*X 2 1+(4683538413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2113875897/10000000000 : ℝ)*X 0 0+(1293533573/2500000000 : ℝ)*X 0 1+(1098753853/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287808491/10000000000 : ℝ)*X 1 0+(-1959919789/10000000000 : ℝ)*X 1 1+(2746884651/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165244021/312500000 : ℝ)*X 2 0+(2746884677/5000000000 : ℝ)*X 2 1+(-489979867/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1086087999/2500000000 : ℝ)*X 0 0+(4679276569/10000000000 : ℝ)*X 0 1+(2016563283/5000000000 : ℝ)*X 0 2+(1086087999/2500000000 : ℝ)*X 1 0+(4679276569/10000000000 : ℝ)*X 1 1+(2016563283/5000000000 : ℝ)*X 1 2+(1086087999/2500000000 : ℝ)*X 2 0+(4679276569/10000000000 : ℝ)*X 2 1+(2016563283/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49366495939701438236079/5825000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85733521/5000000000000 : ℝ)*(base19) + (370689461/25000000000000 : ℝ)*(base23) + (64645919/100000000000000 : ℝ)*(lower2) + (16777137/6250000000000 : ℝ)*(upper3) + (15144109/12500000000000 : ℝ)*(upper5) + (1153770819362739/50000000000000 : ℝ)*(major0) + (1153770819362739/50000000000000 : ℝ)*(major1) + (1153770819362739/50000000000000 : ℝ)*(major2) + (3087662934502051/100000000000000 : ℝ)*(sp0) + (771919495677403/25000000000000 : ℝ)*(sp1) + (771919553655547/25000000000000 : ℝ)*(sp2) + (381848324111381/25000000000000 : ℝ)*(sp3) + (16762877981/100000000000000 : ℝ)*(sp4) + (5000563783/50000000000000 : ℝ)*(sp7) + (152740329757309/10000000000000 : ℝ)*(f.failure) + (48244995271563/1562500000000 : ℝ)*(f.sum) + (2398481950909/2912500000000000000000000000 : ℝ)*base66 + (2055841967433348963/582500000000000000000000000000000 : ℝ)*base67 + (3032414230339151037/582500000000000000000000000000000 : ℝ)*base70 + (1328861524174151037/582500000000000000000000000000000 : ℝ)*base72 + (11525999344991/2912500000000000000000000000 : ℝ)*base73 + (3016534182165848963/582500000000000000000000000000000 : ℝ)*base75 + (2002777326674151037/582500000000000000000000000000000 : ℝ)*base78 + (540386457150848963/582500000000000000000000000000000 : ℝ)*base79 + (1271860862533/1456250000000000000000000000 : ℝ)*base81 + (134027/25000000000000000000 : ℝ)*base89 + (134027/25000000000000000000 : ℝ)*base91 + (134027/25000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (190173453257138336771938281/29125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (838743247/50000000000000 : ℝ)*(base19) + (1929746677/100000000000000 : ℝ)*(base23) + (31752651/100000000000000 : ℝ)*(upper2) + (1135557/500000000000 : ℝ)*(upper3) + (6528609/5000000000000 : ℝ)*(upper5) + (233809837852069/10000000000000 : ℝ)*(major0) + (233809837852069/10000000000000 : ℝ)*(major1) + (233809837852069/10000000000000 : ℝ)*(major2) + (524853863/3125000000000 : ℝ)*(sp1) + (11121831877/50000000000000 : ℝ)*(sp2) + (1564283593185679/50000000000000 : ℝ)*(sp4) + (97767147298789/3125000000000 : ℝ)*(sp5) + (1564271506480463/50000000000000 : ℝ)*(sp6) + (309525870603599/20000000000000 : ℝ)*(sp7) + (309525870603599/20000000000000 : ℝ)*(f.failure) + (1564283593185679/50000000000000 : ℝ)*(f.sum) + (2568501165193/1747500000000000000000000000 : ℝ)*base65 + (2105180196432213281/349500000000000000000000000000000 : ℝ)*base68 + (1503896831092286719/349500000000000000000000000000000 : ℝ)*base69 + (399290163142286719/349500000000000000000000000000000 : ℝ)*base71 + (19733816983849/3495000000000000000000000000 : ℝ)*base74 + (1708506209113286719/349500000000000000000000000000000 : ℝ)*base75 + (750482384824286719/349500000000000000000000000000000 : ℝ)*base77 + (4043047250147786719/349500000000000000000000000000000 : ℝ)*base79 + (2183309183683/1747500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (126103/50000000000000000000 : ℝ)*base90 + (126103/50000000000000000000 : ℝ)*base92 + (126103/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1224_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5019/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (381/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (377/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1224_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1224_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (377/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1224_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1224_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1224_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (377/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1224_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
