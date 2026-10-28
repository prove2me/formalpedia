-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1070_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:10:04.591847+00:00
-- url     : https://prove2.me/submissions/2b5fd8fe-9b90-4983-9023-223185d68fac

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
theorem support_rectangle_w1070_s6_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201751607/10000000000 : ℝ)*x 0 + (5394836021/10000000000 : ℝ)*x 1 + (5264009301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201751607/10000000000 : ℝ)^8263 ≤ (6685960906811/50000000000000 : ℝ)^6215 := by
    have hnat : (2201751607 : ℕ)^8263*50000000000000^6215 ≤ 6685960906811^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201751607 10000000000 6685960906811 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394836021/10000000000 : ℝ)^8263 ≤ (44020836339047/100000000000000 : ℝ)^6215 := by
    have hnat : (5394836021 : ℕ)^8263*100000000000000^6215 ≤ 44020836339047^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394836021 10000000000 44020836339047 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264009301/10000000000 : ℝ)^8263 ≤ (21303620912081/50000000000000 : ℝ)^6215 := by
    have hnat : (5264009301 : ℕ)^8263*50000000000000^6215 ≤ 21303620912081^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264009301 10000000000 21303620912081 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201751607/10000000000 : ℝ), (5394836021/10000000000 : ℝ), (5264009301/10000000000 : ℝ)] ![(6685960906811/50000000000000 : ℝ), (44020836339047/100000000000000 : ℝ), (21303620912081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201751607/10000000000 : ℝ)|^8263 ≤ (6685960906811/50000000000000 : ℝ)^6215
        have hw : |(-2201751607/10000000000 : ℝ)|=(2201751607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394836021/10000000000 : ℝ)|^8263 ≤ (44020836339047/100000000000000 : ℝ)^6215
        have hw : |(5394836021/10000000000 : ℝ)|=(5394836021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264009301/10000000000 : ℝ)|^8263 ≤ (21303620912081/50000000000000 : ℝ)^6215
        have hw : |(5264009301/10000000000 : ℝ)|=(5264009301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s6_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672553647/5000000000 : ℝ)*x 0 + (-283516913/1250000000 : ℝ)*x 1 + (5264009439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672553647/5000000000 : ℝ)^8263 ≤ (43482166638589/100000000000000 : ℝ)^6215 := by
    have hnat : (2672553647 : ℕ)^8263*100000000000000^6215 ≤ 43482166638589^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672553647 5000000000 43482166638589 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283516913/1250000000 : ℝ)^8263 ≤ (6955295021491/50000000000000 : ℝ)^6215 := by
    have hnat : (283516913 : ℕ)^8263*50000000000000^6215 ≤ 6955295021491^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283516913 1250000000 6955295021491 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264009439/10000000000 : ℝ)^8263 ≤ (1331476353413/3125000000000 : ℝ)^6215 := by
    have hnat : (5264009439 : ℕ)^8263*3125000000000^6215 ≤ 1331476353413^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264009439 10000000000 1331476353413 3125000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672553647/5000000000 : ℝ), (-283516913/1250000000 : ℝ), (5264009439/10000000000 : ℝ)] ![(43482166638589/100000000000000 : ℝ), (6955295021491/50000000000000 : ℝ), (1331476353413/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672553647/5000000000 : ℝ)|^8263 ≤ (43482166638589/100000000000000 : ℝ)^6215
        have hw : |(2672553647/5000000000 : ℝ)|=(2672553647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-283516913/1250000000 : ℝ)|^8263 ≤ (6955295021491/50000000000000 : ℝ)^6215
        have hw : |(-283516913/1250000000 : ℝ)|=(283516913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264009439/10000000000 : ℝ)|^8263 ≤ (1331476353413/3125000000000 : ℝ)^6215
        have hw : |(5264009439/10000000000 : ℝ)|=(5264009439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s6_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069021349/2000000000 : ℝ)*x 0 + (5264009743/10000000000 : ℝ)*x 1 + (-226813563/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069021349/2000000000 : ℝ)^8263 ≤ (8696432140163/20000000000000 : ℝ)^6215 := by
    have hnat : (1069021349 : ℕ)^8263*20000000000000^6215 ≤ 8696432140163^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069021349 2000000000 8696432140163 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264009743/10000000000 : ℝ)^8263 ≤ (21303623290321/50000000000000 : ℝ)^6215 := by
    have hnat : (5264009743 : ℕ)^8263*50000000000000^6215 ≤ 21303623290321^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264009743 10000000000 21303623290321 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226813563/1000000000 : ℝ)^8263 ≤ (13910592701201/100000000000000 : ℝ)^6215 := by
    have hnat : (226813563 : ℕ)^8263*100000000000000^6215 ≤ 13910592701201^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226813563 1000000000 13910592701201 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069021349/2000000000 : ℝ), (5264009743/10000000000 : ℝ), (-226813563/1000000000 : ℝ)] ![(8696432140163/20000000000000 : ℝ), (21303623290321/50000000000000 : ℝ), (13910592701201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069021349/2000000000 : ℝ)|^8263 ≤ (8696432140163/20000000000000 : ℝ)^6215
        have hw : |(1069021349/2000000000 : ℝ)|=(1069021349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264009743/10000000000 : ℝ)|^8263 ≤ (21303623290321/50000000000000 : ℝ)^6215
        have hw : |(5264009743/10000000000 : ℝ)|=(5264009743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226813563/1000000000 : ℝ)|^8263 ≤ (13910592701201/100000000000000 : ℝ)^6215
        have hw : |(-226813563/1000000000 : ℝ)|=(226813563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s6_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874978001/2000000000 : ℝ)*x 0 + (1062122791/2500000000 : ℝ)*x 1 + (2252548557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874978001/2000000000 : ℝ)^8263 ≤ (666325919801/2000000000000 : ℝ)^6215 := by
    have hnat : (874978001 : ℕ)^8263*2000000000000^6215 ≤ 666325919801^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874978001 2000000000 666325919801 2000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062122791/2500000000 : ℝ)^8263 ≤ (32042665648013/100000000000000 : ℝ)^6215 := by
    have hnat : (1062122791 : ℕ)^8263*100000000000000^6215 ≤ 32042665648013^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062122791 2500000000 32042665648013 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252548557/5000000000 : ℝ)^8263 ≤ (1732051917367/5000000000000 : ℝ)^6215 := by
    have hnat : (2252548557 : ℕ)^8263*5000000000000^6215 ≤ 1732051917367^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252548557 5000000000 1732051917367 5000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874978001/2000000000 : ℝ), (1062122791/2500000000 : ℝ), (2252548557/5000000000 : ℝ)] ![(666325919801/2000000000000 : ℝ), (32042665648013/100000000000000 : ℝ), (1732051917367/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874978001/2000000000 : ℝ)|^8263 ≤ (666325919801/2000000000000 : ℝ)^6215
        have hw : |(874978001/2000000000 : ℝ)|=(874978001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062122791/2500000000 : ℝ)|^8263 ≤ (32042665648013/100000000000000 : ℝ)^6215
        have hw : |(1062122791/2500000000 : ℝ)|=(1062122791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252548557/5000000000 : ℝ)|^8263 ≤ (1732051917367/5000000000000 : ℝ)^6215
        have hw : |(2252548557/5000000000 : ℝ)|=(2252548557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s6_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201756757/10000000000 : ℝ)*x 0 + (131608497/250000000 : ℝ)*x 1 + (2697252133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201756757/10000000000 : ℝ)^8263 ≤ (6685981698967/50000000000000 : ℝ)^6215 := by
    have hnat : (2201756757 : ℕ)^8263*50000000000000^6215 ≤ 6685981698967^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201756757 10000000000 6685981698967 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131608497/250000000 : ℝ)^8263 ≤ (42610799309739/100000000000000 : ℝ)^6215 := by
    have hnat : (131608497 : ℕ)^8263*100000000000000^6215 ≤ 42610799309739^6215*250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131608497 250000000 42610799309739 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697252133/5000000000 : ℝ)^8263 ≤ (22008618636829/50000000000000 : ℝ)^6215 := by
    have hnat : (2697252133 : ℕ)^8263*50000000000000^6215 ≤ 22008618636829^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697252133 5000000000 22008618636829 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201756757/10000000000 : ℝ), (131608497/250000000 : ℝ), (2697252133/5000000000 : ℝ)] ![(6685981698967/50000000000000 : ℝ), (42610799309739/100000000000000 : ℝ), (22008618636829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201756757/10000000000 : ℝ)|^8263 ≤ (6685981698967/50000000000000 : ℝ)^6215
        have hw : |(-2201756757/10000000000 : ℝ)|=(2201756757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131608497/250000000 : ℝ)|^8263 ≤ (42610799309739/100000000000000 : ℝ)^6215
        have hw : |(131608497/250000000 : ℝ)|=(131608497/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697252133/5000000000 : ℝ)|^8263 ≤ (22008618636829/50000000000000 : ℝ)^6215
        have hw : |(2697252133/5000000000 : ℝ)|=(2697252133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s6_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42497153/80000000 : ℝ)*x 0 + (-10688203/50000000 : ℝ)*x 1 + (539450433/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42497153/80000000 : ℝ)^8263 ≤ (43126012324453/100000000000000 : ℝ)^6215 := by
    have hnat : (42497153 : ℕ)^8263*100000000000000^6215 ≤ 43126012324453^6215*80000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42497153 80000000 43126012324453 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10688203/50000000 : ℝ)^8263 ≤ (12856749694739/100000000000000 : ℝ)^6215 := by
    have hnat : (10688203 : ℕ)^8263*100000000000000^6215 ≤ 12856749694739^6215*50000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10688203 50000000 12856749694739 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539450433/1000000000 : ℝ)^8263 ≤ (44017237967959/100000000000000 : ℝ)^6215 := by
    have hnat : (539450433 : ℕ)^8263*100000000000000^6215 ≤ 44017237967959^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539450433 1000000000 44017237967959 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42497153/80000000 : ℝ), (-10688203/50000000 : ℝ), (539450433/1000000000 : ℝ)] ![(43126012324453/100000000000000 : ℝ), (12856749694739/100000000000000 : ℝ), (44017237967959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42497153/80000000 : ℝ)|^8263 ≤ (43126012324453/100000000000000 : ℝ)^6215
        have hw : |(42497153/80000000 : ℝ)|=(42497153/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10688203/50000000 : ℝ)|^8263 ≤ (12856749694739/100000000000000 : ℝ)^6215
        have hw : |(-10688203/50000000 : ℝ)|=(10688203/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539450433/1000000000 : ℝ)|^8263 ≤ (44017237967959/100000000000000 : ℝ)^6215
        have hw : |(539450433/1000000000 : ℝ)|=(539450433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s6_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656071917/5000000000 : ℝ)*x 0 + (5268071/9765625 : ℝ)*x 1 + (-427528097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656071917/5000000000 : ℝ)^8263 ≤ (43126009183517/100000000000000 : ℝ)^6215 := by
    have hnat : (2656071917 : ℕ)^8263*100000000000000^6215 ≤ 43126009183517^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656071917 5000000000 43126009183517 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5268071/9765625 : ℝ)^8263 ≤ (44017242025281/100000000000000 : ℝ)^6215 := by
    have hnat : (5268071 : ℕ)^8263*100000000000000^6215 ≤ 44017242025281^6215*9765625^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268071 9765625 44017242025281 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427528097/2000000000 : ℝ)^8263 ≤ (3214187193789/25000000000000 : ℝ)^6215 := by
    have hnat : (427528097 : ℕ)^8263*25000000000000^6215 ≤ 3214187193789^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427528097 2000000000 3214187193789 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656071917/5000000000 : ℝ), (5268071/9765625 : ℝ), (-427528097/2000000000 : ℝ)] ![(43126009183517/100000000000000 : ℝ), (44017242025281/100000000000000 : ℝ), (3214187193789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656071917/5000000000 : ℝ)|^8263 ≤ (43126009183517/100000000000000 : ℝ)^6215
        have hw : |(2656071917/5000000000 : ℝ)|=(2656071917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5268071/9765625 : ℝ)|^8263 ≤ (44017242025281/100000000000000 : ℝ)^6215
        have hw : |(5268071/9765625 : ℝ)|=(5268071/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427528097/2000000000 : ℝ)|^8263 ≤ (3214187193789/25000000000000 : ℝ)^6215
        have hw : |(-427528097/2000000000 : ℝ)|=(427528097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s6_7 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187450093/5000000000 : ℝ)*x 0 + (563056101/1250000000 : ℝ)*x 1 + (4249141809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187450093/5000000000 : ℝ)^8263 ≤ (4164549883827/12500000000000 : ℝ)^6215 := by
    have hnat : (2187450093 : ℕ)^8263*12500000000000^6215 ≤ 4164549883827^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187450093 5000000000 4164549883827 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563056101/1250000000 : ℝ)^8263 ≤ (34634410795901/100000000000000 : ℝ)^6215 := by
    have hnat : (563056101 : ℕ)^8263*100000000000000^6215 ≤ 34634410795901^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563056101 1250000000 34634410795901 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249141809/10000000000 : ℝ)^8263 ≤ (16024595061671/50000000000000 : ℝ)^6215 := by
    have hnat : (4249141809 : ℕ)^8263*50000000000000^6215 ≤ 16024595061671^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249141809 10000000000 16024595061671 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187450093/5000000000 : ℝ), (563056101/1250000000 : ℝ), (4249141809/10000000000 : ℝ)] ![(4164549883827/12500000000000 : ℝ), (34634410795901/100000000000000 : ℝ), (16024595061671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187450093/5000000000 : ℝ)|^8263 ≤ (4164549883827/12500000000000 : ℝ)^6215
        have hw : |(2187450093/5000000000 : ℝ)|=(2187450093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563056101/1250000000 : ℝ)|^8263 ≤ (34634410795901/100000000000000 : ℝ)^6215
        have hw : |(563056101/1250000000 : ℝ)|=(563056101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249141809/10000000000 : ℝ)|^8263 ≤ (16024595061671/50000000000000 : ℝ)^6215
        have hw : |(4249141809/10000000000 : ℝ)|=(4249141809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5623/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14017/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2241/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2241/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2241/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2241/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2241/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2241/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2241/20000 : ℝ) ^ (4131/1024 : ℝ) ≤ (365676159058647/2500000000000000000 : ℝ) := by
    have hpowers : (2241/20000 : ℝ)^4131 ≤ (365676159058647/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2241 : ℕ)^4131*2500000000000000000^1024 ≤ 365676159058647^1024*20000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2241 20000 365676159058647 2500000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2241/20000 : ℝ)) (X := (365676159058647/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (703/5000 : ℝ) ^ (4131/1024 : ℝ) ≤ (36544303348168929/100000000000000000000 : ℝ) := by
    have hpowers : (703/5000 : ℝ)^4131 ≤ (36544303348168929/100000000000000000000 : ℝ)^1024 := by
      have hnat : (703 : ℕ)^4131*100000000000000000000^1024 ≤ 36544303348168929^1024*5000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 5000 36544303348168929 100000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/5000 : ℝ)) (X := (36544303348168929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250365676159058647/1250000000000000000 : ℝ) ≤ (5000362538077373/5000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (1250365676159058647/1250000000000000000 : ℝ)^1024 ≤ (5000362538077373/5000000000000000 : ℝ)^4131 := by
      have hnat : (1250365676159058647 : ℕ)^1024*5000000000000000^4131 ≤ 5000362538077373^4131*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250365676159058647 1250000000000000000 5000362538077373 5000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000362538077373/5000000000000000 : ℝ)) (X := (1250365676159058647/1250000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051171349710514809/100000000000000000000 : ℝ) ≤ (500063410047993/500000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (100051171349710514809/100000000000000000000 : ℝ)^1024 ≤ (500063410047993/500000000000000 : ℝ)^4131 := by
      have hnat : (100051171349710514809 : ℕ)^1024*500000000000000^4131 ≤ 500063410047993^4131*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051171349710514809 100000000000000000000 500063410047993 500000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500063410047993/500000000000000 : ℝ)) (X := (100051171349710514809/100000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036544303348168929/50000000000000000000 : ℝ) ≤ (5000905662882487/5000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (50036544303348168929/50000000000000000000 : ℝ)^1024 ≤ (5000905662882487/5000000000000000 : ℝ)^4131 := by
      have hnat : (50036544303348168929 : ℕ)^1024*5000000000000000^4131 ≤ 5000905662882487^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036544303348168929 50000000000000000000 5000905662882487 5000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000905662882487/5000000000000000 : ℝ)) (X := (50036544303348168929/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(365676159058647/2500000000000000000 : ℝ) ≤ ((2853989866553919509/2855000000000000000 : ℝ)+2*(271562402557/142750000000000 : ℝ)*(2241/20000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (2853989866553919509/2855000000000000000 : ℝ)+2*(271562402557/142750000000000 : ℝ)*(2241/20000 : ℝ)=(5000362538077373/5000000000000000 : ℝ) by norm_num, show 1+2*(365676159058647/2500000000000000000 : ℝ)=(1250365676159058647/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36544303348168929/100000000000000000000 : ℝ)+(365676159058647/2500000000000000000 : ℝ) ≤ ((2853989866553919509/2855000000000000000 : ℝ)+(271562402557/142750000000000 : ℝ)*((703/5000 : ℝ)+(2241/20000 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (2853989866553919509/2855000000000000000 : ℝ)+(271562402557/142750000000000 : ℝ)*((703/5000 : ℝ)+(2241/20000 : ℝ))=(500063410047993/500000000000000 : ℝ) by norm_num, show 1+(36544303348168929/100000000000000000000 : ℝ)+(365676159058647/2500000000000000000 : ℝ)=(100051171349710514809/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36544303348168929/100000000000000000000 : ℝ) ≤ ((2853989866553919509/2855000000000000000 : ℝ)+2*(271562402557/142750000000000 : ℝ)*(703/5000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (2853989866553919509/2855000000000000000 : ℝ)+2*(271562402557/142750000000000 : ℝ)*(703/5000 : ℝ)=(5000905662882487/5000000000000000 : ℝ) by norm_num, show 1+2*(36544303348168929/100000000000000000000 : ℝ)=(50036544303348168929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2853989866553919509/2855000000000000000 : ℝ)*(X 1 0+X 2 0)+(271562402557/142750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (2853989866553919509/2855000000000000000 : ℝ)) (alpha := (271562402557/142750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2853989866553919509/2855000000000000000 : ℝ)*(X 0 1+X 2 1)+(271562402557/142750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (2853989866553919509/2855000000000000000 : ℝ)) (alpha := (271562402557/142750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2853989866553919509/2855000000000000000 : ℝ)*(X 0 2+X 1 2)+(271562402557/142750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (2853989866553919509/2855000000000000000 : ℝ)) (alpha := (271562402557/142750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2201751607/10000000000 : ℝ)*X 0 0+(5394836021/10000000000 : ℝ)*X 0 1+(5264009301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672553647/5000000000 : ℝ)*X 1 0+(-283516913/1250000000 : ℝ)*X 1 1+(5264009439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069021349/2000000000 : ℝ)*X 2 0+(5264009743/10000000000 : ℝ)*X 2 1+(-226813563/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874978001/2000000000 : ℝ)*X 0 0+(1062122791/2500000000 : ℝ)*X 0 1+(2252548557/5000000000 : ℝ)*X 0 2+(874978001/2000000000 : ℝ)*X 1 0+(1062122791/2500000000 : ℝ)*X 1 1+(2252548557/5000000000 : ℝ)*X 1 2+(874978001/2000000000 : ℝ)*X 2 0+(1062122791/2500000000 : ℝ)*X 2 1+(2252548557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2201756757/10000000000 : ℝ)*X 0 0+(131608497/250000000 : ℝ)*X 0 1+(2697252133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42497153/80000000 : ℝ)*X 1 0+(-10688203/50000000 : ℝ)*X 1 1+(539450433/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656071917/5000000000 : ℝ)*X 2 0+(5268071/9765625 : ℝ)*X 2 1+(-427528097/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187450093/5000000000 : ℝ)*X 0 0+(563056101/1250000000 : ℝ)*X 0 1+(4249141809/10000000000 : ℝ)*X 0 2+(2187450093/5000000000 : ℝ)*X 1 0+(563056101/1250000000 : ℝ)*X 1 1+(4249141809/10000000000 : ℝ)*X 1 2+(2187450093/5000000000 : ℝ)*X 2 0+(563056101/1250000000 : ℝ)*X 2 1+(4249141809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (779835566137494036900097503/142750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1513358183/100000000000000 : ℝ)*(base19) + (412864521/50000000000000 : ℝ)*(base23) + (15427617/20000000000000 : ℝ)*(upper2) + (180961349/50000000000000 : ℝ)*(upper3) + (360652371299493/6250000000000 : ℝ)*(major0) + (360652371299493/6250000000000 : ℝ)*(major1) + (5770437940791889/100000000000000 : ℝ)*(major2) + (7643761677969579/100000000000000 : ℝ)*(sp0) + (7643795436984261/100000000000000 : ℝ)*(sp1) + (7643788528551381/100000000000000 : ℝ)*(sp2) + (3897051100670003/100000000000000 : ℝ)*(sp3) + (17636186433/50000000000000 : ℝ)*(sp4) + (7596062021/100000000000000 : ℝ)*(sp6) + (27648473119/100000000000000 : ℝ)*(sp7) + (1948539374571561/50000000000000 : ℝ)*(f.failure) + (1910949237585611/25000000000000 : ℝ)*(f.sum) + (16397283329939/14275000000000000000000000000 : ℝ)*base65 + (9702774638806063/17843750000000000000000000000000 : ℝ)*base68 + (1388153053425617499/285500000000000000000000000000000 : ℝ)*base70 + (100582788392443937/17843750000000000000000000000000 : ℝ)*base71 + (4967374110289/14275000000000000000000000000 : ℝ)*base73 + (1778642521937617499/285500000000000000000000000000000 : ℝ)*base76 + (129425117893153937/17843750000000000000000000000000 : ℝ)*base77 + (6031856035377313/17843750000000000000000000000000 : ℝ)*base80 + (303846491891/7137500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (9834669/2500000000000000000000 : ℝ)*base89 + (9834669/2500000000000000000000 : ℝ)*base91 + (15165331/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (220816720692265326398897301/35687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1388335579/100000000000000 : ℝ)*(base19) + (1111879601/100000000000000 : ℝ)*(base23) + (20603609/50000000000000 : ℝ)*(upper2) + (60681393/25000000000000 : ℝ)*(upper3) + (129148159/100000000000000 : ℝ)*(upper5) + (2899859031961363/50000000000000 : ℝ)*(major0) + (2899859031961363/50000000000000 : ℝ)*(major1) + (2899859031961363/50000000000000 : ℝ)*(major2) + (1366613831/4000000000000 : ℝ)*(sp1) + (2808427539/6250000000000 : ℝ)*(sp2) + (7682582772866367/100000000000000 : ℝ)*(sp4) + (3841273609592507/50000000000000 : ℝ)*(sp5) + (3841268363073071/50000000000000 : ℝ)*(sp6) + (244803321795549/6250000000000 : ℝ)*(sp7) + (244803321795549/6250000000000 : ℝ)*(f.failure) + (7682582772866367/100000000000000 : ℝ)*(f.sum) + (44155799500611/14275000000000000000000000000 : ℝ)*base66 + (644366110814249233/142750000000000000000000000000000 : ℝ)*base68 + (1043872890980749233/142750000000000000000000000000000 : ℝ)*base70 + (1130426148172249233/142750000000000000000000000000000 : ℝ)*base72 + (9172599845741/3568750000000000000000000000 : ℝ)*base73 + (2123556695063999233/142750000000000000000000000000000 : ℝ)*base76 + (596237334489249233/142750000000000000000000000000000 : ℝ)*base78 + (784584851575750767/142750000000000000000000000000000 : ℝ)*base79 + (53010910936807/7137500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1755521/312500000000000000000 : ℝ)*base89 + (1755521/312500000000000000000 : ℝ)*base91 + (1755521/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1070_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1070_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1070_s7_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100895843/5000000000 : ℝ)*x 0 + (1078876277/2000000000 : ℝ)*x 1 + (2632218773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100895843/5000000000 : ℝ)^8263 ≤ (13372245437313/100000000000000 : ℝ)^6215 := by
    have hnat : (1100895843 : ℕ)^8263*100000000000000^6215 ≤ 13372245437313^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100895843 5000000000 13372245437313 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078876277/2000000000 : ℝ)^8263 ≤ (22007952104881/50000000000000 : ℝ)^6215 := by
    have hnat : (1078876277 : ℕ)^8263*50000000000000^6215 ≤ 22007952104881^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078876277 2000000000 22007952104881 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632218773/5000000000 : ℝ)^8263 ≤ (4261185034457/10000000000000 : ℝ)^6215 := by
    have hnat : (2632218773 : ℕ)^8263*10000000000000^6215 ≤ 4261185034457^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632218773 5000000000 4261185034457 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100895843/5000000000 : ℝ), (1078876277/2000000000 : ℝ), (2632218773/5000000000 : ℝ)] ![(13372245437313/100000000000000 : ℝ), (22007952104881/50000000000000 : ℝ), (4261185034457/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100895843/5000000000 : ℝ)|^8263 ≤ (13372245437313/100000000000000 : ℝ)^6215
        have hw : |(-1100895843/5000000000 : ℝ)|=(1100895843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078876277/2000000000 : ℝ)|^8263 ≤ (22007952104881/50000000000000 : ℝ)^6215
        have hw : |(1078876277/2000000000 : ℝ)|=(1078876277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632218773/5000000000 : ℝ)|^8263 ≤ (4261185034457/10000000000000 : ℝ)^6215
        have hw : |(2632218773/5000000000 : ℝ)|=(2632218773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s7_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068998703/2000000000 : ℝ)*x 0 + (-1133860261/5000000000 : ℝ)*x 1 + (2632219033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068998703/2000000000 : ℝ)^8263 ≤ (2717558503289/6250000000000 : ℝ)^6215 := by
    have hnat : (1068998703 : ℕ)^8263*6250000000000^6215 ≤ 2717558503289^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068998703 2000000000 2717558503289 6250000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133860261/5000000000 : ℝ)^8263 ≤ (13907207992949/100000000000000 : ℝ)^6215 := by
    have hnat : (1133860261 : ℕ)^8263*100000000000000^6215 ≤ 13907207992949^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133860261 5000000000 13907207992949 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632219033/5000000000 : ℝ)^8263 ≤ (42611855940579/100000000000000 : ℝ)^6215 := by
    have hnat : (2632219033 : ℕ)^8263*100000000000000^6215 ≤ 42611855940579^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632219033 5000000000 42611855940579 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068998703/2000000000 : ℝ), (-1133860261/5000000000 : ℝ), (2632219033/5000000000 : ℝ)] ![(2717558503289/6250000000000 : ℝ), (13907207992949/100000000000000 : ℝ), (42611855940579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068998703/2000000000 : ℝ)|^8263 ≤ (2717558503289/6250000000000 : ℝ)^6215
        have hw : |(1068998703/2000000000 : ℝ)|=(1068998703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133860261/5000000000 : ℝ)|^8263 ≤ (13907207992949/100000000000000 : ℝ)^6215
        have hw : |(-1133860261/5000000000 : ℝ)|=(1133860261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632219033/5000000000 : ℝ)|^8263 ≤ (42611855940579/100000000000000 : ℝ)^6215
        have hw : |(2632219033/5000000000 : ℝ)|=(2632219033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s7_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344993683/10000000000 : ℝ)*x 0 + (5264437629/10000000000 : ℝ)*x 1 + (-566930219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344993683/10000000000 : ℝ)^8263 ≤ (8696187573927/20000000000000 : ℝ)^6215 := by
    have hnat : (5344993683 : ℕ)^8263*20000000000000^6215 ≤ 8696187573927^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344993683 10000000000 8696187573927 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264437629/10000000000 : ℝ)^8263 ≤ (42611851237779/100000000000000 : ℝ)^6215 := by
    have hnat : (5264437629 : ℕ)^8263*100000000000000^6215 ≤ 42611851237779^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264437629 10000000000 42611851237779 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566930219/2500000000 : ℝ)^8263 ≤ (3476802719827/25000000000000 : ℝ)^6215 := by
    have hnat : (566930219 : ℕ)^8263*25000000000000^6215 ≤ 3476802719827^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566930219 2500000000 3476802719827 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344993683/10000000000 : ℝ), (5264437629/10000000000 : ℝ), (-566930219/2500000000 : ℝ)] ![(8696187573927/20000000000000 : ℝ), (42611851237779/100000000000000 : ℝ), (3476802719827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344993683/10000000000 : ℝ)|^8263 ≤ (8696187573927/20000000000000 : ℝ)^6215
        have hw : |(5344993683/10000000000 : ℝ)|=(5344993683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264437629/10000000000 : ℝ)|^8263 ≤ (42611851237779/100000000000000 : ℝ)^6215
        have hw : |(5264437629/10000000000 : ℝ)|=(5264437629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-566930219/2500000000 : ℝ)|^8263 ≤ (3476802719827/25000000000000 : ℝ)^6215
        have hw : |(-566930219/2500000000 : ℝ)|=(566930219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s7_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187456207/5000000000 : ℝ)*x 0 + (531169389/1250000000 : ℝ)*x 1 + (4504227453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187456207/5000000000 : ℝ)^8263 ≤ (8329130719187/25000000000000 : ℝ)^6215 := by
    have hnat : (2187456207 : ℕ)^8263*25000000000000^6215 ≤ 8329130719187^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187456207 5000000000 8329130719187 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531169389/1250000000 : ℝ)^8263 ≤ (32051329134301/100000000000000 : ℝ)^6215 := by
    have hnat : (531169389 : ℕ)^8263*100000000000000^6215 ≤ 32051329134301^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531169389 1250000000 32051329134301 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504227453/10000000000 : ℝ)^8263 ≤ (4329018497913/12500000000000 : ℝ)^6215 := by
    have hnat : (4504227453 : ℕ)^8263*12500000000000^6215 ≤ 4329018497913^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504227453 10000000000 4329018497913 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187456207/5000000000 : ℝ), (531169389/1250000000 : ℝ), (4504227453/10000000000 : ℝ)] ![(8329130719187/25000000000000 : ℝ), (32051329134301/100000000000000 : ℝ), (4329018497913/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187456207/5000000000 : ℝ)|^8263 ≤ (8329130719187/25000000000000 : ℝ)^6215
        have hw : |(2187456207/5000000000 : ℝ)|=(2187456207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531169389/1250000000 : ℝ)|^8263 ≤ (32051329134301/100000000000000 : ℝ)^6215
        have hw : |(531169389/1250000000 : ℝ)|=(531169389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504227453/10000000000 : ℝ)|^8263 ≤ (4329018497913/12500000000000 : ℝ)^6215
        have hw : |(4504227453/10000000000 : ℝ)|=(4504227453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s7_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-550449127/2500000000 : ℝ)*x 0 + (263238197/500000000 : ℝ)*x 1 + (2697027003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550449127/2500000000 : ℝ)^8263 ≤ (13372284373381/100000000000000 : ℝ)^6215 := by
    have hnat : (550449127 : ℕ)^8263*100000000000000^6215 ≤ 13372284373381^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550449127 2500000000 13372284373381 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263238197/500000000 : ℝ)^8263 ≤ (42615362887477/100000000000000 : ℝ)^6215 := by
    have hnat : (263238197 : ℕ)^8263*100000000000000^6215 ≤ 42615362887477^6215*500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263238197 500000000 42615362887477 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697027003/5000000000 : ℝ)^8263 ≤ (5501544089481/12500000000000 : ℝ)^6215 := by
    have hnat : (2697027003 : ℕ)^8263*12500000000000^6215 ≤ 5501544089481^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697027003 5000000000 5501544089481 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550449127/2500000000 : ℝ), (263238197/500000000 : ℝ), (2697027003/5000000000 : ℝ)] ![(13372284373381/100000000000000 : ℝ), (42615362887477/100000000000000 : ℝ), (5501544089481/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550449127/2500000000 : ℝ)|^8263 ≤ (13372284373381/100000000000000 : ℝ)^6215
        have hw : |(-550449127/2500000000 : ℝ)|=(550449127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263238197/500000000 : ℝ)|^8263 ≤ (42615362887477/100000000000000 : ℝ)^6215
        have hw : |(263238197/500000000 : ℝ)|=(263238197/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697027003/5000000000 : ℝ)|^8263 ≤ (5501544089481/12500000000000 : ℝ)^6215
        have hw : |(2697027003/5000000000 : ℝ)|=(2697027003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s7_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312252859/10000000000 : ℝ)*x 0 + (-1069052373/5000000000 : ℝ)*x 1 + (2697027003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312252859/10000000000 : ℝ)^8263 ≤ (43127185959047/100000000000000 : ℝ)^6215 := by
    have hnat : (5312252859 : ℕ)^8263*100000000000000^6215 ≤ 43127185959047^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312252859 10000000000 43127185959047 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069052373/5000000000 : ℝ)^8263 ≤ (2572092262539/20000000000000 : ℝ)^6215 := by
    have hnat : (1069052373 : ℕ)^8263*20000000000000^6215 ≤ 2572092262539^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069052373 5000000000 2572092262539 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697027003/5000000000 : ℝ)^8263 ≤ (5501544089481/12500000000000 : ℝ)^6215 := by
    have hnat : (2697027003 : ℕ)^8263*12500000000000^6215 ≤ 5501544089481^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697027003 5000000000 5501544089481 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312252859/10000000000 : ℝ), (-1069052373/5000000000 : ℝ), (2697027003/5000000000 : ℝ)] ![(43127185959047/100000000000000 : ℝ), (2572092262539/20000000000000 : ℝ), (5501544089481/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312252859/10000000000 : ℝ)|^8263 ≤ (43127185959047/100000000000000 : ℝ)^6215
        have hw : |(5312252859/10000000000 : ℝ)|=(5312252859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069052373/5000000000 : ℝ)|^8263 ≤ (2572092262539/20000000000000 : ℝ)^6215
        have hw : |(-1069052373/5000000000 : ℝ)|=(1069052373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697027003/5000000000 : ℝ)|^8263 ≤ (5501544089481/12500000000000 : ℝ)^6215
        have hw : |(2697027003/5000000000 : ℝ)|=(2697027003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s7_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312252859/10000000000 : ℝ)*x 0 + (2697027003/5000000000 : ℝ)*x 1 + (-1069052373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312252859/10000000000 : ℝ)^8263 ≤ (43127185959047/100000000000000 : ℝ)^6215 := by
    have hnat : (5312252859 : ℕ)^8263*100000000000000^6215 ≤ 43127185959047^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312252859 10000000000 43127185959047 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697027003/5000000000 : ℝ)^8263 ≤ (5501544089481/12500000000000 : ℝ)^6215 := by
    have hnat : (2697027003 : ℕ)^8263*12500000000000^6215 ≤ 5501544089481^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697027003 5000000000 5501544089481 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069052373/5000000000 : ℝ)^8263 ≤ (2572092262539/20000000000000 : ℝ)^6215 := by
    have hnat : (1069052373 : ℕ)^8263*20000000000000^6215 ≤ 2572092262539^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069052373 5000000000 2572092262539 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312252859/10000000000 : ℝ), (2697027003/5000000000 : ℝ), (-1069052373/5000000000 : ℝ)] ![(43127185959047/100000000000000 : ℝ), (5501544089481/12500000000000 : ℝ), (2572092262539/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312252859/10000000000 : ℝ)|^8263 ≤ (43127185959047/100000000000000 : ℝ)^6215
        have hw : |(5312252859/10000000000 : ℝ)|=(5312252859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697027003/5000000000 : ℝ)|^8263 ≤ (5501544089481/12500000000000 : ℝ)^6215
        have hw : |(2697027003/5000000000 : ℝ)|=(2697027003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1069052373/5000000000 : ℝ)|^8263 ≤ (2572092262539/20000000000000 : ℝ)^6215
        have hw : |(-1069052373/5000000000 : ℝ)|=(1069052373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s7_7 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374922573/10000000000 : ℝ)*x 0 + (4503588209/10000000000 : ℝ)*x 1 + (849999291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374922573/10000000000 : ℝ)^8263 ≤ (33316625734743/100000000000000 : ℝ)^6215 := by
    have hnat : (4374922573 : ℕ)^8263*100000000000000^6215 ≤ 33316625734743^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374922573 10000000000 33316625734743 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503588209/10000000000 : ℝ)^8263 ≤ (34625613485147/100000000000000 : ℝ)^6215 := by
    have hnat : (4503588209 : ℕ)^8263*100000000000000^6215 ≤ 34625613485147^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503588209 10000000000 34625613485147 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849999291/2000000000 : ℝ)^8263 ≤ (4007220095063/12500000000000 : ℝ)^6215 := by
    have hnat : (849999291 : ℕ)^8263*12500000000000^6215 ≤ 4007220095063^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849999291 2000000000 4007220095063 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374922573/10000000000 : ℝ), (4503588209/10000000000 : ℝ), (849999291/2000000000 : ℝ)] ![(33316625734743/100000000000000 : ℝ), (34625613485147/100000000000000 : ℝ), (4007220095063/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374922573/10000000000 : ℝ)|^8263 ≤ (33316625734743/100000000000000 : ℝ)^6215
        have hw : |(4374922573/10000000000 : ℝ)|=(4374922573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503588209/10000000000 : ℝ)|^8263 ≤ (34625613485147/100000000000000 : ℝ)^6215
        have hw : |(4503588209/10000000000 : ℝ)|=(4503588209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849999291/2000000000 : ℝ)|^8263 ≤ (4007220095063/12500000000000 : ℝ)^6215
        have hw : |(849999291/2000000000 : ℝ)|=(849999291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2251/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14017/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14017/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14017/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14017/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14017/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14017/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5623/50000 : ℝ) ^ (4131/1024 : ℝ) ≤ (14844163445090479/100000000000000000000 : ℝ) := by
    have hpowers : (5623/50000 : ℝ)^4131 ≤ (14844163445090479/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5623 : ℕ)^4131*100000000000000000000^1024 ≤ 14844163445090479^1024*50000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5623 50000 14844163445090479 100000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5623/50000 : ℝ)) (X := (14844163445090479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14017/100000 : ℝ) ^ (4131/1024 : ℝ) ≤ (360955139913231/1000000000000000000 : ℝ) := by
    have hpowers : (14017/100000 : ℝ)^4131 ≤ (360955139913231/1000000000000000000 : ℝ)^1024 := by
      have hnat : (14017 : ℕ)^4131*1000000000000000000^1024 ≤ 360955139913231^1024*100000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14017 100000 360955139913231 1000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14017/100000 : ℝ)) (X := (360955139913231/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014844163445090479/50000000000000000000 : ℝ) ≤ (10000735837647103/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (50014844163445090479/50000000000000000000 : ℝ)^1024 ≤ (10000735837647103/10000000000000000 : ℝ)^4131 := by
      have hnat : (50014844163445090479 : ℕ)^1024*10000000000000000^4131 ≤ 10000735837647103^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014844163445090479 50000000000000000000 10000735837647103 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000735837647103/10000000000000000 : ℝ)) (X := (50014844163445090479/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050939677436413579/100000000000000000000 : ℝ) ≤ (5000631230214223/5000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (100050939677436413579/100000000000000000000 : ℝ)^1024 ≤ (5000631230214223/5000000000000000 : ℝ)^4131 := by
      have hnat : (100050939677436413579 : ℕ)^1024*5000000000000000^4131 ≤ 5000631230214223^4131*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050939677436413579 100000000000000000000 5000631230214223 5000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000631230214223/5000000000000000 : ℝ)) (X := (100050939677436413579/100000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (500360955139913231/500000000000000000 : ℝ) ≤ (10001789083209789/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (500360955139913231/500000000000000000 : ℝ)^1024 ≤ (10001789083209789/10000000000000000 : ℝ)^4131 := by
      have hnat : (500360955139913231 : ℕ)^1024*10000000000000000^4131 ≤ 10001789083209789^4131*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500360955139913231 500000000000000000 10001789083209789 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001789083209789/10000000000000000 : ℝ)) (X := (500360955139913231/500000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14844163445090479/100000000000000000000 : ℝ) ≤ ((27700194206522155657/27710000000000000000 : ℝ)+2*(526622781343/277100000000000 : ℝ)*(5623/50000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (27700194206522155657/27710000000000000000 : ℝ)+2*(526622781343/277100000000000 : ℝ)*(5623/50000 : ℝ)=(10000735837647103/10000000000000000 : ℝ) by norm_num, show 1+2*(14844163445090479/100000000000000000000 : ℝ)=(50014844163445090479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(360955139913231/1000000000000000000 : ℝ)+(14844163445090479/100000000000000000000 : ℝ) ≤ ((27700194206522155657/27710000000000000000 : ℝ)+(526622781343/277100000000000 : ℝ)*((14017/100000 : ℝ)+(5623/50000 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (27700194206522155657/27710000000000000000 : ℝ)+(526622781343/277100000000000 : ℝ)*((14017/100000 : ℝ)+(5623/50000 : ℝ))=(5000631230214223/5000000000000000 : ℝ) by norm_num, show 1+(360955139913231/1000000000000000000 : ℝ)+(14844163445090479/100000000000000000000 : ℝ)=(100050939677436413579/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(360955139913231/1000000000000000000 : ℝ) ≤ ((27700194206522155657/27710000000000000000 : ℝ)+2*(526622781343/277100000000000 : ℝ)*(14017/100000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (27700194206522155657/27710000000000000000 : ℝ)+2*(526622781343/277100000000000 : ℝ)*(14017/100000 : ℝ)=(10001789083209789/10000000000000000 : ℝ) by norm_num, show 1+2*(360955139913231/1000000000000000000 : ℝ)=(500360955139913231/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27700194206522155657/27710000000000000000 : ℝ)*(X 1 0+X 2 0)+(526622781343/277100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (27700194206522155657/27710000000000000000 : ℝ)) (alpha := (526622781343/277100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27700194206522155657/27710000000000000000 : ℝ)*(X 0 1+X 2 1)+(526622781343/277100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (27700194206522155657/27710000000000000000 : ℝ)) (alpha := (526622781343/277100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27700194206522155657/27710000000000000000 : ℝ)*(X 0 2+X 1 2)+(526622781343/277100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14017/100000 : ℝ)) (c := (27700194206522155657/27710000000000000000 : ℝ)) (alpha := (526622781343/277100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1100895843/5000000000 : ℝ)*X 0 0+(1078876277/2000000000 : ℝ)*X 0 1+(2632218773/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068998703/2000000000 : ℝ)*X 1 0+(-1133860261/5000000000 : ℝ)*X 1 1+(2632219033/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344993683/10000000000 : ℝ)*X 2 0+(5264437629/10000000000 : ℝ)*X 2 1+(-566930219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187456207/5000000000 : ℝ)*X 0 0+(531169389/1250000000 : ℝ)*X 0 1+(4504227453/10000000000 : ℝ)*X 0 2+(2187456207/5000000000 : ℝ)*X 1 0+(531169389/1250000000 : ℝ)*X 1 1+(4504227453/10000000000 : ℝ)*X 1 2+(2187456207/5000000000 : ℝ)*X 2 0+(531169389/1250000000 : ℝ)*X 2 1+(4504227453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-550449127/2500000000 : ℝ)*X 0 0+(263238197/500000000 : ℝ)*X 0 1+(2697027003/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312252859/10000000000 : ℝ)*X 1 0+(-1069052373/5000000000 : ℝ)*X 1 1+(2697027003/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312252859/10000000000 : ℝ)*X 2 0+(2697027003/5000000000 : ℝ)*X 2 1+(-1069052373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4374922573/10000000000 : ℝ)*X 0 0+(4503588209/10000000000 : ℝ)*X 0 1+(849999291/2000000000 : ℝ)*X 0 2+(4374922573/10000000000 : ℝ)*X 1 0+(4503588209/10000000000 : ℝ)*X 1 1+(849999291/2000000000 : ℝ)*X 1 2+(4374922573/10000000000 : ℝ)*X 2 0+(4503588209/10000000000 : ℝ)*X 2 1+(849999291/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6596464150435179533371553151/1385500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1658579913/100000000000000 : ℝ)*(base19) + (108658911/5000000000000 : ℝ)*(base23) + (9620047/5000000000000 : ℝ)*(upper2) + (312596939/100000000000000 : ℝ)*(upper3) + (46637607/100000000000000 : ℝ)*(upper4) + (580968353786679/10000000000000 : ℝ)*(major0) + (580968353786679/10000000000000 : ℝ)*(major1) + (5809683537866791/100000000000000 : ℝ)*(major2) + (384785810425071/5000000000000 : ℝ)*(sp0) + (3847890951802259/50000000000000 : ℝ)*(sp1) + (7695781389006211/100000000000000 : ℝ)*(sp2) + (245222184308423/6250000000000 : ℝ)*(sp3) + (67353683011/100000000000000 : ℝ)*(sp4) + (28405911997/100000000000000 : ℝ)*(sp7) + (1961791677423383/50000000000000 : ℝ)*(f.failure) + (7695783562184431/100000000000000 : ℝ)*(f.sum) + (173138693251533/27710000000000000000000000000 : ℝ)*base65 + (5130204607961676897/277100000000000000000000000000000 : ℝ)*base68 + (19867932941644913313/2771000000000000000000000000000000 : ℝ)*base70 + (564026549117076897/277100000000000000000000000000000 : ℝ)*base72 + (217381574683253/27710000000000000000000000000 : ℝ)*base73 + (28147056917986913313/2771000000000000000000000000000000 : ℝ)*base76 + (2310312593624193103/277100000000000000000000000000000 : ℝ)*base77 + (5912909157226006897/277100000000000000000000000000000 : ℝ)*base80 + (11981425233219/2771000000000000000000000000 : ℝ)*base82 + (25036307/2500000000000000000000 : ℝ)*base89 + (25036307/2500000000000000000000 : ℝ)*base91 + (36307/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27523147367940498180369/13855000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92116257/25000000000000 : ℝ)*(base19) + (40289459/10000000000000 : ℝ)*(base23) + (19976787/50000000000000 : ℝ)*(upper3) + (979291/6250000000000 : ℝ)*(lower4) + (20386179/50000000000000 : ℝ)*(upper5) + (2919472932131433/50000000000000 : ℝ)*(major0) + (2919472932131433/50000000000000 : ℝ)*(major1) + (2919472932131433/50000000000000 : ℝ)*(major2) + (10011070083/100000000000000 : ℝ)*(sp1) + (10811608889/100000000000000 : ℝ)*(sp2) + (7734545926942589/100000000000000 : ℝ)*(sp4) + (3867267773703739/50000000000000 : ℝ)*(sp5) + (773453471243911/10000000000000 : ℝ)*(sp6) + (1971672867683007/50000000000000 : ℝ)*(sp7) + (1971672867683007/50000000000000 : ℝ)*(f.failure) + (7734545926942589/100000000000000 : ℝ)*(f.sum) + (912509547939/1731875000000000000000000000 : ℝ)*base66 + (8446174933142633519/1385500000000000000000000000000000 : ℝ)*base68 + (2371016120268366481/1385500000000000000000000000000000 : ℝ)*base69 + (7260884179510866481/1385500000000000000000000000000000 : ℝ)*base71 + (6100573441111/6927500000000000000000000000 : ℝ)*base74 + (25937207881757633519/1385500000000000000000000000000000 : ℝ)*base76 + (3321114716295866481/1385500000000000000000000000000000 : ℝ)*base77 + (18964361922918133519/1385500000000000000000000000000000 : ℝ)*base80 + (4146223313651/1731875000000000000000000000 : ℝ)*base81 + (9255003/2500000000000000000000 : ℝ)*base89 + (9255003/2500000000000000000000 : ℝ)*base91 + (9255003/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1070_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14017/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1070_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1070_s8_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100901109/5000000000 : ℝ)*x 0 + (1348569717/2500000000 : ℝ)*x 1 + (5264532987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100901109/5000000000 : ℝ)^8263 ≤ (6686165239897/50000000000000 : ℝ)^6215 := by
    have hnat : (1100901109 : ℕ)^8263*50000000000000^6215 ≤ 6686165239897^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100901109 5000000000 6686165239897 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348569717/2500000000 : ℝ)^8263 ≤ (44014792070613/100000000000000 : ℝ)^6215 := by
    have hnat : (1348569717 : ℕ)^8263*100000000000000^6215 ≤ 44014792070613^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348569717 2500000000 44014792070613 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264532987/10000000000 : ℝ)^8263 ≤ (21306438720611/50000000000000 : ℝ)^6215 := by
    have hnat : (5264532987 : ℕ)^8263*50000000000000^6215 ≤ 21306438720611^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264532987 10000000000 21306438720611 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100901109/5000000000 : ℝ), (1348569717/2500000000 : ℝ), (5264532987/10000000000 : ℝ)] ![(6686165239897/50000000000000 : ℝ), (44014792070613/100000000000000 : ℝ), (21306438720611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100901109/5000000000 : ℝ)|^8263 ≤ (6686165239897/50000000000000 : ℝ)^6215
        have hw : |(-1100901109/5000000000 : ℝ)|=(1100901109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348569717/2500000000 : ℝ)|^8263 ≤ (44014792070613/100000000000000 : ℝ)^6215
        have hw : |(1348569717/2500000000 : ℝ)|=(1348569717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264532987/10000000000 : ℝ)|^8263 ≤ (21306438720611/50000000000000 : ℝ)^6215
        have hw : |(5264532987/10000000000 : ℝ)|=(5264532987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s8_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068993459/2000000000 : ℝ)*x 0 + (-113381501/500000000 : ℝ)*x 1 + (2632266493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068993459/2000000000 : ℝ)^8263 ≤ (1087016311733/2500000000000 : ℝ)^6215 := by
    have hnat : (1068993459 : ℕ)^8263*2500000000000^6215 ≤ 1087016311733^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068993459 2000000000 1087016311733 2500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113381501/500000000 : ℝ)^8263 ≤ (13906470084709/100000000000000 : ℝ)^6215 := by
    have hnat : (113381501 : ℕ)^8263*100000000000000^6215 ≤ 13906470084709^6215*500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113381501 500000000 13906470084709 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632266493/5000000000 : ℝ)^8263 ≤ (2130643871523/5000000000000 : ℝ)^6215 := by
    have hnat : (2632266493 : ℕ)^8263*5000000000000^6215 ≤ 2130643871523^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632266493 5000000000 2130643871523 5000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068993459/2000000000 : ℝ), (-113381501/500000000 : ℝ), (2632266493/5000000000 : ℝ)] ![(1087016311733/2500000000000 : ℝ), (13906470084709/100000000000000 : ℝ), (2130643871523/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068993459/2000000000 : ℝ)|^8263 ≤ (1087016311733/2500000000000 : ℝ)^6215
        have hw : |(1068993459/2000000000 : ℝ)|=(1068993459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113381501/500000000 : ℝ)|^8263 ≤ (13906470084709/100000000000000 : ℝ)^6215
        have hw : |(-113381501/500000000 : ℝ)|=(113381501/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632266493/5000000000 : ℝ)|^8263 ≤ (2130643871523/5000000000000 : ℝ)^6215
        have hw : |(2632266493/5000000000 : ℝ)|=(2632266493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s8_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534496731/1000000000 : ℝ)*x 0 + (5264532991/10000000000 : ℝ)*x 1 + (-1133814997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534496731/1000000000 : ℝ)^8263 ≤ (43480652631553/100000000000000 : ℝ)^6215 := by
    have hnat : (534496731 : ℕ)^8263*100000000000000^6215 ≤ 43480652631553^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534496731 1000000000 43480652631553 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264532991/10000000000 : ℝ)^8263 ≤ (10653219371067/25000000000000 : ℝ)^6215 := by
    have hnat : (5264532991 : ℕ)^8263*25000000000000^6215 ≤ 10653219371067^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264532991 10000000000 10653219371067 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133814997/5000000000 : ℝ)^8263 ≤ (13906469872719/100000000000000 : ℝ)^6215 := by
    have hnat : (1133814997 : ℕ)^8263*100000000000000^6215 ≤ 13906469872719^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133814997 5000000000 13906469872719 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534496731/1000000000 : ℝ), (5264532991/10000000000 : ℝ), (-1133814997/5000000000 : ℝ)] ![(43480652631553/100000000000000 : ℝ), (10653219371067/25000000000000 : ℝ), (13906469872719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534496731/1000000000 : ℝ)|^8263 ≤ (43480652631553/100000000000000 : ℝ)^6215
        have hw : |(534496731/1000000000 : ℝ)|=(534496731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264532991/10000000000 : ℝ)|^8263 ≤ (10653219371067/25000000000000 : ℝ)^6215
        have hw : |(5264532991/10000000000 : ℝ)|=(5264532991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1133814997/5000000000 : ℝ)|^8263 ≤ (13906469872719/100000000000000 : ℝ)^6215
        have hw : |(-1133814997/5000000000 : ℝ)|=(1133814997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s8_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093729419/2500000000 : ℝ)*x 0 + (10623869/25000000 : ℝ)*x 1 + (4504033409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093729419/2500000000 : ℝ)^8263 ≤ (6663315230703/20000000000000 : ℝ)^6215 := by
    have hnat : (1093729419 : ℕ)^8263*20000000000000^6215 ≤ 6663315230703^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093729419 2500000000 6663315230703 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10623869/25000000 : ℝ)^8263 ≤ (500832178781/1562500000000 : ℝ)^6215 := by
    have hnat : (10623869 : ℕ)^8263*1562500000000^6215 ≤ 500832178781^6215*25000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10623869 25000000 500832178781 1562500000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504033409/10000000000 : ℝ)^8263 ≤ (8657541097229/25000000000000 : ℝ)^6215 := by
    have hnat : (4504033409 : ℕ)^8263*25000000000000^6215 ≤ 8657541097229^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504033409 10000000000 8657541097229 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093729419/2500000000 : ℝ), (10623869/25000000 : ℝ), (4504033409/10000000000 : ℝ)] ![(6663315230703/20000000000000 : ℝ), (500832178781/1562500000000 : ℝ), (8657541097229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093729419/2500000000 : ℝ)|^8263 ≤ (6663315230703/20000000000000 : ℝ)^6215
        have hw : |(1093729419/2500000000 : ℝ)|=(1093729419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10623869/25000000 : ℝ)|^8263 ≤ (500832178781/1562500000000 : ℝ)^6215
        have hw : |(10623869/25000000 : ℝ)|=(10623869/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504033409/10000000000 : ℝ)|^8263 ≤ (8657541097229/25000000000000 : ℝ)^6215
        have hw : |(4504033409/10000000000 : ℝ)|=(4504033409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s8_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-220180769/1000000000 : ℝ)*x 0 + (5264858073/10000000000 : ℝ)*x 1 + (5393952299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220180769/1000000000 : ℝ)^8263 ≤ (13372374664471/100000000000000 : ℝ)^6215 := by
    have hnat : (220180769 : ℕ)^8263*100000000000000^6215 ≤ 13372374664471^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220180769 1000000000 13372374664471 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264858073/10000000000 : ℝ)^8263 ≤ (42616375928627/100000000000000 : ℝ)^6215 := by
    have hnat : (5264858073 : ℕ)^8263*100000000000000^6215 ≤ 42616375928627^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264858073 10000000000 42616375928627 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393952299/10000000000 : ℝ)^8263 ≤ (44011249385893/100000000000000 : ℝ)^6215 := by
    have hnat : (5393952299 : ℕ)^8263*100000000000000^6215 ≤ 44011249385893^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393952299 10000000000 44011249385893 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220180769/1000000000 : ℝ), (5264858073/10000000000 : ℝ), (5393952299/10000000000 : ℝ)] ![(13372374664471/100000000000000 : ℝ), (42616375928627/100000000000000 : ℝ), (44011249385893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220180769/1000000000 : ℝ)|^8263 ≤ (13372374664471/100000000000000 : ℝ)^6215
        have hw : |(-220180769/1000000000 : ℝ)|=(220180769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264858073/10000000000 : ℝ)|^8263 ≤ (42616375928627/100000000000000 : ℝ)^6215
        have hw : |(5264858073/10000000000 : ℝ)|=(5264858073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393952299/10000000000 : ℝ)|^8263 ≤ (44011249385893/100000000000000 : ℝ)^6215
        have hw : |(5393952299/10000000000 : ℝ)|=(5393952299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s8_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166008639/312500000 : ℝ)*x 0 + (-1069105147/5000000000 : ℝ)*x 1 + (674244091/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166008639/312500000 : ℝ)^8263 ≤ (43127440571037/100000000000000 : ℝ)^6215 := by
    have hnat : (166008639 : ℕ)^8263*100000000000000^6215 ≤ 43127440571037^6215*312500000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166008639 312500000 43127440571037 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069105147/5000000000 : ℝ)^8263 ≤ (12861305381267/100000000000000 : ℝ)^6215 := by
    have hnat : (1069105147 : ℕ)^8263*100000000000000^6215 ≤ 12861305381267^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069105147 5000000000 12861305381267 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674244091/1250000000 : ℝ)^8263 ≤ (44011254039723/100000000000000 : ℝ)^6215 := by
    have hnat : (674244091 : ℕ)^8263*100000000000000^6215 ≤ 44011254039723^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674244091 1250000000 44011254039723 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166008639/312500000 : ℝ), (-1069105147/5000000000 : ℝ), (674244091/1250000000 : ℝ)] ![(43127440571037/100000000000000 : ℝ), (12861305381267/100000000000000 : ℝ), (44011254039723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166008639/312500000 : ℝ)|^8263 ≤ (43127440571037/100000000000000 : ℝ)^6215
        have hw : |(166008639/312500000 : ℝ)|=(166008639/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069105147/5000000000 : ℝ)|^8263 ≤ (12861305381267/100000000000000 : ℝ)^6215
        have hw : |(-1069105147/5000000000 : ℝ)|=(1069105147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674244091/1250000000 : ℝ)|^8263 ≤ (44011254039723/100000000000000 : ℝ)^6215
        have hw : |(674244091/1250000000 : ℝ)|=(674244091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s8_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664034533/1250000000 : ℝ)*x 0 + (5393953027/10000000000 : ℝ)*x 1 + (-427642027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664034533/1250000000 : ℝ)^8263 ≤ (43127438584999/100000000000000 : ℝ)^6215 := by
    have hnat : (664034533 : ℕ)^8263*100000000000000^6215 ≤ 43127438584999^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664034533 1250000000 43127438584999 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393953027/10000000000 : ℝ)^8263 ≤ (44011257283301/100000000000000 : ℝ)^6215 := by
    have hnat : (5393953027 : ℕ)^8263*100000000000000^6215 ≤ 44011257283301^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393953027 10000000000 44011257283301 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427642027/2000000000 : ℝ)^8263 ≤ (3215326027433/25000000000000 : ℝ)^6215 := by
    have hnat : (427642027 : ℕ)^8263*25000000000000^6215 ≤ 3215326027433^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427642027 2000000000 3215326027433 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664034533/1250000000 : ℝ), (5393953027/10000000000 : ℝ), (-427642027/2000000000 : ℝ)] ![(43127438584999/100000000000000 : ℝ), (44011257283301/100000000000000 : ℝ), (3215326027433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664034533/1250000000 : ℝ)|^8263 ≤ (43127438584999/100000000000000 : ℝ)^6215
        have hw : |(664034533/1250000000 : ℝ)|=(664034533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393953027/10000000000 : ℝ)|^8263 ≤ (44011257283301/100000000000000 : ℝ)^6215
        have hw : |(5393953027/10000000000 : ℝ)|=(5393953027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427642027/2000000000 : ℝ)|^8263 ≤ (3215326027433/25000000000000 : ℝ)^6215
        have hw : |(-427642027/2000000000 : ℝ)|=(427642027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s8_7 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093732029/2500000000 : ℝ)*x 0 + (2251697811/5000000000 : ℝ)*x 1 + (1062546789/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093732029/2500000000 : ℝ)^8263 ≤ (266533454853/800000000000 : ℝ)^6215 := by
    have hnat : (1093732029 : ℕ)^8263*800000000000^6215 ≤ 266533454853^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093732029 2500000000 266533454853 800000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251697811/5000000000 : ℝ)^8263 ≤ (34623644876759/100000000000000 : ℝ)^6215 := by
    have hnat : (2251697811 : ℕ)^8263*100000000000000^6215 ≤ 34623644876759^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251697811 5000000000 34623644876759 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062546789/2500000000 : ℝ)^8263 ≤ (3205967324277/10000000000000 : ℝ)^6215 := by
    have hnat : (1062546789 : ℕ)^8263*10000000000000^6215 ≤ 3205967324277^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062546789 2500000000 3205967324277 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093732029/2500000000 : ℝ), (2251697811/5000000000 : ℝ), (1062546789/2500000000 : ℝ)] ![(266533454853/800000000000 : ℝ), (34623644876759/100000000000000 : ℝ), (3205967324277/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093732029/2500000000 : ℝ)|^8263 ≤ (266533454853/800000000000 : ℝ)^6215
        have hw : |(1093732029/2500000000 : ℝ)|=(1093732029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251697811/5000000000 : ℝ)|^8263 ≤ (34623644876759/100000000000000 : ℝ)^6215
        have hw : |(2251697811/5000000000 : ℝ)|=(2251697811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062546789/2500000000 : ℝ)|^8263 ≤ (3205967324277/10000000000000 : ℝ)^6215
        have hw : |(1062546789/2500000000 : ℝ)|=(1062546789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11257/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2801/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2251/20000 : ℝ) ^ (4131/1024 : ℝ) ≤ (7446072959768543/50000000000000000000 : ℝ) := by
    have hpowers : (2251/20000 : ℝ)^4131 ≤ (7446072959768543/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2251 : ℕ)^4131*50000000000000000000^1024 ≤ 7446072959768543^1024*20000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2251 20000 7446072959768543 50000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2251/20000 : ℝ)) (X := (7446072959768543/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14007/100000 : ℝ) ^ (4131/1024 : ℝ) ≤ (4498967655270153/12500000000000000000 : ℝ) := by
    have hpowers : (14007/100000 : ℝ)^4131 ≤ (4498967655270153/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14007 : ℕ)^4131*12500000000000000000^1024 ≤ 4498967655270153^1024*100000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14007 100000 4498967655270153 12500000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14007/100000 : ℝ)) (X := (4498967655270153/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007446072959768543/25000000000000000000 : ℝ) ≤ (2000147643182461/2000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (25007446072959768543/25000000000000000000 : ℝ)^1024 ≤ (2000147643182461/2000000000000000 : ℝ)^4131 := by
      have hnat : (25007446072959768543 : ℕ)^1024*2000000000000000^4131 ≤ 2000147643182461^4131*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007446072959768543 25000000000000000000 2000147643182461 2000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000147643182461/2000000000000000 : ℝ)) (X := (25007446072959768543/25000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005088388716169831/10000000000000000000 : ℝ) ≤ (2000252215603601/2000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (10005088388716169831/10000000000000000000 : ℝ)^1024 ≤ (2000252215603601/2000000000000000 : ℝ)^4131 := by
      have hnat : (10005088388716169831 : ℕ)^1024*2000000000000000^4131 ≤ 2000252215603601^4131*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005088388716169831 10000000000000000000 2000252215603601 2000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000252215603601/2000000000000000 : ℝ)) (X := (10005088388716169831/10000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254498967655270153/6250000000000000000 : ℝ) ≤ (2000356788024741/2000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (6254498967655270153/6250000000000000000 : ℝ)^1024 ≤ (2000356788024741/2000000000000000 : ℝ)^4131 := by
      have hnat : (6254498967655270153 : ℕ)^1024*2000000000000000^4131 ≤ 2000356788024741^4131*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254498967655270153 6250000000000000000 2000356788024741 2000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000356788024741/2000000000000000 : ℝ)) (X := (6254498967655270153/6250000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7446072959768543/50000000000000000000 : ℝ) ≤ ((687756548604783909/688000000000000000 : ℝ)+2*(5228621057/2752000000000 : ℝ)*(2251/20000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (687756548604783909/688000000000000000 : ℝ)+2*(5228621057/2752000000000 : ℝ)*(2251/20000 : ℝ)=(2000147643182461/2000000000000000 : ℝ) by norm_num, show 1+2*(7446072959768543/50000000000000000000 : ℝ)=(25007446072959768543/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4498967655270153/12500000000000000000 : ℝ)+(7446072959768543/50000000000000000000 : ℝ) ≤ ((687756548604783909/688000000000000000 : ℝ)+(5228621057/2752000000000 : ℝ)*((14007/100000 : ℝ)+(2251/20000 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (687756548604783909/688000000000000000 : ℝ)+(5228621057/2752000000000 : ℝ)*((14007/100000 : ℝ)+(2251/20000 : ℝ))=(2000252215603601/2000000000000000 : ℝ) by norm_num, show 1+(4498967655270153/12500000000000000000 : ℝ)+(7446072959768543/50000000000000000000 : ℝ)=(10005088388716169831/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4498967655270153/12500000000000000000 : ℝ) ≤ ((687756548604783909/688000000000000000 : ℝ)+2*(5228621057/2752000000000 : ℝ)*(14007/100000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (687756548604783909/688000000000000000 : ℝ)+2*(5228621057/2752000000000 : ℝ)*(14007/100000 : ℝ)=(2000356788024741/2000000000000000 : ℝ) by norm_num, show 1+2*(4498967655270153/12500000000000000000 : ℝ)=(6254498967655270153/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (687756548604783909/688000000000000000 : ℝ)*(X 1 0+X 2 0)+(5228621057/2752000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (687756548604783909/688000000000000000 : ℝ)) (alpha := (5228621057/2752000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (687756548604783909/688000000000000000 : ℝ)*(X 0 1+X 2 1)+(5228621057/2752000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (687756548604783909/688000000000000000 : ℝ)) (alpha := (5228621057/2752000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (687756548604783909/688000000000000000 : ℝ)*(X 0 2+X 1 2)+(5228621057/2752000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (687756548604783909/688000000000000000 : ℝ)) (alpha := (5228621057/2752000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1100901109/5000000000 : ℝ)*X 0 0+(1348569717/2500000000 : ℝ)*X 0 1+(5264532987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068993459/2000000000 : ℝ)*X 1 0+(-113381501/500000000 : ℝ)*X 1 1+(2632266493/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534496731/1000000000 : ℝ)*X 2 0+(5264532991/10000000000 : ℝ)*X 2 1+(-1133814997/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093729419/2500000000 : ℝ)*X 0 0+(10623869/25000000 : ℝ)*X 0 1+(4504033409/10000000000 : ℝ)*X 0 2+(1093729419/2500000000 : ℝ)*X 1 0+(10623869/25000000 : ℝ)*X 1 1+(4504033409/10000000000 : ℝ)*X 1 2+(1093729419/2500000000 : ℝ)*X 2 0+(10623869/25000000 : ℝ)*X 2 1+(4504033409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-220180769/1000000000 : ℝ)*X 0 0+(5264858073/10000000000 : ℝ)*X 0 1+(5393952299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((166008639/312500000 : ℝ)*X 1 0+(-1069105147/5000000000 : ℝ)*X 1 1+(674244091/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664034533/1250000000 : ℝ)*X 2 0+(5393953027/10000000000 : ℝ)*X 2 1+(-427642027/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1093732029/2500000000 : ℝ)*X 0 0+(2251697811/5000000000 : ℝ)*X 0 1+(1062546789/2500000000 : ℝ)*X 0 2+(1093732029/2500000000 : ℝ)*X 1 0+(2251697811/5000000000 : ℝ)*X 1 1+(1062546789/2500000000 : ℝ)*X 1 2+(1093732029/2500000000 : ℝ)*X 2 0+(2251697811/5000000000 : ℝ)*X 2 1+(1062546789/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123756620598599596497470811/17200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1470324531/100000000000000 : ℝ)*(base19) + (344199693/25000000000000 : ℝ)*(base23) + (61550393/100000000000000 : ℝ)*(lower2) + (21382411/12500000000000 : ℝ)*(upper3) + (26146923/20000000000000 : ℝ)*(upper5) + (5818494274512307/100000000000000 : ℝ)*(major0) + (5818494274512307/100000000000000 : ℝ)*(major1) + (5818494274512307/100000000000000 : ℝ)*(major2) + (7707414080417587/100000000000000 : ℝ)*(sp0) + (7707453132430173/100000000000000 : ℝ)*(sp1) + (1926863306488983/25000000000000 : ℝ)*(sp2) + (39295121268447/1000000000000 : ℝ)*(sp3) + (40522337117/100000000000000 : ℝ)*(sp4) + (21579586789/100000000000000 : ℝ)*(sp7) + (392953370643149/10000000000000 : ℝ)*(f.failure) + (481715912672169/6250000000000 : ℝ)*(f.sum) + (1807536008769/688000000000000000000000000 : ℝ)*base66 + (557089718948818063/68800000000000000000000000000000 : ℝ)*base67 + (106615894815981937/68800000000000000000000000000000 : ℝ)*base70 + (358432199601618063/68800000000000000000000000000000 : ℝ)*base71 + (3578523405471/688000000000000000000000000 : ℝ)*base73 + (477595024035218063/68800000000000000000000000000000 : ℝ)*base75 + (944306106713618063/68800000000000000000000000000000 : ℝ)*base77 + (413194136764818063/68800000000000000000000000000000 : ℝ)*base79 + (4308347860993/688000000000000000000000000 : ℝ)*base82 + (7125921/500000000000000000000 : ℝ)*base89 + (7125921/500000000000000000000 : ℝ)*base91 + (7125921/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (277611568971894838545093/268750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117950653/10000000000000 : ℝ)*(base19) + (623362589/50000000000000 : ℝ)*(base23) + (219629637/50000000000000 : ℝ)*(lower1) + (99297349/100000000000000 : ℝ)*(upper2) + (109085051/25000000000000 : ℝ)*(upper3) + (158598571/100000000000000 : ℝ)*(upper5) + (91371327645841/1562500000000 : ℝ)*(major0) + (91371327645841/1562500000000 : ℝ)*(major1) + (91371327645841/1562500000000 : ℝ)*(major2) + (6036945761/25000000000000 : ℝ)*(sp2) + (1936557041412193/25000000000000 : ℝ)*(sp4) + (7746226986142241/100000000000000 : ℝ)*(sp5) + (154924055422811/2000000000000 : ℝ)*(sp6) + (246831358661651/6250000000000 : ℝ)*(sp7) + (246831358661651/6250000000000 : ℝ)*(f.failure) + (1936557041412193/25000000000000 : ℝ)*(f.sum) + (100632152243/10750000000000000000000000 : ℝ)*base65 + (4525397830722469/1075000000000000000000000000000 : ℝ)*base67 + (60719354231477531/1075000000000000000000000000000 : ℝ)*base70 + (11791747331022469/1075000000000000000000000000000 : ℝ)*base71 + (76494938563/21500000000000000000000000 : ℝ)*base73 + (11862434902022469/1075000000000000000000000000000 : ℝ)*base75 + (24817568693622469/1075000000000000000000000000000 : ℝ)*base77 + (207538750372469/1075000000000000000000000000000 : ℝ)*base79 + (28404807161/4300000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2366721/312500000000000000000 : ℝ)*base90 + (2366721/312500000000000000000 : ℝ)*base92 + (2366721/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1070_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1070_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1070_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1070_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1070_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1070_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1070_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
