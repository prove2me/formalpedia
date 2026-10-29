-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1379_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:50.858849+00:00
-- url     : https://prove2.me/submissions/62d0ce49-50c3-4ab9-a231-b531fd3a0001

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
theorem support_rectangle_w1379_s6_0 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2012428763/10000000000 : ℝ)*x 0 + (5410807443/10000000000 : ℝ)*x 1 + (5245668501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2012428763/10000000000 : ℝ)^4339 ≤ (6132118274017/50000000000000 : ℝ)^3315 := by
    have hnat : (2012428763 : ℕ)^4339*50000000000000^3315 ≤ 6132118274017^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012428763 10000000000 6132118274017 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410807443/10000000000 : ℝ)^4339 ≤ (4475762327571/10000000000000 : ℝ)^3315 := by
    have hnat : (5410807443 : ℕ)^4339*10000000000000^3315 ≤ 4475762327571^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410807443 10000000000 4475762327571 10000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245668501/10000000000 : ℝ)^4339 ≤ (21489070081149/50000000000000 : ℝ)^3315 := by
    have hnat : (5245668501 : ℕ)^4339*50000000000000^3315 ≤ 21489070081149^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245668501 10000000000 21489070081149 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2012428763/10000000000 : ℝ), (5410807443/10000000000 : ℝ), (5245668501/10000000000 : ℝ)] ![(6132118274017/50000000000000 : ℝ), (4475762327571/10000000000000 : ℝ), (21489070081149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2012428763/10000000000 : ℝ)|^4339 ≤ (6132118274017/50000000000000 : ℝ)^3315
        have hw : |(-2012428763/10000000000 : ℝ)|=(2012428763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410807443/10000000000 : ℝ)|^4339 ≤ (4475762327571/10000000000000 : ℝ)^3315
        have hw : |(5410807443/10000000000 : ℝ)|=(5410807443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245668501/10000000000 : ℝ)|^4339 ≤ (21489070081149/50000000000000 : ℝ)^3315
        have hw : |(5245668501/10000000000 : ℝ)|=(5245668501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s6_1 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855733/1600000 : ℝ)*x 0 + (-2096540009/10000000000 : ℝ)*x 1 + (2622834251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855733/1600000 : ℝ)^4339 ≤ (22041199269341/50000000000000 : ℝ)^3315 := by
    have hnat : (855733 : ℕ)^4339*50000000000000^3315 ≤ 22041199269341^3315*1600000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855733 1600000 22041199269341 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2096540009/10000000000 : ℝ)^4339 ≤ (6469730641309/50000000000000 : ℝ)^3315 := by
    have hnat : (2096540009 : ℕ)^4339*50000000000000^3315 ≤ 6469730641309^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096540009 10000000000 6469730641309 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622834251/5000000000 : ℝ)^4339 ≤ (21489070086511/50000000000000 : ℝ)^3315 := by
    have hnat : (2622834251 : ℕ)^4339*50000000000000^3315 ≤ 21489070086511^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622834251 5000000000 21489070086511 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855733/1600000 : ℝ), (-2096540009/10000000000 : ℝ), (2622834251/5000000000 : ℝ)] ![(22041199269341/50000000000000 : ℝ), (6469730641309/50000000000000 : ℝ), (21489070086511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855733/1600000 : ℝ)|^4339 ≤ (22041199269341/50000000000000 : ℝ)^3315
        have hw : |(855733/1600000 : ℝ)|=(855733/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2096540009/10000000000 : ℝ)|^4339 ≤ (6469730641309/50000000000000 : ℝ)^3315
        have hw : |(-2096540009/10000000000 : ℝ)|=(2096540009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622834251/5000000000 : ℝ)|^4339 ≤ (21489070086511/50000000000000 : ℝ)^3315
        have hw : |(2622834251/5000000000 : ℝ)|=(2622834251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s6_2 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337082813/2500000000 : ℝ)*x 0 + (5245668501/10000000000 : ℝ)*x 1 + (-2096540007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337082813/2500000000 : ℝ)^4339 ≤ (22041199280129/50000000000000 : ℝ)^3315 := by
    have hnat : (1337082813 : ℕ)^4339*50000000000000^3315 ≤ 22041199280129^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337082813 2500000000 22041199280129 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245668501/10000000000 : ℝ)^4339 ≤ (21489070081149/50000000000000 : ℝ)^3315 := by
    have hnat : (5245668501 : ℕ)^4339*50000000000000^3315 ≤ 21489070081149^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245668501 10000000000 21489070081149 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096540007/10000000000 : ℝ)^4339 ≤ (12939461266461/100000000000000 : ℝ)^3315 := by
    have hnat : (2096540007 : ℕ)^4339*100000000000000^3315 ≤ 12939461266461^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096540007 10000000000 12939461266461 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337082813/2500000000 : ℝ), (5245668501/10000000000 : ℝ), (-2096540007/10000000000 : ℝ)] ![(22041199280129/50000000000000 : ℝ), (21489070081149/50000000000000 : ℝ), (12939461266461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337082813/2500000000 : ℝ)|^4339 ≤ (22041199280129/50000000000000 : ℝ)^3315
        have hw : |(1337082813/2500000000 : ℝ)|=(1337082813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245668501/10000000000 : ℝ)|^4339 ≤ (21489070081149/50000000000000 : ℝ)^3315
        have hw : |(5245668501/10000000000 : ℝ)|=(5245668501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2096540007/10000000000 : ℝ)|^4339 ≤ (12939461266461/100000000000000 : ℝ)^3315
        have hw : |(-2096540007/10000000000 : ℝ)|=(2096540007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s6_3 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4317035971/10000000000 : ℝ)*x 0 + (2072475981/5000000000 : ℝ)*x 1 + (1123917177/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317035971/10000000000 : ℝ)^4339 ≤ (33303885532181/100000000000000 : ℝ)^3315 := by
    have hnat : (4317035971 : ℕ)^4339*100000000000000^3315 ≤ 33303885532181^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317035971 10000000000 33303885532181 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072475981/5000000000 : ℝ)^4339 ≤ (789426476761/2500000000000 : ℝ)^3315 := by
    have hnat : (2072475981 : ℕ)^4339*2500000000000^3315 ≤ 789426476761^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072475981 5000000000 789426476761 2500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123917177/2500000000 : ℝ)^4339 ≤ (8779763843779/25000000000000 : ℝ)^3315 := by
    have hnat : (1123917177 : ℕ)^4339*25000000000000^3315 ≤ 8779763843779^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123917177 2500000000 8779763843779 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317035971/10000000000 : ℝ), (2072475981/5000000000 : ℝ), (1123917177/2500000000 : ℝ)] ![(33303885532181/100000000000000 : ℝ), (789426476761/2500000000000 : ℝ), (8779763843779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317035971/10000000000 : ℝ)|^4339 ≤ (33303885532181/100000000000000 : ℝ)^3315
        have hw : |(4317035971/10000000000 : ℝ)|=(4317035971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2072475981/5000000000 : ℝ)|^4339 ≤ (789426476761/2500000000000 : ℝ)^3315
        have hw : |(2072475981/5000000000 : ℝ)|=(2072475981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123917177/2500000000 : ℝ)|^4339 ≤ (8779763843779/25000000000000 : ℝ)^3315
        have hw : |(1123917177/2500000000 : ℝ)|=(1123917177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s6_4 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006220283/5000000000 : ℝ)*x 0 + (5246261577/10000000000 : ℝ)*x 1 + (5410211303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006220283/5000000000 : ℝ)^4339 ≤ (1226433069773/10000000000000 : ℝ)^3315 := by
    have hnat : (1006220283 : ℕ)^4339*10000000000000^3315 ≤ 1226433069773^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006220283 5000000000 1226433069773 10000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246261577/10000000000 : ℝ)^4339 ≤ (42984500363089/100000000000000 : ℝ)^3315 := by
    have hnat : (5246261577 : ℕ)^4339*100000000000000^3315 ≤ 42984500363089^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246261577 10000000000 42984500363089 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410211303/10000000000 : ℝ)^4339 ≤ (44751168934393/100000000000000 : ℝ)^3315 := by
    have hnat : (5410211303 : ℕ)^4339*100000000000000^3315 ≤ 44751168934393^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410211303 10000000000 44751168934393 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006220283/5000000000 : ℝ), (5246261577/10000000000 : ℝ), (5410211303/10000000000 : ℝ)] ![(1226433069773/10000000000000 : ℝ), (42984500363089/100000000000000 : ℝ), (44751168934393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006220283/5000000000 : ℝ)|^4339 ≤ (1226433069773/10000000000000 : ℝ)^3315
        have hw : |(-1006220283/5000000000 : ℝ)|=(1006220283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246261577/10000000000 : ℝ)|^4339 ≤ (42984500363089/100000000000000 : ℝ)^3315
        have hw : |(5246261577/10000000000 : ℝ)|=(5246261577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410211303/10000000000 : ℝ)|^4339 ≤ (44751168934393/100000000000000 : ℝ)^3315
        have hw : |(5410211303/10000000000 : ℝ)|=(5410211303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s6_5 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305619389/10000000000 : ℝ)*x 0 + (-1931997203/10000000000 : ℝ)*x 1 + (1352552827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305619389/10000000000 : ℝ)^4339 ≤ (8724435909561/20000000000000 : ℝ)^3315 := by
    have hnat : (5305619389 : ℕ)^4339*20000000000000^3315 ≤ 8724435909561^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305619389 10000000000 8724435909561 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931997203/10000000000 : ℝ)^4339 ≤ (5813325722669/50000000000000 : ℝ)^3315 := by
    have hnat : (1931997203 : ℕ)^4339*50000000000000^3315 ≤ 5813325722669^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931997203 10000000000 5813325722669 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352552827/2500000000 : ℝ)^4339 ≤ (44751168988527/100000000000000 : ℝ)^3315 := by
    have hnat : (1352552827 : ℕ)^4339*100000000000000^3315 ≤ 44751168988527^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352552827 2500000000 44751168988527 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305619389/10000000000 : ℝ), (-1931997203/10000000000 : ℝ), (1352552827/2500000000 : ℝ)] ![(8724435909561/20000000000000 : ℝ), (5813325722669/50000000000000 : ℝ), (44751168988527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305619389/10000000000 : ℝ)|^4339 ≤ (8724435909561/20000000000000 : ℝ)^3315
        have hw : |(5305619389/10000000000 : ℝ)|=(5305619389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1931997203/10000000000 : ℝ)|^4339 ≤ (5813325722669/50000000000000 : ℝ)^3315
        have hw : |(-1931997203/10000000000 : ℝ)|=(1931997203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352552827/2500000000 : ℝ)|^4339 ≤ (44751168988527/100000000000000 : ℝ)^3315
        have hw : |(1352552827/2500000000 : ℝ)|=(1352552827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s6_6 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530561939/1000000000 : ℝ)*x 0 + (1352552827/2500000000 : ℝ)*x 1 + (-965998601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530561939/1000000000 : ℝ)^4339 ≤ (21811089779283/50000000000000 : ℝ)^3315 := by
    have hnat : (530561939 : ℕ)^4339*50000000000000^3315 ≤ 21811089779283^3315*1000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530561939 1000000000 21811089779283 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352552827/2500000000 : ℝ)^4339 ≤ (44751168988527/100000000000000 : ℝ)^3315 := by
    have hnat : (1352552827 : ℕ)^4339*100000000000000^3315 ≤ 44751168988527^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352552827 2500000000 44751168988527 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965998601/5000000000 : ℝ)^4339 ≤ (11626651437461/100000000000000 : ℝ)^3315 := by
    have hnat : (965998601 : ℕ)^4339*100000000000000^3315 ≤ 11626651437461^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965998601 5000000000 11626651437461 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530561939/1000000000 : ℝ), (1352552827/2500000000 : ℝ), (-965998601/5000000000 : ℝ)] ![(21811089779283/50000000000000 : ℝ), (44751168988527/100000000000000 : ℝ), (11626651437461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530561939/1000000000 : ℝ)|^4339 ≤ (21811089779283/50000000000000 : ℝ)^3315
        have hw : |(530561939/1000000000 : ℝ)|=(530561939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352552827/2500000000 : ℝ)|^4339 ≤ (44751168988527/100000000000000 : ℝ)^3315
        have hw : |(1352552827/2500000000 : ℝ)|=(1352552827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-965998601/5000000000 : ℝ)|^4339 ≤ (11626651437461/100000000000000 : ℝ)^3315
        have hw : |(-965998601/5000000000 : ℝ)|=(965998601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s6_7 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53963263/125000000 : ℝ)*x 0 + (4494409149/10000000000 : ℝ)*x 1 + (4146218021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53963263/125000000 : ℝ)^4339 ≤ (16652069333753/50000000000000 : ℝ)^3315 := by
    have hnat : (53963263 : ℕ)^4339*50000000000000^3315 ≤ 16652069333753^3315*125000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53963263 125000000 16652069333753 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494409149/10000000000 : ℝ)^4339 ≤ (17553088599439/50000000000000 : ℝ)^3315 := by
    have hnat : (4494409149 : ℕ)^4339*50000000000000^3315 ≤ 17553088599439^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494409149 10000000000 17553088599439 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146218021/10000000000 : ℝ)^4339 ≤ (3948710513673/12500000000000 : ℝ)^3315 := by
    have hnat : (4146218021 : ℕ)^4339*12500000000000^3315 ≤ 3948710513673^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146218021 10000000000 3948710513673 12500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53963263/125000000 : ℝ), (4494409149/10000000000 : ℝ), (4146218021/10000000000 : ℝ)] ![(16652069333753/50000000000000 : ℝ), (17553088599439/50000000000000 : ℝ), (3948710513673/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53963263/125000000 : ℝ)|^4339 ≤ (16652069333753/50000000000000 : ℝ)^3315
        have hw : |(53963263/125000000 : ℝ)|=(53963263/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494409149/10000000000 : ℝ)|^4339 ≤ (17553088599439/50000000000000 : ℝ)^3315
        have hw : |(4494409149/10000000000 : ℝ)|=(4494409149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4146218021/10000000000 : ℝ)|^4339 ≤ (3948710513673/12500000000000 : ℝ)^3315
        have hw : |(4146218021/10000000000 : ℝ)|=(4146218021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1379_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11233/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1473/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2807/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2807/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2807/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2807/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2807/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2807/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2807/25000 : ℝ) ^ (2169/512 : ℝ) ≤ (4739574650500999/50000000000000000000 : ℝ) := by
    have hpowers : (2807/25000 : ℝ)^2169 ≤ (4739574650500999/50000000000000000000 : ℝ)^512 := by
      have hnat : (2807 : ℕ)^2169*50000000000000000000^512 ≤ 4739574650500999^512*25000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2807 25000 4739574650500999 50000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2807/25000 : ℝ)) (X := (4739574650500999/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hpowhi : (921/6250 : ℝ) ^ (2169/512 : ℝ) ≤ (29990462589160141/100000000000000000000 : ℝ) := by
    have hpowers : (921/6250 : ℝ)^2169 ≤ (29990462589160141/100000000000000000000 : ℝ)^512 := by
      have hnat : (921 : ℕ)^2169*100000000000000000000^512 ≤ 29990462589160141^512*6250^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        921 6250 29990462589160141 100000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (921/6250 : ℝ)) (X := (29990462589160141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004739574650500999/25000000000000000000 : ℝ) ≤ (10000447484834001/10000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (25004739574650500999/25000000000000000000 : ℝ)^512 ≤ (10000447484834001/10000000000000000 : ℝ)^2169 := by
      have hnat : (25004739574650500999 : ℕ)^512*10000000000000000^2169 ≤ 10000447484834001^2169*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004739574650500999 25000000000000000000 10000447484834001 10000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000447484834001/10000000000000000 : ℝ)) (X := (25004739574650500999/25000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039469611890162139/100000000000000000000 : ℝ) ≤ (10000931553494793/10000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (100039469611890162139/100000000000000000000 : ℝ)^512 ≤ (10000931553494793/10000000000000000 : ℝ)^2169 := by
      have hnat : (100039469611890162139 : ℕ)^512*10000000000000000^2169 ≤ 10000931553494793^2169*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039469611890162139 100000000000000000000 10000931553494793 10000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000931553494793/10000000000000000 : ℝ)) (X := (100039469611890162139/100000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029990462589160141/50000000000000000000 : ℝ) ≤ (2000283124431117/2000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (50029990462589160141/50000000000000000000 : ℝ)^512 ≤ (2000283124431117/2000000000000000 : ℝ)^2169 := by
      have hnat : (50029990462589160141 : ℕ)^512*2000000000000000^2169 ≤ 2000283124431117^2169*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029990462589160141 50000000000000000000 2000283124431117 2000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000283124431117/2000000000000000 : ℝ)) (X := (50029990462589160141/50000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4739574650500999/50000000000000000000 : ℝ) ≤ ((8767674882737732589/8770000000000000000 : ℝ)+2*(60508582599/43850000000000 : ℝ)*(2807/25000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (8767674882737732589/8770000000000000000 : ℝ)+2*(60508582599/43850000000000 : ℝ)*(2807/25000 : ℝ)=(10000447484834001/10000000000000000 : ℝ) by norm_num, show 1+2*(4739574650500999/50000000000000000000 : ℝ)=(25004739574650500999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29990462589160141/100000000000000000000 : ℝ)+(4739574650500999/50000000000000000000 : ℝ) ≤ ((8767674882737732589/8770000000000000000 : ℝ)+(60508582599/43850000000000 : ℝ)*((921/6250 : ℝ)+(2807/25000 : ℝ)))^(2169/512 : ℝ) := by
    rw [show (8767674882737732589/8770000000000000000 : ℝ)+(60508582599/43850000000000 : ℝ)*((921/6250 : ℝ)+(2807/25000 : ℝ))=(10000931553494793/10000000000000000 : ℝ) by norm_num, show 1+(29990462589160141/100000000000000000000 : ℝ)+(4739574650500999/50000000000000000000 : ℝ)=(100039469611890162139/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29990462589160141/100000000000000000000 : ℝ) ≤ ((8767674882737732589/8770000000000000000 : ℝ)+2*(60508582599/43850000000000 : ℝ)*(921/6250 : ℝ))^(2169/512 : ℝ) := by
    rw [show (8767674882737732589/8770000000000000000 : ℝ)+2*(60508582599/43850000000000 : ℝ)*(921/6250 : ℝ)=(2000283124431117/2000000000000000 : ℝ) by norm_num, show 1+2*(29990462589160141/100000000000000000000 : ℝ)=(50029990462589160141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8767674882737732589/8770000000000000000 : ℝ)*(X 1 0+X 2 0)+(60508582599/43850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (2807/25000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (8767674882737732589/8770000000000000000 : ℝ)) (alpha := (60508582599/43850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8767674882737732589/8770000000000000000 : ℝ)*(X 0 1+X 2 1)+(60508582599/43850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (2807/25000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (8767674882737732589/8770000000000000000 : ℝ)) (alpha := (60508582599/43850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8767674882737732589/8770000000000000000 : ℝ)*(X 0 2+X 1 2)+(60508582599/43850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (2807/25000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (8767674882737732589/8770000000000000000 : ℝ)) (alpha := (60508582599/43850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2012428763/10000000000 : ℝ)*X 0 0+(5410807443/10000000000 : ℝ)*X 0 1+(5245668501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((855733/1600000 : ℝ)*X 1 0+(-2096540009/10000000000 : ℝ)*X 1 1+(2622834251/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337082813/2500000000 : ℝ)*X 2 0+(5245668501/10000000000 : ℝ)*X 2 1+(-2096540007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317035971/10000000000 : ℝ)*X 0 0+(2072475981/5000000000 : ℝ)*X 0 1+(1123917177/2500000000 : ℝ)*X 0 2+(4317035971/10000000000 : ℝ)*X 1 0+(2072475981/5000000000 : ℝ)*X 1 1+(1123917177/2500000000 : ℝ)*X 1 2+(4317035971/10000000000 : ℝ)*X 2 0+(2072475981/5000000000 : ℝ)*X 2 1+(1123917177/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1006220283/5000000000 : ℝ)*X 0 0+(5246261577/10000000000 : ℝ)*X 0 1+(5410211303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305619389/10000000000 : ℝ)*X 1 0+(-1931997203/10000000000 : ℝ)*X 1 1+(1352552827/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530561939/1000000000 : ℝ)*X 2 0+(1352552827/2500000000 : ℝ)*X 2 1+(-965998601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((53963263/125000000 : ℝ)*X 0 0+(4494409149/10000000000 : ℝ)*X 0 1+(4146218021/10000000000 : ℝ)*X 0 2+(53963263/125000000 : ℝ)*X 1 0+(4494409149/10000000000 : ℝ)*X 1 1+(4146218021/10000000000 : ℝ)*X 1 2+(53963263/125000000 : ℝ)*X 2 0+(4494409149/10000000000 : ℝ)*X 2 1+(4146218021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187436853670658522709230691/21925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (198310921/12500000000000 : ℝ)*(base19) + (1481932511/100000000000000 : ℝ)*(base23) + (14282629/25000000000000 : ℝ)*(lower2) + (214154859/100000000000000 : ℝ)*(upper3) + (69189799/50000000000000 : ℝ)*(upper5) + (445345486626173/10000000000000 : ℝ)*(major0) + (445345486626173/10000000000000 : ℝ)*(major1) + (445345486626173/10000000000000 : ℝ)*(major2) + (302777052523687/5000000000000 : ℝ)*(sp0) + (3027786162957591/50000000000000 : ℝ)*(sp1) + (6055572430470039/100000000000000 : ℝ)*(sp2) + (2851318835809129/100000000000000 : ℝ)*(sp3) + (32861928809/100000000000000 : ℝ)*(sp4) + (2087418133/12500000000000 : ℝ)*(sp7) + (2851335535154193/100000000000000 : ℝ)*(f.failure) + (121111478248051/2000000000000 : ℝ)*(f.sum) + (2483970784977/877000000000000000000000000 : ℝ)*base66 + (20125400454048103/87700000000000000000000000000000 : ℝ)*base68 + (423024049913248103/87700000000000000000000000000000 : ℝ)*base70 + (90439144868448103/87700000000000000000000000000000 : ℝ)*base72 + (155837582877/109625000000000000000000000 : ℝ)*base73 + (1182699472000148103/87700000000000000000000000000000 : ℝ)*base76 + (445116574665951897/87700000000000000000000000000000 : ℝ)*base77 + (1631386891064248103/87700000000000000000000000000000 : ℝ)*base80 + (3427488689923/877000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (60339919/10000000000000000000000 : ℝ)*base89 + (60339919/10000000000000000000000 : ℝ)*base91 + (60339919/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206755616525394759275723649/27406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (325081419/25000000000000 : ℝ)*(base19) + (1414375123/100000000000000 : ℝ)*(base23) + (39131811/25000000000000 : ℝ)*(upper3) + (51008509/100000000000000 : ℝ)*(lower4) + (157411097/100000000000000 : ℝ)*(upper5) + (280356733208347/6250000000000 : ℝ)*(major0) + (280356733208347/6250000000000 : ℝ)*(major1) + (280356733208347/6250000000000 : ℝ)*(major2) + (6736005207/25000000000000 : ℝ)*(sp1) + (5805168211/20000000000000 : ℝ)*(sp2) + (3049714849551579/50000000000000 : ℝ)*(sp4) + (3049700727378327/50000000000000 : ℝ)*(sp5) + (6099399258886979/100000000000000 : ℝ)*(sp6) + (574397102418757/20000000000000 : ℝ)*(sp7) + (574397102418757/20000000000000 : ℝ)*(f.failure) + (3049714849551579/50000000000000 : ℝ)*(f.sum) + (5095923145269/1096250000000000000000000000 : ℝ)*base65 + (362133421488617117/54812500000000000000000000000000 : ℝ)*base68 + (947711541173367117/54812500000000000000000000000000 : ℝ)*base70 + (23435425762945383/54812500000000000000000000000000 : ℝ)*base71 + (9099492410161/4385000000000000000000000000 : ℝ)*base73 + (956262741403242117/54812500000000000000000000000000 : ℝ)*base76 + (23683277332554617/54812500000000000000000000000000 : ℝ)*base78 + (660059030404070383/54812500000000000000000000000000 : ℝ)*base79 + (11830830395687/2192500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4699931/2000000000000000000000 : ℝ)*base89 + (4699931/2000000000000000000000 : ℝ)*base91 + (4699931/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1379_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1379_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1379_s7_0 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2012435401/10000000000 : ℝ)*x 0 + (216430531/400000000 : ℝ)*x 1 + (1311427039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2012435401/10000000000 : ℝ)^4339 ≤ (766518093609/6250000000000 : ℝ)^3315 := by
    have hnat : (2012435401 : ℕ)^4339*6250000000000^3315 ≤ 766518093609^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012435401 10000000000 766518093609 6250000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216430531/400000000 : ℝ)^4339 ≤ (44757145066163/100000000000000 : ℝ)^3315 := by
    have hnat : (216430531 : ℕ)^4339*100000000000000^3315 ≤ 44757145066163^3315*400000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216430531 400000000 44757145066163 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311427039/2500000000 : ℝ)^4339 ≤ (2686160338699/6250000000000 : ℝ)^3315 := by
    have hnat : (1311427039 : ℕ)^4339*6250000000000^3315 ≤ 2686160338699^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311427039 2500000000 2686160338699 6250000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2012435401/10000000000 : ℝ), (216430531/400000000 : ℝ), (1311427039/2500000000 : ℝ)] ![(766518093609/6250000000000 : ℝ), (44757145066163/100000000000000 : ℝ), (2686160338699/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2012435401/10000000000 : ℝ)|^4339 ≤ (766518093609/6250000000000 : ℝ)^3315
        have hw : |(-2012435401/10000000000 : ℝ)|=(2012435401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216430531/400000000 : ℝ)|^4339 ≤ (44757145066163/100000000000000 : ℝ)^3315
        have hw : |(216430531/400000000 : ℝ)|=(216430531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311427039/2500000000 : ℝ)|^4339 ≤ (2686160338699/6250000000000 : ℝ)^3315
        have hw : |(1311427039/2500000000 : ℝ)|=(1311427039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s7_1 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348319399/10000000000 : ℝ)*x 0 + (-2096503187/10000000000 : ℝ)*x 1 + (5245708161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348319399/10000000000 : ℝ)^4339 ≤ (2755141917911/6250000000000 : ℝ)^3315 := by
    have hnat : (5348319399 : ℕ)^4339*6250000000000^3315 ≤ 2755141917911^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348319399 10000000000 2755141917911 6250000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2096503187/10000000000 : ℝ)^4339 ≤ (12939163824823/100000000000000 : ℝ)^3315 := by
    have hnat : (2096503187 : ℕ)^4339*100000000000000^3315 ≤ 12939163824823^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096503187 10000000000 12939163824823 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245708161/10000000000 : ℝ)^4339 ≤ (10744641368201/25000000000000 : ℝ)^3315 := by
    have hnat : (5245708161 : ℕ)^4339*25000000000000^3315 ≤ 10744641368201^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245708161 10000000000 10744641368201 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348319399/10000000000 : ℝ), (-2096503187/10000000000 : ℝ), (5245708161/10000000000 : ℝ)] ![(2755141917911/6250000000000 : ℝ), (12939163824823/100000000000000 : ℝ), (10744641368201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348319399/10000000000 : ℝ)|^4339 ≤ (2755141917911/6250000000000 : ℝ)^3315
        have hw : |(5348319399/10000000000 : ℝ)|=(5348319399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2096503187/10000000000 : ℝ)|^4339 ≤ (12939163824823/100000000000000 : ℝ)^3315
        have hw : |(-2096503187/10000000000 : ℝ)|=(2096503187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245708161/10000000000 : ℝ)|^4339 ≤ (10744641368201/25000000000000 : ℝ)^3315
        have hw : |(5245708161/10000000000 : ℝ)|=(5245708161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s7_2 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069663881/2000000000 : ℝ)*x 0 + (5245708143/10000000000 : ℝ)*x 1 + (-524125801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069663881/2000000000 : ℝ)^4339 ≤ (22041135375653/50000000000000 : ℝ)^3315 := by
    have hnat : (1069663881 : ℕ)^4339*50000000000000^3315 ≤ 22041135375653^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069663881 2000000000 22041135375653 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245708143/10000000000 : ℝ)^4339 ≤ (42978565279773/100000000000000 : ℝ)^3315 := by
    have hnat : (5245708143 : ℕ)^4339*100000000000000^3315 ≤ 42978565279773^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245708143 10000000000 42978565279773 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524125801/2500000000 : ℝ)^4339 ≤ (12939163962153/100000000000000 : ℝ)^3315 := by
    have hnat : (524125801 : ℕ)^4339*100000000000000^3315 ≤ 12939163962153^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524125801 2500000000 12939163962153 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069663881/2000000000 : ℝ), (5245708143/10000000000 : ℝ), (-524125801/2500000000 : ℝ)] ![(22041135375653/50000000000000 : ℝ), (42978565279773/100000000000000 : ℝ), (12939163962153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069663881/2000000000 : ℝ)|^4339 ≤ (22041135375653/50000000000000 : ℝ)^3315
        have hw : |(1069663881/2000000000 : ℝ)|=(1069663881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245708143/10000000000 : ℝ)|^4339 ≤ (42978565279773/100000000000000 : ℝ)^3315
        have hw : |(5245708143/10000000000 : ℝ)|=(5245708143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524125801/2500000000 : ℝ)|^4339 ≤ (12939163962153/100000000000000 : ℝ)^3315
        have hw : |(-524125801/2500000000 : ℝ)|=(524125801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s7_3 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4317038993/10000000000 : ℝ)*x 0 + (518130063/1250000000 : ℝ)*x 1 + (280973711/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317038993/10000000000 : ℝ)^4339 ≤ (16651958023467/50000000000000 : ℝ)^3315 := by
    have hnat : (4317038993 : ℕ)^4339*50000000000000^3315 ≤ 16651958023467^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317038993 10000000000 16651958023467 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518130063/1250000000 : ℝ)^4339 ≤ (31577941965437/100000000000000 : ℝ)^3315 := by
    have hnat : (518130063 : ℕ)^4339*100000000000000^3315 ≤ 31577941965437^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518130063 1250000000 31577941965437 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280973711/625000000 : ℝ)^4339 ≤ (35118141976461/100000000000000 : ℝ)^3315 := by
    have hnat : (280973711 : ℕ)^4339*100000000000000^3315 ≤ 35118141976461^3315*625000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280973711 625000000 35118141976461 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317038993/10000000000 : ℝ), (518130063/1250000000 : ℝ), (280973711/625000000 : ℝ)] ![(16651958023467/50000000000000 : ℝ), (31577941965437/100000000000000 : ℝ), (35118141976461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317038993/10000000000 : ℝ)|^4339 ≤ (16651958023467/50000000000000 : ℝ)^3315
        have hw : |(4317038993/10000000000 : ℝ)|=(4317038993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518130063/1250000000 : ℝ)|^4339 ≤ (31577941965437/100000000000000 : ℝ)^3315
        have hw : |(518130063/1250000000 : ℝ)|=(518130063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280973711/625000000 : ℝ)|^4339 ≤ (35118141976461/100000000000000 : ℝ)^3315
        have hw : |(280973711/625000000 : ℝ)|=(280973711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s7_4 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-503111779/2500000000 : ℝ)*x 0 + (5246300553/10000000000 : ℝ)*x 1 + (1352541967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503111779/2500000000 : ℝ)^4339 ≤ (613219147279/5000000000000 : ℝ)^3315 := by
    have hnat : (503111779 : ℕ)^4339*5000000000000^3315 ≤ 613219147279^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503111779 2500000000 613219147279 5000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246300553/10000000000 : ℝ)^4339 ≤ (1719396734121/4000000000000 : ℝ)^3315 := by
    have hnat : (5246300553 : ℕ)^4339*4000000000000^3315 ≤ 1719396734121^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246300553 10000000000 1719396734121 4000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352541967/2500000000 : ℝ)^4339 ≤ (44750698677077/100000000000000 : ℝ)^3315 := by
    have hnat : (1352541967 : ℕ)^4339*100000000000000^3315 ≤ 44750698677077^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352541967 2500000000 44750698677077 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-503111779/2500000000 : ℝ), (5246300553/10000000000 : ℝ), (1352541967/2500000000 : ℝ)] ![(613219147279/5000000000000 : ℝ), (1719396734121/4000000000000 : ℝ), (44750698677077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-503111779/2500000000 : ℝ)|^4339 ≤ (613219147279/5000000000000 : ℝ)^3315
        have hw : |(-503111779/2500000000 : ℝ)|=(503111779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246300553/10000000000 : ℝ)|^4339 ≤ (1719396734121/4000000000000 : ℝ)^3315
        have hw : |(5246300553/10000000000 : ℝ)|=(5246300553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352541967/2500000000 : ℝ)|^4339 ≤ (44750698677077/100000000000000 : ℝ)^3315
        have hw : |(1352541967/2500000000 : ℝ)|=(1352541967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s7_5 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305629211/10000000000 : ℝ)*x 0 + (-30188183/156250000 : ℝ)*x 1 + (5410167709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305629211/10000000000 : ℝ)^4339 ≤ (21811142624201/50000000000000 : ℝ)^3315 := by
    have hnat : (5305629211 : ℕ)^4339*50000000000000^3315 ≤ 21811142624201^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305629211 10000000000 21811142624201 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30188183/156250000 : ℝ)^4339 ≤ (1453377224069/12500000000000 : ℝ)^3315 := by
    have hnat : (30188183 : ℕ)^4339*12500000000000^3315 ≤ 1453377224069^3315*156250000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30188183 156250000 1453377224069 12500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410167709/10000000000 : ℝ)^4339 ≤ (8950139391127/20000000000000 : ℝ)^3315 := by
    have hnat : (5410167709 : ℕ)^4339*20000000000000^3315 ≤ 8950139391127^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410167709 10000000000 8950139391127 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305629211/10000000000 : ℝ), (-30188183/156250000 : ℝ), (5410167709/10000000000 : ℝ)] ![(21811142624201/50000000000000 : ℝ), (1453377224069/12500000000000 : ℝ), (8950139391127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305629211/10000000000 : ℝ)|^4339 ≤ (21811142624201/50000000000000 : ℝ)^3315
        have hw : |(5305629211/10000000000 : ℝ)|=(5305629211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30188183/156250000 : ℝ)|^4339 ≤ (1453377224069/12500000000000 : ℝ)^3315
        have hw : |(-30188183/156250000 : ℝ)|=(30188183/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410167709/10000000000 : ℝ)|^4339 ≤ (8950139391127/20000000000000 : ℝ)^3315
        have hw : |(5410167709/10000000000 : ℝ)|=(5410167709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s7_6 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305628971/10000000000 : ℝ)*x 0 + (1352542031/2500000000 : ℝ)*x 1 + (-1932043467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305628971/10000000000 : ℝ)^4339 ≤ (43622282665613/100000000000000 : ℝ)^3315 := by
    have hnat : (5305628971 : ℕ)^4339*100000000000000^3315 ≤ 43622282665613^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305628971 10000000000 43622282665613 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352542031/2500000000 : ℝ)^4339 ≤ (22375350724353/50000000000000 : ℝ)^3315 := by
    have hnat : (1352542031 : ℕ)^4339*50000000000000^3315 ≤ 22375350724353^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352542031 2500000000 22375350724353 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1932043467/10000000000 : ℝ)^4339 ≤ (5813507931351/50000000000000 : ℝ)^3315 := by
    have hnat : (1932043467 : ℕ)^4339*50000000000000^3315 ≤ 5813507931351^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932043467 10000000000 5813507931351 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305628971/10000000000 : ℝ), (1352542031/2500000000 : ℝ), (-1932043467/10000000000 : ℝ)] ![(43622282665613/100000000000000 : ℝ), (22375350724353/50000000000000 : ℝ), (5813507931351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305628971/10000000000 : ℝ)|^4339 ≤ (43622282665613/100000000000000 : ℝ)^3315
        have hw : |(5305628971/10000000000 : ℝ)|=(5305628971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352542031/2500000000 : ℝ)|^4339 ≤ (22375350724353/50000000000000 : ℝ)^3315
        have hw : |(1352542031/2500000000 : ℝ)|=(1352542031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1932043467/10000000000 : ℝ)|^4339 ≤ (5813507931351/50000000000000 : ℝ)^3315
        have hw : |(-1932043467/10000000000 : ℝ)|=(1932043467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s7_7 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4317063837/10000000000 : ℝ)*x 0 + (2247160523/5000000000 : ℝ)*x 1 + (2073152757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317063837/10000000000 : ℝ)^4339 ≤ (8326041727591/25000000000000 : ℝ)^3315 := by
    have hnat : (4317063837 : ℕ)^4339*25000000000000^3315 ≤ 8326041727591^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317063837 10000000000 8326041727591 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247160523/5000000000 : ℝ)^4339 ≤ (4388159555549/12500000000000 : ℝ)^3315 := by
    have hnat : (2247160523 : ℕ)^4339*12500000000000^3315 ≤ 4388159555549^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247160523 5000000000 4388159555549 12500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073152757/5000000000 : ℝ)^4339 ≤ (3948819578321/12500000000000 : ℝ)^3315 := by
    have hnat : (2073152757 : ℕ)^4339*12500000000000^3315 ≤ 3948819578321^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073152757 5000000000 3948819578321 12500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317063837/10000000000 : ℝ), (2247160523/5000000000 : ℝ), (2073152757/5000000000 : ℝ)] ![(8326041727591/25000000000000 : ℝ), (4388159555549/12500000000000 : ℝ), (3948819578321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317063837/10000000000 : ℝ)|^4339 ≤ (8326041727591/25000000000000 : ℝ)^3315
        have hw : |(4317063837/10000000000 : ℝ)|=(4317063837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247160523/5000000000 : ℝ)|^4339 ≤ (4388159555549/12500000000000 : ℝ)^3315
        have hw : |(2247160523/5000000000 : ℝ)|=(2247160523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2073152757/5000000000 : ℝ)|^4339 ≤ (3948819578321/12500000000000 : ℝ)^3315
        have hw : |(2073152757/5000000000 : ℝ)|=(2073152757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1379_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5617/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14729/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11233/100000 : ℝ) ^ (2169/512 : ℝ) ≤ (9497044622118393/100000000000000000000 : ℝ) := by
    have hpowers : (11233/100000 : ℝ)^2169 ≤ (9497044622118393/100000000000000000000 : ℝ)^512 := by
      have hnat : (11233 : ℕ)^2169*100000000000000000000^512 ≤ 9497044622118393^512*100000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11233 100000 9497044622118393 100000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11233/100000 : ℝ)) (X := (9497044622118393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1473/10000 : ℝ) ^ (2169/512 : ℝ) ≤ (29938766433803473/100000000000000000000 : ℝ) := by
    have hpowers : (1473/10000 : ℝ)^2169 ≤ (29938766433803473/100000000000000000000 : ℝ)^512 := by
      have hnat : (1473 : ℕ)^2169*100000000000000000000^512 ≤ 29938766433803473^512*10000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1473 10000 29938766433803473 100000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1473/10000 : ℝ)) (X := (29938766433803473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009497044622118393/50000000000000000000 : ℝ) ≤ (10000448329562113/10000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (50009497044622118393/50000000000000000000 : ℝ)^512 ≤ (10000448329562113/10000000000000000 : ℝ)^2169 := by
      have hnat : (50009497044622118393 : ℕ)^512*10000000000000000^2169 ≤ 10000448329562113^2169*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009497044622118393 50000000000000000000 10000448329562113 10000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000448329562113/10000000000000000 : ℝ)) (X := (50009497044622118393/50000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019717905527960933/50000000000000000000 : ℝ) ≤ (10000930755854731/10000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (50019717905527960933/50000000000000000000 : ℝ)^512 ≤ (10000930755854731/10000000000000000 : ℝ)^2169 := by
      have hnat : (50019717905527960933 : ℕ)^512*10000000000000000^2169 ≤ 10000930755854731^2169*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019717905527960933 50000000000000000000 10000930755854731 10000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000930755854731/10000000000000000 : ℝ)) (X := (50019717905527960933/50000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029938766433803473/50000000000000000000 : ℝ) ≤ (10001413182147349/10000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (50029938766433803473/50000000000000000000 : ℝ)^512 ≤ (10001413182147349/10000000000000000 : ℝ)^2169 := by
      have hnat : (50029938766433803473 : ℕ)^512*10000000000000000^2169 ≤ 10001413182147349^2169*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029938766433803473 50000000000000000000 10001413182147349 10000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001413182147349/10000000000000000 : ℝ)) (X := (50029938766433803473/50000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9497044622118393/100000000000000000000 : ℝ) ≤ ((34960729619388753173/34970000000000000000 : ℝ)+2*(241213146309/174850000000000 : ℝ)*(11233/100000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (34960729619388753173/34970000000000000000 : ℝ)+2*(241213146309/174850000000000 : ℝ)*(11233/100000 : ℝ)=(10000448329562113/10000000000000000 : ℝ) by norm_num, show 1+2*(9497044622118393/100000000000000000000 : ℝ)=(50009497044622118393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29938766433803473/100000000000000000000 : ℝ)+(9497044622118393/100000000000000000000 : ℝ) ≤ ((34960729619388753173/34970000000000000000 : ℝ)+(241213146309/174850000000000 : ℝ)*((1473/10000 : ℝ)+(11233/100000 : ℝ)))^(2169/512 : ℝ) := by
    rw [show (34960729619388753173/34970000000000000000 : ℝ)+(241213146309/174850000000000 : ℝ)*((1473/10000 : ℝ)+(11233/100000 : ℝ))=(10000930755854731/10000000000000000 : ℝ) by norm_num, show 1+(29938766433803473/100000000000000000000 : ℝ)+(9497044622118393/100000000000000000000 : ℝ)=(50019717905527960933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29938766433803473/100000000000000000000 : ℝ) ≤ ((34960729619388753173/34970000000000000000 : ℝ)+2*(241213146309/174850000000000 : ℝ)*(1473/10000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (34960729619388753173/34970000000000000000 : ℝ)+2*(241213146309/174850000000000 : ℝ)*(1473/10000 : ℝ)=(10001413182147349/10000000000000000 : ℝ) by norm_num, show 1+2*(29938766433803473/100000000000000000000 : ℝ)=(50029938766433803473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34960729619388753173/34970000000000000000 : ℝ)*(X 1 0+X 2 0)+(241213146309/174850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (34960729619388753173/34970000000000000000 : ℝ)) (alpha := (241213146309/174850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34960729619388753173/34970000000000000000 : ℝ)*(X 0 1+X 2 1)+(241213146309/174850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (34960729619388753173/34970000000000000000 : ℝ)) (alpha := (241213146309/174850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34960729619388753173/34970000000000000000 : ℝ)*(X 0 2+X 1 2)+(241213146309/174850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (34960729619388753173/34970000000000000000 : ℝ)) (alpha := (241213146309/174850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2012435401/10000000000 : ℝ)*X 0 0+(216430531/400000000 : ℝ)*X 0 1+(1311427039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348319399/10000000000 : ℝ)*X 1 0+(-2096503187/10000000000 : ℝ)*X 1 1+(5245708161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069663881/2000000000 : ℝ)*X 2 0+(5245708143/10000000000 : ℝ)*X 2 1+(-524125801/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317038993/10000000000 : ℝ)*X 0 0+(518130063/1250000000 : ℝ)*X 0 1+(280973711/625000000 : ℝ)*X 0 2+(4317038993/10000000000 : ℝ)*X 1 0+(518130063/1250000000 : ℝ)*X 1 1+(280973711/625000000 : ℝ)*X 1 2+(4317038993/10000000000 : ℝ)*X 2 0+(518130063/1250000000 : ℝ)*X 2 1+(280973711/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-503111779/2500000000 : ℝ)*X 0 0+(5246300553/10000000000 : ℝ)*X 0 1+(1352541967/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305629211/10000000000 : ℝ)*X 1 0+(-30188183/156250000 : ℝ)*X 1 1+(5410167709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305628971/10000000000 : ℝ)*X 2 0+(1352542031/2500000000 : ℝ)*X 2 1+(-1932043467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317063837/10000000000 : ℝ)*X 0 0+(2247160523/5000000000 : ℝ)*X 0 1+(2073152757/5000000000 : ℝ)*X 0 2+(4317063837/10000000000 : ℝ)*X 1 0+(2247160523/5000000000 : ℝ)*X 1 1+(2073152757/5000000000 : ℝ)*X 1 2+(4317063837/10000000000 : ℝ)*X 2 0+(2247160523/5000000000 : ℝ)*X 2 1+(2073152757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (951500049155935580327541441/134500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1317344579/100000000000000 : ℝ)*(base19) + (151558043/12500000000000 : ℝ)*(base23) + (59728481/100000000000000 : ℝ)*(lower2) + (209638827/100000000000000 : ℝ)*(upper3) + (108375523/100000000000000 : ℝ)*(upper5) + (4455706395345907/100000000000000 : ℝ)*(major0) + (4455706395345907/100000000000000 : ℝ)*(major1) + (4455706395345907/100000000000000 : ℝ)*(major2) + (6058609953043207/100000000000000 : ℝ)*(sp0) + (6058634155295141/100000000000000 : ℝ)*(sp1) + (378664641260961/6250000000000 : ℝ)*(sp2) + (285276283820953/10000000000000 : ℝ)*(sp3) + (25519596513/100000000000000 : ℝ)*(sp4) + (142440309/1000000000000 : ℝ)*(sp7) + (285277708224043/10000000000000 : ℝ)*(f.failure) + (151465886815993/2500000000000 : ℝ)*(f.sum) + (3466724989373/1345000000000000000000000000 : ℝ)*base66 + (752070515125647147/269000000000000000000000000000000 : ℝ)*base67 + (1740956204492352853/269000000000000000000000000000000 : ℝ)*base70 + (2371957680209352853/269000000000000000000000000000000 : ℝ)*base72 + (425542160717/1345000000000000000000000000 : ℝ)*base73 + (549179983117352853/269000000000000000000000000000000 : ℝ)*base76 + (53553175141647147/269000000000000000000000000000000 : ℝ)*base77 + (76097674300352853/269000000000000000000000000000000 : ℝ)*base80 + (4026750307609/672500000000000000000000000 : ℝ)*base82 + (7892469/1000000000000000000000 : ℝ)*base89 + (7892469/1000000000000000000000 : ℝ)*base91 + (7892469/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7005072165732851234357276799/874250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (463321823/50000000000000 : ℝ)*(base19) + (50170113/6250000000000 : ℝ)*(base23) + (270261413/100000000000000 : ℝ)*(lower1) + (58022981/100000000000000 : ℝ)*(upper3) + (13944967/25000000000000 : ℝ)*(lower4) + (101479753/50000000000000 : ℝ)*(upper5) + (2243977154175121/50000000000000 : ℝ)*(major0) + (2243977154175121/50000000000000 : ℝ)*(major1) + (2243977154175121/50000000000000 : ℝ)*(major2) + (2920021091/50000000000000 : ℝ)*(sp2) + (6102484461005119/100000000000000 : ℝ)*(sp4) + (6102483534361473/100000000000000 : ℝ)*(sp5) + (6102477818241129/100000000000000 : ℝ)*(sp6) + (1436711944303259/50000000000000 : ℝ)*(sp7) + (1436711944303259/50000000000000 : ℝ)*(f.failure) + (6102484461005119/100000000000000 : ℝ)*(f.sum) + (29200718659993/8742500000000000000000000000 : ℝ)*base65 + (5650620905133291067/1748500000000000000000000000000000 : ℝ)*base68 + (4515403624019791067/1748500000000000000000000000000000 : ℝ)*base70 + (230494202786532291067/1748500000000000000000000000000000 : ℝ)*base72 + (351852667901/273203125000000000000000000 : ℝ)*base74 + (66541959450827708933/1748500000000000000000000000000000 : ℝ)*base75 + (12698538676216708933/1748500000000000000000000000000000 : ℝ)*base77 + (20857201637560791067/1748500000000000000000000000000000 : ℝ)*base80 + (39495890780729/17485000000000000000000000000 : ℝ)*base82 + (15159803/5000000000000000000000 : ℝ)*base90 + (15159803/5000000000000000000000 : ℝ)*base92 + (15159803/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1379_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1379_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1379_box_0 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-462015301/2500000000 : ℝ)*x 0 + (2694192533/5000000000 : ℝ)*x 1 + (2694192559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (462015301/2500000000 : ℝ)^4339 ≤ (10969979217429/100000000000000 : ℝ)^3315 := by
    have hnat : (462015301 : ℕ)^4339*100000000000000^3315 ≤ 10969979217429^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462015301 2500000000 10969979217429 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694192533/5000000000 : ℝ)^4339 ≤ (22257505049231/50000000000000 : ℝ)^3315 := by
    have hnat : (2694192533 : ℕ)^4339*50000000000000^3315 ≤ 22257505049231^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694192533 5000000000 22257505049231 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694192559/5000000000 : ℝ)^4339 ≤ (11128752665187/25000000000000 : ℝ)^3315 := by
    have hnat : (2694192559 : ℕ)^4339*25000000000000^3315 ≤ 11128752665187^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694192559 5000000000 11128752665187 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-462015301/2500000000 : ℝ), (2694192533/5000000000 : ℝ), (2694192559/5000000000 : ℝ)] ![(10969979217429/100000000000000 : ℝ), (22257505049231/50000000000000 : ℝ), (11128752665187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-462015301/2500000000 : ℝ)|^4339 ≤ (10969979217429/100000000000000 : ℝ)^3315
        have hw : |(-462015301/2500000000 : ℝ)|=(462015301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694192533/5000000000 : ℝ)|^4339 ≤ (22257505049231/50000000000000 : ℝ)^3315
        have hw : |(2694192533/5000000000 : ℝ)|=(2694192533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694192559/5000000000 : ℝ)|^4339 ≤ (11128752665187/25000000000000 : ℝ)^3315
        have hw : |(2694192559/5000000000 : ℝ)|=(2694192559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_1 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66070223/125000000 : ℝ)*x 0 + (-1989030837/10000000000 : ℝ)*x 1 + (538838513/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66070223/125000000 : ℝ)^4339 ≤ (4340705604891/10000000000000 : ℝ)^3315 := by
    have hnat : (66070223 : ℕ)^4339*10000000000000^3315 ≤ 4340705604891^3315*125000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66070223 125000000 4340705604891 10000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989030837/10000000000 : ℝ)^4339 ≤ (377435410627/3125000000000 : ℝ)^3315 := by
    have hnat : (1989030837 : ℕ)^4339*3125000000000^3315 ≤ 377435410627^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989030837 10000000000 377435410627 3125000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538838513/1000000000 : ℝ)^4339 ≤ (22257505395253/50000000000000 : ℝ)^3315 := by
    have hnat : (538838513 : ℕ)^4339*50000000000000^3315 ≤ 22257505395253^3315*1000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538838513 1000000000 22257505395253 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66070223/125000000 : ℝ), (-1989030837/10000000000 : ℝ), (538838513/1000000000 : ℝ)] ![(4340705604891/10000000000000 : ℝ), (377435410627/3125000000000 : ℝ), (22257505395253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66070223/125000000 : ℝ)|^4339 ≤ (4340705604891/10000000000000 : ℝ)^3315
        have hw : |(66070223/125000000 : ℝ)|=(66070223/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989030837/10000000000 : ℝ)|^4339 ≤ (377435410627/3125000000000 : ℝ)^3315
        have hw : |(-1989030837/10000000000 : ℝ)|=(1989030837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538838513/1000000000 : ℝ)|^4339 ≤ (22257505395253/50000000000000 : ℝ)^3315
        have hw : |(538838513/1000000000 : ℝ)|=(538838513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_2 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642808867/5000000000 : ℝ)*x 0 + (5388385233/10000000000 : ℝ)*x 1 + (-1989030841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642808867/5000000000 : ℝ)^4339 ≤ (43407054909509/100000000000000 : ℝ)^3315 := by
    have hnat : (2642808867 : ℕ)^4339*100000000000000^3315 ≤ 43407054909509^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642808867 5000000000 43407054909509 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388385233/10000000000 : ℝ)^4339 ≤ (8903002380853/20000000000000 : ℝ)^3315 := by
    have hnat : (5388385233 : ℕ)^4339*20000000000000^3315 ≤ 8903002380853^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388385233 10000000000 8903002380853 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989030841/10000000000 : ℝ)^4339 ≤ (754870823241/6250000000000 : ℝ)^3315 := by
    have hnat : (1989030841 : ℕ)^4339*6250000000000^3315 ≤ 754870823241^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989030841 10000000000 754870823241 6250000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642808867/5000000000 : ℝ), (5388385233/10000000000 : ℝ), (-1989030841/10000000000 : ℝ)] ![(43407054909509/100000000000000 : ℝ), (8903002380853/20000000000000 : ℝ), (754870823241/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642808867/5000000000 : ℝ)|^4339 ≤ (43407054909509/100000000000000 : ℝ)^3315
        have hw : |(2642808867/5000000000 : ℝ)|=(2642808867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388385233/10000000000 : ℝ)|^4339 ≤ (8903002380853/20000000000000 : ℝ)^3315
        have hw : |(5388385233/10000000000 : ℝ)|=(5388385233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989030841/10000000000 : ℝ)|^4339 ≤ (754870823241/6250000000000 : ℝ)^3315
        have hw : |(-1989030841/10000000000 : ℝ)|=(1989030841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_3 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (139512089/312500000 : ℝ)*x 0 + (4247174273/10000000000 : ℝ)*x 1 + (4247174487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139512089/312500000 : ℝ)^4339 ≤ (8699887259651/25000000000000 : ℝ)^3315 := by
    have hnat : (139512089 : ℕ)^4339*25000000000000^3315 ≤ 8699887259651^3315*312500000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139512089 312500000 8699887259651 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247174273/10000000000 : ℝ)^4339 ≤ (8150056100047/25000000000000 : ℝ)^3315 := by
    have hnat : (4247174273 : ℕ)^4339*25000000000000^3315 ≤ 8150056100047^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247174273 10000000000 8150056100047 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4247174487/10000000000 : ℝ)^4339 ≤ (16300113275099/50000000000000 : ℝ)^3315 := by
    have hnat : (4247174487 : ℕ)^4339*50000000000000^3315 ≤ 16300113275099^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247174487 10000000000 16300113275099 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(139512089/312500000 : ℝ), (4247174273/10000000000 : ℝ), (4247174487/10000000000 : ℝ)] ![(8699887259651/25000000000000 : ℝ), (8150056100047/25000000000000 : ℝ), (16300113275099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(139512089/312500000 : ℝ)|^4339 ≤ (8699887259651/25000000000000 : ℝ)^3315
        have hw : |(139512089/312500000 : ℝ)|=(139512089/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247174273/10000000000 : ℝ)|^4339 ≤ (8150056100047/25000000000000 : ℝ)^3315
        have hw : |(4247174273/10000000000 : ℝ)|=(4247174273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4247174487/10000000000 : ℝ)|^4339 ≤ (16300113275099/50000000000000 : ℝ)^3315
        have hw : |(4247174487/10000000000 : ℝ)|=(4247174487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_4 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089777073/5000000000 : ℝ)*x 0 + (5265685789/10000000000 : ℝ)*x 1 + (10284543/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089777073/5000000000 : ℝ)^4339 ≤ (680706874169/5000000000000 : ℝ)^3315 := by
    have hnat : (1089777073 : ℕ)^4339*5000000000000^3315 ≤ 680706874169^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089777073 5000000000 680706874169 5000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265685789/10000000000 : ℝ)^4339 ≤ (8638586006231/20000000000000 : ℝ)^3315 := by
    have hnat : (5265685789 : ℕ)^4339*20000000000000^3315 ≤ 8638586006231^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265685789 10000000000 8638586006231 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10284543/19531250 : ℝ)^4339 ≤ (43192932468347/100000000000000 : ℝ)^3315 := by
    have hnat : (10284543 : ℕ)^4339*100000000000000^3315 ≤ 43192932468347^3315*19531250^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10284543 19531250 43192932468347 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089777073/5000000000 : ℝ), (5265685789/10000000000 : ℝ), (10284543/19531250 : ℝ)] ![(680706874169/5000000000000 : ℝ), (8638586006231/20000000000000 : ℝ), (43192932468347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089777073/5000000000 : ℝ)|^4339 ≤ (680706874169/5000000000000 : ℝ)^3315
        have hw : |(-1089777073/5000000000 : ℝ)|=(1089777073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265685789/10000000000 : ℝ)|^4339 ≤ (8638586006231/20000000000000 : ℝ)^3315
        have hw : |(5265685789/10000000000 : ℝ)|=(5265685789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10284543/19531250 : ℝ)|^4339 ≤ (43192932468347/100000000000000 : ℝ)^3315
        have hw : |(10284543/19531250 : ℝ)|=(10284543/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_5 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342916577/2500000000 : ℝ)*x 0 + (-7962959/39062500 : ℝ)*x 1 + (2632842937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342916577/2500000000 : ℝ)^4339 ≤ (44334313631443/100000000000000 : ℝ)^3315 := by
    have hnat : (1342916577 : ℕ)^4339*100000000000000^3315 ≤ 44334313631443^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342916577 2500000000 44334313631443 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7962959/39062500 : ℝ)^4339 ≤ (6236377708777/50000000000000 : ℝ)^3315 := by
    have hnat : (7962959 : ℕ)^4339*50000000000000^3315 ≤ 6236377708777^3315*39062500^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7962959 39062500 6236377708777 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632842937/5000000000 : ℝ)^4339 ≤ (539911636797/1250000000000 : ℝ)^3315 := by
    have hnat : (2632842937 : ℕ)^4339*1250000000000^3315 ≤ 539911636797^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632842937 5000000000 539911636797 1250000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342916577/2500000000 : ℝ), (-7962959/39062500 : ℝ), (2632842937/5000000000 : ℝ)] ![(44334313631443/100000000000000 : ℝ), (6236377708777/50000000000000 : ℝ), (539911636797/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342916577/2500000000 : ℝ)|^4339 ≤ (44334313631443/100000000000000 : ℝ)^3315
        have hw : |(1342916577/2500000000 : ℝ)|=(1342916577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7962959/39062500 : ℝ)|^4339 ≤ (6236377708777/50000000000000 : ℝ)^3315
        have hw : |(-7962959/39062500 : ℝ)|=(7962959/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632842937/5000000000 : ℝ)|^4339 ≤ (539911636797/1250000000000 : ℝ)^3315
        have hw : |(2632842937/5000000000 : ℝ)|=(2632842937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_6 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371665869/10000000000 : ℝ)*x 0 + (5265685717/10000000000 : ℝ)*x 1 + (-2038518307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371665869/10000000000 : ℝ)^4339 ≤ (22167154444503/50000000000000 : ℝ)^3315 := by
    have hnat : (5371665869 : ℕ)^4339*50000000000000^3315 ≤ 22167154444503^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371665869 10000000000 22167154444503 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265685717/10000000000 : ℝ)^4339 ≤ (69108686813/160000000000 : ℝ)^3315 := by
    have hnat : (5265685717 : ℕ)^4339*160000000000^3315 ≤ 69108686813^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265685717 10000000000 69108686813 160000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2038518307/10000000000 : ℝ)^4339 ≤ (12472761848423/100000000000000 : ℝ)^3315 := by
    have hnat : (2038518307 : ℕ)^4339*100000000000000^3315 ≤ 12472761848423^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038518307 10000000000 12472761848423 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371665869/10000000000 : ℝ), (5265685717/10000000000 : ℝ), (-2038518307/10000000000 : ℝ)] ![(22167154444503/50000000000000 : ℝ), (69108686813/160000000000 : ℝ), (12472761848423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371665869/10000000000 : ℝ)|^4339 ≤ (22167154444503/50000000000000 : ℝ)^3315
        have hw : |(5371665869/10000000000 : ℝ)|=(5371665869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265685717/10000000000 : ℝ)|^4339 ≤ (69108686813/160000000000 : ℝ)^3315
        have hw : |(5265685717/10000000000 : ℝ)|=(5265685717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2038518307/10000000000 : ℝ)|^4339 ≤ (12472761848423/100000000000000 : ℝ)^3315
        have hw : |(-2038518307/10000000000 : ℝ)|=(2038518307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_7 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2084356101/5000000000 : ℝ)*x 0 + (1098739771/2500000000 : ℝ)*x 1 + (4394959541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084356101/5000000000 : ℝ)^4339 ≤ (7953548147507/25000000000000 : ℝ)^3315 := by
    have hnat : (2084356101 : ℕ)^4339*25000000000000^3315 ≤ 7953548147507^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084356101 5000000000 7953548147507 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098739771/2500000000 : ℝ)^4339 ≤ (8523225343743/25000000000000 : ℝ)^3315 := by
    have hnat : (1098739771 : ℕ)^4339*25000000000000^3315 ≤ 8523225343743^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098739771 2500000000 8523225343743 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4394959541/10000000000 : ℝ)^4339 ≤ (6818581203023/20000000000000 : ℝ)^3315 := by
    have hnat : (4394959541 : ℕ)^4339*20000000000000^3315 ≤ 6818581203023^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394959541 10000000000 6818581203023 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2084356101/5000000000 : ℝ), (1098739771/2500000000 : ℝ), (4394959541/10000000000 : ℝ)] ![(7953548147507/25000000000000 : ℝ), (8523225343743/25000000000000 : ℝ), (6818581203023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2084356101/5000000000 : ℝ)|^4339 ≤ (7953548147507/25000000000000 : ℝ)^3315
        have hw : |(2084356101/5000000000 : ℝ)|=(2084356101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098739771/2500000000 : ℝ)|^4339 ≤ (8523225343743/25000000000000 : ℝ)^3315
        have hw : |(1098739771/2500000000 : ℝ)|=(1098739771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4394959541/10000000000 : ℝ)|^4339 ≤ (6818581203023/20000000000000 : ℝ)^3315
        have hw : |(4394959541/10000000000 : ℝ)|=(4394959541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_8 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054924183/5000000000 : ℝ)*x 0 + (2590522323/5000000000 : ℝ)*x 1 + (5402387529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054924183/5000000000 : ℝ)^4339 ≤ (13047075229079/100000000000000 : ℝ)^3315 := by
    have hnat : (1054924183 : ℕ)^4339*100000000000000^3315 ≤ 13047075229079^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054924183 5000000000 13047075229079 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590522323/5000000000 : ℝ)^4339 ≤ (8457288515907/20000000000000 : ℝ)^3315 := by
    have hnat : (2590522323 : ℕ)^4339*20000000000000^3315 ≤ 8457288515907^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590522323 5000000000 8457288515907 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402387529/10000000000 : ℝ)^4339 ≤ (44666482172519/100000000000000 : ℝ)^3315 := by
    have hnat : (5402387529 : ℕ)^4339*100000000000000^3315 ≤ 44666482172519^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402387529 10000000000 44666482172519 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054924183/5000000000 : ℝ), (2590522323/5000000000 : ℝ), (5402387529/10000000000 : ℝ)] ![(13047075229079/100000000000000 : ℝ), (8457288515907/20000000000000 : ℝ), (44666482172519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054924183/5000000000 : ℝ)|^4339 ≤ (13047075229079/100000000000000 : ℝ)^3315
        have hw : |(-1054924183/5000000000 : ℝ)|=(1054924183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590522323/5000000000 : ℝ)|^4339 ≤ (8457288515907/20000000000000 : ℝ)^3315
        have hw : |(2590522323/5000000000 : ℝ)|=(2590522323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402387529/10000000000 : ℝ)|^4339 ≤ (44666482172519/100000000000000 : ℝ)^3315
        have hw : |(5402387529/10000000000 : ℝ)|=(5402387529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_9 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105515873/200000000 : ℝ)*x 0 + (-396650677/2000000000 : ℝ)*x 1 + (5402387313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105515873/200000000 : ℝ)^4339 ≤ (43301485519633/100000000000000 : ℝ)^3315 := by
    have hnat : (105515873 : ℕ)^4339*100000000000000^3315 ≤ 43301485519633^3315*200000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105515873 200000000 43301485519633 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396650677/2000000000 : ℝ)^4339 ≤ (2406406926599/20000000000000 : ℝ)^3315 := by
    have hnat : (396650677 : ℕ)^4339*20000000000000^3315 ≤ 2406406926599^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396650677 2000000000 2406406926599 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402387313/10000000000 : ℝ)^4339 ≤ (11166619958749/25000000000000 : ℝ)^3315 := by
    have hnat : (5402387313 : ℕ)^4339*25000000000000^3315 ≤ 11166619958749^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402387313 10000000000 11166619958749 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105515873/200000000 : ℝ), (-396650677/2000000000 : ℝ), (5402387313/10000000000 : ℝ)] ![(43301485519633/100000000000000 : ℝ), (2406406926599/20000000000000 : ℝ), (11166619958749/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105515873/200000000 : ℝ)|^4339 ≤ (43301485519633/100000000000000 : ℝ)^3315
        have hw : |(105515873/200000000 : ℝ)|=(105515873/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-396650677/2000000000 : ℝ)|^4339 ≤ (2406406926599/20000000000000 : ℝ)^3315
        have hw : |(-396650677/2000000000 : ℝ)|=(396650677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402387313/10000000000 : ℝ)|^4339 ≤ (11166619958749/25000000000000 : ℝ)^3315
        have hw : |(5402387313/10000000000 : ℝ)|=(5402387313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_10 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318948267/2500000000 : ℝ)*x 0 + (1080477521/2000000000 : ℝ)*x 1 + (-991626887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318948267/2500000000 : ℝ)^4339 ≤ (43301479267271/100000000000000 : ℝ)^3315 := by
    have hnat : (1318948267 : ℕ)^4339*100000000000000^3315 ≤ 43301479267271^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318948267 2500000000 43301479267271 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080477521/2000000000 : ℝ)^4339 ≤ (44666482994981/100000000000000 : ℝ)^3315 := by
    have hnat : (1080477521 : ℕ)^4339*100000000000000^3315 ≤ 44666482994981^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080477521 2000000000 44666482994981 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (991626887/5000000000 : ℝ)^4339 ≤ (6016018860993/50000000000000 : ℝ)^3315 := by
    have hnat : (991626887 : ℕ)^4339*50000000000000^3315 ≤ 6016018860993^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991626887 5000000000 6016018860993 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318948267/2500000000 : ℝ), (1080477521/2000000000 : ℝ), (-991626887/5000000000 : ℝ)] ![(43301479267271/100000000000000 : ℝ), (44666482994981/100000000000000 : ℝ), (6016018860993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318948267/2500000000 : ℝ)|^4339 ≤ (43301479267271/100000000000000 : ℝ)^3315
        have hw : |(1318948267/2500000000 : ℝ)|=(1318948267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080477521/2000000000 : ℝ)|^4339 ≤ (44666482994981/100000000000000 : ℝ)^3315
        have hw : |(1080477521/2000000000 : ℝ)|=(1080477521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-991626887/5000000000 : ℝ)|^4339 ≤ (6016018860993/50000000000000 : ℝ)^3315
        have hw : |(-991626887/5000000000 : ℝ)|=(991626887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_11 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2248785263/5000000000 : ℝ)*x 0 + (423029469/1000000000 : ℝ)*x 1 + (2115147901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2248785263/5000000000 : ℝ)^4339 ≤ (35138502346211/100000000000000 : ℝ)^3315 := by
    have hnat : (2248785263 : ℕ)^4339*100000000000000^3315 ≤ 35138502346211^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248785263 5000000000 35138502346211 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423029469/1000000000 : ℝ)^4339 ≤ (32430743239631/100000000000000 : ℝ)^3315 := by
    have hnat : (423029469 : ℕ)^4339*100000000000000^3315 ≤ 32430743239631^3315*1000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423029469 1000000000 32430743239631 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115147901/5000000000 : ℝ)^4339 ≤ (3243075439791/10000000000000 : ℝ)^3315 := by
    have hnat : (2115147901 : ℕ)^4339*10000000000000^3315 ≤ 3243075439791^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115147901 5000000000 3243075439791 10000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2248785263/5000000000 : ℝ), (423029469/1000000000 : ℝ), (2115147901/5000000000 : ℝ)] ![(35138502346211/100000000000000 : ℝ), (32430743239631/100000000000000 : ℝ), (3243075439791/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2248785263/5000000000 : ℝ)|^4339 ≤ (35138502346211/100000000000000 : ℝ)^3315
        have hw : |(2248785263/5000000000 : ℝ)|=(2248785263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423029469/1000000000 : ℝ)|^4339 ≤ (32430743239631/100000000000000 : ℝ)^3315
        have hw : |(423029469/1000000000 : ℝ)|=(423029469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115147901/5000000000 : ℝ)|^4339 ≤ (3243075439791/10000000000000 : ℝ)^3315
        have hw : |(2115147901/5000000000 : ℝ)|=(2115147901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_12 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-959017441/5000000000 : ℝ)*x 0 + (2735450661/5000000000 : ℝ)*x 1 + (1313647249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959017441/5000000000 : ℝ)^4339 ≤ (11516794869107/100000000000000 : ℝ)^3315 := by
    have hnat : (959017441 : ℕ)^4339*100000000000000^3315 ≤ 11516794869107^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959017441 5000000000 11516794869107 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735450661/5000000000 : ℝ)^4339 ≤ (45409377315031/100000000000000 : ℝ)^3315 := by
    have hnat : (2735450661 : ℕ)^4339*100000000000000^3315 ≤ 45409377315031^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735450661 5000000000 45409377315031 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313647249/2500000000 : ℝ)^4339 ≤ (21536913902367/50000000000000 : ℝ)^3315 := by
    have hnat : (1313647249 : ℕ)^4339*50000000000000^3315 ≤ 21536913902367^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313647249 2500000000 21536913902367 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-959017441/5000000000 : ℝ), (2735450661/5000000000 : ℝ), (1313647249/2500000000 : ℝ)] ![(11516794869107/100000000000000 : ℝ), (45409377315031/100000000000000 : ℝ), (21536913902367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-959017441/5000000000 : ℝ)|^4339 ≤ (11516794869107/100000000000000 : ℝ)^3315
        have hw : |(-959017441/5000000000 : ℝ)|=(959017441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735450661/5000000000 : ℝ)|^4339 ≤ (45409377315031/100000000000000 : ℝ)^3315
        have hw : |(2735450661/5000000000 : ℝ)|=(2735450661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313647249/2500000000 : ℝ)|^4339 ≤ (21536913902367/50000000000000 : ℝ)^3315
        have hw : |(1313647249/2500000000 : ℝ)|=(1313647249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_13 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379446037/10000000000 : ℝ)*x 0 + (-510722967/2500000000 : ℝ)*x 1 + (2627294377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379446037/10000000000 : ℝ)^4339 ≤ (44418375425113/100000000000000 : ℝ)^3315 := by
    have hnat : (5379446037 : ℕ)^4339*100000000000000^3315 ≤ 44418375425113^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379446037 10000000000 44418375425113 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (510722967/2500000000 : ℝ)^4339 ≤ (12507799350373/100000000000000 : ℝ)^3315 := by
    have hnat : (510722967 : ℕ)^4339*100000000000000^3315 ≤ 12507799350373^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510722967 2500000000 12507799350373 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627294377/5000000000 : ℝ)^4339 ≤ (43073825208187/100000000000000 : ℝ)^3315 := by
    have hnat : (2627294377 : ℕ)^4339*100000000000000^3315 ≤ 43073825208187^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627294377 5000000000 43073825208187 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379446037/10000000000 : ℝ), (-510722967/2500000000 : ℝ), (2627294377/5000000000 : ℝ)] ![(44418375425113/100000000000000 : ℝ), (12507799350373/100000000000000 : ℝ), (43073825208187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379446037/10000000000 : ℝ)|^4339 ≤ (44418375425113/100000000000000 : ℝ)^3315
        have hw : |(5379446037/10000000000 : ℝ)|=(5379446037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-510722967/2500000000 : ℝ)|^4339 ≤ (12507799350373/100000000000000 : ℝ)^3315
        have hw : |(-510722967/2500000000 : ℝ)|=(510722967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627294377/5000000000 : ℝ)|^4339 ≤ (43073825208187/100000000000000 : ℝ)^3315
        have hw : |(2627294377/5000000000 : ℝ)|=(2627294377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_14 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672430751/1250000000 : ℝ)*x 0 + (1050917781/2000000000 : ℝ)*x 1 + (-408578341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672430751/1250000000 : ℝ)^4339 ≤ (44418375111691/100000000000000 : ℝ)^3315 := by
    have hnat : (672430751 : ℕ)^4339*100000000000000^3315 ≤ 44418375111691^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672430751 1250000000 44418375111691 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050917781/2000000000 : ℝ)^4339 ≤ (43073826828347/100000000000000 : ℝ)^3315 := by
    have hnat : (1050917781 : ℕ)^4339*100000000000000^3315 ≤ 43073826828347^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050917781 2000000000 43073826828347 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408578341/2000000000 : ℝ)^4339 ≤ (2501559608823/20000000000000 : ℝ)^3315 := by
    have hnat : (408578341 : ℕ)^4339*20000000000000^3315 ≤ 2501559608823^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408578341 2000000000 2501559608823 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672430751/1250000000 : ℝ), (1050917781/2000000000 : ℝ), (-408578341/2000000000 : ℝ)] ![(44418375111691/100000000000000 : ℝ), (43073826828347/100000000000000 : ℝ), (2501559608823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672430751/1250000000 : ℝ)|^4339 ≤ (44418375111691/100000000000000 : ℝ)^3315
        have hw : |(672430751/1250000000 : ℝ)|=(672430751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050917781/2000000000 : ℝ)|^4339 ≤ (43073826828347/100000000000000 : ℝ)^3315
        have hw : |(1050917781/2000000000 : ℝ)|=(1050917781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408578341/2000000000 : ℝ)|^4339 ≤ (2501559608823/20000000000000 : ℝ)^3315
        have hw : |(-408578341/2000000000 : ℝ)|=(408578341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_box_15 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2070761007/5000000000 : ℝ)*x 0 + (2204157257/5000000000 : ℝ)*x 1 + (440831449/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070761007/5000000000 : ℝ)^4339 ≤ (3154286188911/10000000000000 : ℝ)^3315 := by
    have hnat : (2070761007 : ℕ)^4339*10000000000000^3315 ≤ 3154286188911^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070761007 5000000000 3154286188911 10000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2204157257/5000000000 : ℝ)^4339 ≤ (34228569168281/100000000000000 : ℝ)^3315 := by
    have hnat : (2204157257 : ℕ)^4339*100000000000000^3315 ≤ 34228569168281^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204157257 5000000000 34228569168281 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440831449/1000000000 : ℝ)^4339 ≤ (34228568924369/100000000000000 : ℝ)^3315 := by
    have hnat : (440831449 : ℕ)^4339*100000000000000^3315 ≤ 34228568924369^3315*1000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440831449 1000000000 34228568924369 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2070761007/5000000000 : ℝ), (2204157257/5000000000 : ℝ), (440831449/1000000000 : ℝ)] ![(3154286188911/10000000000000 : ℝ), (34228569168281/100000000000000 : ℝ), (34228568924369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2070761007/5000000000 : ℝ)|^4339 ≤ (3154286188911/10000000000000 : ℝ)^3315
        have hw : |(2070761007/5000000000 : ℝ)|=(2070761007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2204157257/5000000000 : ℝ)|^4339 ≤ (34228569168281/100000000000000 : ℝ)^3315
        have hw : |(2204157257/5000000000 : ℝ)|=(2204157257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(440831449/1000000000 : ℝ)|^4339 ≤ (34228568924369/100000000000000 : ℝ)^3315
        have hw : |(440831449/1000000000 : ℝ)|=(440831449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1379_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7859/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29507/50000 : ℝ) ∧ (10021/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16899/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5617/50000 : ℝ) ^ (2169/512 : ℝ) ≤ (118757834765383/1250000000000000000 : ℝ) := by
    have hpowers : (5617/50000 : ℝ)^2169 ≤ (118757834765383/1250000000000000000 : ℝ)^512 := by
      have hnat : (5617 : ℕ)^2169*1250000000000000000^512 ≤ 118757834765383^512*50000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5617 50000 118757834765383 1250000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5617/50000 : ℝ)) (X := (118757834765383/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14729/100000 : ℝ) ^ (2169/512 : ℝ) ≤ (1870634814425941/6250000000000000000 : ℝ) := by
    have hpowers : (14729/100000 : ℝ)^2169 ≤ (1870634814425941/6250000000000000000 : ℝ)^512 := by
      have hnat : (14729 : ℕ)^2169*6250000000000000000^512 ≤ 1870634814425941^512*100000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14729 100000 1870634814425941 6250000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14729/100000 : ℝ)) (X := (1870634814425941/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (625118757834765383/625000000000000000 : ℝ) ≤ (10000448498653799/10000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (625118757834765383/625000000000000000 : ℝ)^512 ≤ (10000448498653799/10000000000000000 : ℝ)^2169 := by
      have hnat : (625118757834765383 : ℕ)^512*10000000000000000^2169 ≤ 10000448498653799^2169*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625118757834765383 625000000000000000 10000448498653799 10000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000448498653799/10000000000000000 : ℝ)) (X := (625118757834765383/625000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (781558052998531607/781250000000000000 : ℝ) ≤ (5000465318610313/5000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (781558052998531607/781250000000000000 : ℝ)^512 ≤ (5000465318610313/5000000000000000 : ℝ)^2169 := by
      have hnat : (781558052998531607 : ℕ)^512*5000000000000000^2169 ≤ 5000465318610313^2169*781250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781558052998531607 781250000000000000 5000465318610313 5000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000465318610313/5000000000000000 : ℝ)) (X := (781558052998531607/781250000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126870634814425941/3125000000000000000 : ℝ) ≤ (10001412775787453/10000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (3126870634814425941/3125000000000000000 : ℝ)^512 ≤ (10001412775787453/10000000000000000 : ℝ)^2169 := by
      have hnat : (3126870634814425941 : ℕ)^512*10000000000000000^2169 ≤ 10001412775787453^2169*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126870634814425941 3125000000000000000 10001412775787453 10000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001412775787453/10000000000000000 : ℝ)) (X := (3126870634814425941/3125000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(118757834765383/1250000000000000000 : ℝ) ≤ ((11646911604491852823/11650000000000000000 : ℝ)+2*(160712855609/116500000000000 : ℝ)*(5617/50000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (11646911604491852823/11650000000000000000 : ℝ)+2*(160712855609/116500000000000 : ℝ)*(5617/50000 : ℝ)=(10000448498653799/10000000000000000 : ℝ) by norm_num, show 1+2*(118757834765383/1250000000000000000 : ℝ)=(625118757834765383/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1870634814425941/6250000000000000000 : ℝ)+(118757834765383/1250000000000000000 : ℝ) ≤ ((11646911604491852823/11650000000000000000 : ℝ)+(160712855609/116500000000000 : ℝ)*((14729/100000 : ℝ)+(5617/50000 : ℝ)))^(2169/512 : ℝ) := by
    rw [show (11646911604491852823/11650000000000000000 : ℝ)+(160712855609/116500000000000 : ℝ)*((14729/100000 : ℝ)+(5617/50000 : ℝ))=(5000465318610313/5000000000000000 : ℝ) by norm_num, show 1+(1870634814425941/6250000000000000000 : ℝ)+(118757834765383/1250000000000000000 : ℝ)=(781558052998531607/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1870634814425941/6250000000000000000 : ℝ) ≤ ((11646911604491852823/11650000000000000000 : ℝ)+2*(160712855609/116500000000000 : ℝ)*(14729/100000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (11646911604491852823/11650000000000000000 : ℝ)+2*(160712855609/116500000000000 : ℝ)*(14729/100000 : ℝ)=(10001412775787453/10000000000000000 : ℝ) by norm_num, show 1+2*(1870634814425941/6250000000000000000 : ℝ)=(3126870634814425941/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11646911604491852823/11650000000000000000 : ℝ)*(X 1 0+X 2 0)+(160712855609/116500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (11646911604491852823/11650000000000000000 : ℝ)) (alpha := (160712855609/116500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11646911604491852823/11650000000000000000 : ℝ)*(X 0 1+X 2 1)+(160712855609/116500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (11646911604491852823/11650000000000000000 : ℝ)) (alpha := (160712855609/116500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11646911604491852823/11650000000000000000 : ℝ)*(X 0 2+X 1 2)+(160712855609/116500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (11646911604491852823/11650000000000000000 : ℝ)) (alpha := (160712855609/116500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-462015301/2500000000 : ℝ)*X 0 0+(2694192533/5000000000 : ℝ)*X 0 1+(2694192559/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66070223/125000000 : ℝ)*X 1 0+(-1989030837/10000000000 : ℝ)*X 1 1+(538838513/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642808867/5000000000 : ℝ)*X 2 0+(5388385233/10000000000 : ℝ)*X 2 1+(-1989030841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((139512089/312500000 : ℝ)*X 0 0+(4247174273/10000000000 : ℝ)*X 0 1+(4247174487/10000000000 : ℝ)*X 0 2+(139512089/312500000 : ℝ)*X 1 0+(4247174273/10000000000 : ℝ)*X 1 1+(4247174487/10000000000 : ℝ)*X 1 2+(139512089/312500000 : ℝ)*X 2 0+(4247174273/10000000000 : ℝ)*X 2 1+(4247174487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1089777073/5000000000 : ℝ)*X 0 0+(5265685789/10000000000 : ℝ)*X 0 1+(10284543/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1342916577/2500000000 : ℝ)*X 1 0+(-7962959/39062500 : ℝ)*X 1 1+(2632842937/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5371665869/10000000000 : ℝ)*X 2 0+(5265685717/10000000000 : ℝ)*X 2 1+(-2038518307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2084356101/5000000000 : ℝ)*X 0 0+(1098739771/2500000000 : ℝ)*X 0 1+(4394959541/10000000000 : ℝ)*X 0 2+(2084356101/5000000000 : ℝ)*X 1 0+(1098739771/2500000000 : ℝ)*X 1 1+(4394959541/10000000000 : ℝ)*X 1 2+(2084356101/5000000000 : ℝ)*X 2 0+(1098739771/2500000000 : ℝ)*X 2 1+(4394959541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1054924183/5000000000 : ℝ)*X 0 0+(2590522323/5000000000 : ℝ)*X 0 1+(5402387529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((105515873/200000000 : ℝ)*X 1 0+(-396650677/2000000000 : ℝ)*X 1 1+(5402387313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318948267/2500000000 : ℝ)*X 2 0+(1080477521/2000000000 : ℝ)*X 2 1+(-991626887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2248785263/5000000000 : ℝ)*X 0 0+(423029469/1000000000 : ℝ)*X 0 1+(2115147901/5000000000 : ℝ)*X 0 2+(2248785263/5000000000 : ℝ)*X 1 0+(423029469/1000000000 : ℝ)*X 1 1+(2115147901/5000000000 : ℝ)*X 1 2+(2248785263/5000000000 : ℝ)*X 2 0+(423029469/1000000000 : ℝ)*X 2 1+(2115147901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-959017441/5000000000 : ℝ)*X 0 0+(2735450661/5000000000 : ℝ)*X 0 1+(1313647249/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5379446037/10000000000 : ℝ)*X 1 0+(-510722967/2500000000 : ℝ)*X 1 1+(2627294377/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672430751/1250000000 : ℝ)*X 2 0+(1050917781/2000000000 : ℝ)*X 2 1+(-408578341/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2070761007/5000000000 : ℝ)*X 0 0+(2204157257/5000000000 : ℝ)*X 0 1+(440831449/1000000000 : ℝ)*X 0 2+(2070761007/5000000000 : ℝ)*X 1 0+(2204157257/5000000000 : ℝ)*X 1 1+(440831449/1000000000 : ℝ)*X 1 2+(2070761007/5000000000 : ℝ)*X 2 0+(2204157257/5000000000 : ℝ)*X 2 1+(440831449/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7859/12500 : ℝ) ≤ (-3662131019884759884459390141/5825000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173337203/100000000000000 : ℝ)*(lower0) + (8105263/10000000000000 : ℝ)*(lower3) + (216147279/50000000000000 : ℝ)*(lower4) + (2961846562539539/100000000000000 : ℝ)*(major0) + (2961846562539539/100000000000000 : ℝ)*(major1) + (2961846562539539/100000000000000 : ℝ)*(major2) + (27092498733/100000000000000 : ℝ)*(sp2) + (2078458899/100000000000000 : ℝ)*(sp3) + (1012078394655817/25000000000000 : ℝ)*(sp4) + (2024146171050093/50000000000000 : ℝ)*(sp5) + (506036602241607/12500000000000 : ℝ)*(sp6) + (948163768437309/50000000000000 : ℝ)*(sp7) + (3165904161/50000000000000 : ℝ)*(sp12) + (6892082851/25000000000000 : ℝ)*(sp13) + (474082403833379/25000000000000 : ℝ)*(f.failure) + (404831991043159/10000000000000 : ℝ)*(f.sum) + (14924630801949/5825000000000000000000000000 : ℝ)*base66 + (755910911643631403/1165000000000000000000000000000000 : ℝ)*base68 + (9477811184183631403/1165000000000000000000000000000000 : ℝ)*base70 + (2134858402771368597/1165000000000000000000000000000000 : ℝ)*base71 + (824440760191/91015625000000000000000000 : ℝ)*base74 + (3086805463883631403/1165000000000000000000000000000000 : ℝ)*base76 + (4256272550521368597/1165000000000000000000000000000000 : ℝ)*base77 + (7049720261531368597/1165000000000000000000000000000000 : ℝ)*base79 + (49513648853199/5825000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7563843/2500000000000000000000 : ℝ)*base90 + (7563843/2500000000000000000000 : ℝ)*base92 + (7563843/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29507/50000 : ℝ) ≤ (1718843786992918349658504135987/2912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14545943/50000000000000 : ℝ)*(lower1) + (6931641/100000000000000 : ℝ)*(upper2) + (4441901/25000000000000 : ℝ)*(lower4) + (15158907107559/500000000000 : ℝ)*(major0) + (15158907107559/500000000000 : ℝ)*(major1) + (15158907107559/500000000000 : ℝ)*(major2) + (2051391091295791/50000000000000 : ℝ)*(sp0) + (4102783876841139/100000000000000 : ℝ)*(sp1) + (256423855821373/6250000000000 : ℝ)*(sp2) + (388220929200537/20000000000000 : ℝ)*(sp3) + (675930439/50000000000000 : ℝ)*(sp5) + (3535560049/100000000000000 : ℝ)*(sp6) + (936421969/100000000000000 : ℝ)*(sp7) + (609222087/20000000000000 : ℝ)*(sp12) + (970552791212327/50000000000000 : ℝ)*(f.failure) + (2051392614351009/50000000000000 : ℝ)*(f.sum) + (560807726453/58250000000000000000000000 : ℝ)*base66 + (66813921258414057/5825000000000000000000000000000 : ℝ)*base67 + (51675009099889057/5825000000000000000000000000000 : ℝ)*base69 + (55868036080239057/5825000000000000000000000000000 : ℝ)*base71 + (21267163077/23300000000000000000000000 : ℝ)*base74 + (38947089902439057/5825000000000000000000000000000 : ℝ)*base75 + (17111340860314057/5825000000000000000000000000000 : ℝ)*base77 + (78852628197539057/5825000000000000000000000000000 : ℝ)*base79 + (832142707021/233000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (36202759/5000000000000000000000 : ℝ)*base90 + (36202759/5000000000000000000000 : ℝ)*base92 + (36202759/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (10021/12500 : ℝ) ≤ (29187124734604830917649912985971/36406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35259783/25000000000000 : ℝ)*(upper0) + (7084273/50000000000000 : ℝ)*(lower1) + (26293947/10000000000000 : ℝ)*(upper2) + (55796649/50000000000000 : ℝ)*(lower3) + (204592419/100000000000000 : ℝ)*(lower5) + (417778281620259/12500000000000 : ℝ)*(major0) + (417778281620259/12500000000000 : ℝ)*(major1) + (417778281620259/12500000000000 : ℝ)*(major2) + (57500563/50000000000000 : ℝ)*(sp0) + (160128739/20000000000000 : ℝ)*(sp3) + (141183130834619/3125000000000 : ℝ)*(sp8) + (2258930150854467/50000000000000 : ℝ)*(sp9) + (2258930150854467/50000000000000 : ℝ)*(sp10) + (2139867855888893/100000000000000 : ℝ)*(sp11) + (534967164133147/25000000000000 : ℝ)*(f.failure) + (2258930150854467/50000000000000 : ℝ)*(f.sum) + (7717884513051/2912500000000000000000000000 : ℝ)*base66 + (1262773752028116157/145625000000000000000000000000000 : ℝ)*base67 + (2445128361438133843/145625000000000000000000000000000 : ℝ)*base70 + (1754669883245008843/145625000000000000000000000000000 : ℝ)*base72 + (5630905748027/5825000000000000000000000000 : ℝ)*base74 + (677617308179383843/145625000000000000000000000000000 : ℝ)*base76 + (2396206318242508843/145625000000000000000000000000000 : ℝ)*base78 + (1131735616183133843/145625000000000000000000000000000 : ℝ)*base80 + (4008202994527/5825000000000000000000000000 : ℝ)*base82 + (26631301/2500000000000000000000 : ℝ)*base89 + (26631301/2500000000000000000000 : ℝ)*base91 + (26631301/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-16899/20000 : ℝ) ≤ (-4921697659210433542739762007/5825000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34184777/50000000000000 : ℝ)*(lower0) + (10071967/12500000000000 : ℝ)*(lower1) + (26770263/50000000000000 : ℝ)*(lower2) + (20304687/100000000000000 : ℝ)*(lower3) + (1689570756162183/50000000000000 : ℝ)*(major0) + (1689570756162183/50000000000000 : ℝ)*(major1) + (1689570756162183/50000000000000 : ℝ)*(major2) + (155126990067/100000000000000 : ℝ)*(sp5) + (69070144541/100000000000000 : ℝ)*(sp6) + (306248441/4000000000000 : ℝ)*(sp7) + (4622943502882099/100000000000000 : ℝ)*(sp12) + (4622788375892033/100000000000000 : ℝ)*(sp13) + (2311437216368779/50000000000000 : ℝ)*(sp14) + (1081748043390707/50000000000000 : ℝ)*(sp15) + (2163503742992439/100000000000000 : ℝ)*(f.failure) + (4622943502882099/100000000000000 : ℝ)*(f.sum) + (8341831184147/2912500000000000000000000000 : ℝ)*base65 + (1574826466055907391/582500000000000000000000000000000 : ℝ)*base68 + (765057268706592609/582500000000000000000000000000000 : ℝ)*base69 + (4577020939698407391/582500000000000000000000000000000 : ℝ)*base72 + (7541109337297/2912500000000000000000000000 : ℝ)*base73 + (5974134445763407391/582500000000000000000000000000000 : ℝ)*base76 + (627701759081592609/582500000000000000000000000000000 : ℝ)*base77 + (1055988178701592609/582500000000000000000000000000000 : ℝ)*base79 + (12951929247603/2912500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (28636137/10000000000000000000000 : ℝ)*base89 + (28636137/10000000000000000000000 : ℝ)*base91 + (28636137/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1379_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7859/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29507/50000 : ℝ) else (10021/12500 : ℝ) ≤ X j i ∧ X j i ≤ (16899/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1379_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1379_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7859/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29507/50000 : ℝ) else (10021/12500 : ℝ) ≤ X j i ∧ X j i ≤ (16899/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1379_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1379_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1379_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7859/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29507/50000 : ℝ) else (10021/12500 : ℝ) ≤ X j i ∧ X j i ≤ (16899/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1379_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
