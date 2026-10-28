-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1135_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:29:09.268775+00:00
-- url     : https://prove2.me/submissions/a81c5dec-69d5-49ea-9043-2b3766a79346

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
theorem support_rectangle_w1135_s6_0 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-271275743/1250000000 : ℝ)*x 0 + (1348380303/2500000000 : ℝ)*x 1 + (526528577/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271275743/1250000000 : ℝ)^1041 ≤ (412073047603/3125000000000 : ℝ)^785 := by
    have hnat : (271275743 : ℕ)^1041*3125000000000^785 ≤ 412073047603^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271275743 1250000000 412073047603 3125000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348380303/2500000000 : ℝ)^1041 ≤ (44099335945639/100000000000000 : ℝ)^785 := by
    have hnat : (1348380303 : ℕ)^1041*100000000000000^785 ≤ 44099335945639^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348380303 2500000000 44099335945639 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526528577/1000000000 : ℝ)^1041 ≤ (4271432651241/10000000000000 : ℝ)^785 := by
    have hnat : (526528577 : ℕ)^1041*10000000000000^785 ≤ 4271432651241^785*1000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526528577 1000000000 4271432651241 10000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271275743/1250000000 : ℝ), (1348380303/2500000000 : ℝ), (526528577/1000000000 : ℝ)] ![(412073047603/3125000000000 : ℝ), (44099335945639/100000000000000 : ℝ), (4271432651241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271275743/1250000000 : ℝ)|^1041 ≤ (412073047603/3125000000000 : ℝ)^785
        have hw : |(-271275743/1250000000 : ℝ)|=(271275743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348380303/2500000000 : ℝ)|^1041 ≤ (44099335945639/100000000000000 : ℝ)^785
        have hw : |(1348380303/2500000000 : ℝ)|=(1348380303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526528577/1000000000 : ℝ)|^1041 ≤ (4271432651241/10000000000000 : ℝ)^785
        have hw : |(526528577/1000000000 : ℝ)|=(526528577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s6_1 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672437167/5000000000 : ℝ)*x 0 + (-2235256003/10000000000 : ℝ)*x 1 + (21061143/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672437167/5000000000 : ℝ)^1041 ≤ (4357264576793/10000000000000 : ℝ)^785 := by
    have hnat : (2672437167 : ℕ)^1041*10000000000000^785 ≤ 4357264576793^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672437167 5000000000 4357264576793 10000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2235256003/10000000000 : ℝ)^1041 ≤ (342825698171/2500000000000 : ℝ)^785 := by
    have hnat : (2235256003 : ℕ)^1041*2500000000000^785 ≤ 342825698171^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235256003 10000000000 342825698171 2500000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21061143/40000000 : ℝ)^1041 ≤ (42714326297249/100000000000000 : ℝ)^785 := by
    have hnat : (21061143 : ℕ)^1041*100000000000000^785 ≤ 42714326297249^785*40000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21061143 40000000 42714326297249 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672437167/5000000000 : ℝ), (-2235256003/10000000000 : ℝ), (21061143/40000000 : ℝ)] ![(4357264576793/10000000000000 : ℝ), (342825698171/2500000000000 : ℝ), (42714326297249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672437167/5000000000 : ℝ)|^1041 ≤ (4357264576793/10000000000000 : ℝ)^785
        have hw : |(2672437167/5000000000 : ℝ)|=(2672437167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2235256003/10000000000 : ℝ)|^1041 ≤ (342825698171/2500000000000 : ℝ)^785
        have hw : |(-2235256003/10000000000 : ℝ)|=(2235256003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21061143/40000000 : ℝ)|^1041 ≤ (42714326297249/100000000000000 : ℝ)^785
        have hw : |(21061143/40000000 : ℝ)|=(21061143/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s6_2 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (53448743/100000000 : ℝ)*x 0 + (5265285763/10000000000 : ℝ)*x 1 + (-223525603/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53448743/100000000 : ℝ)^1041 ≤ (43572645400363/100000000000000 : ℝ)^785 := by
    have hnat : (53448743 : ℕ)^1041*100000000000000^785 ≤ 43572645400363^785*100000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53448743 100000000 43572645400363 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265285763/10000000000 : ℝ)^1041 ≤ (2669645402319/6250000000000 : ℝ)^785 := by
    have hnat : (5265285763 : ℕ)^1041*6250000000000^785 ≤ 2669645402319^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265285763 10000000000 2669645402319 6250000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223525603/1000000000 : ℝ)^1041 ≤ (27426056293/200000000000 : ℝ)^785 := by
    have hnat : (223525603 : ℕ)^1041*200000000000^785 ≤ 27426056293^785*1000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223525603 1000000000 27426056293 200000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53448743/100000000 : ℝ), (5265285763/10000000000 : ℝ), (-223525603/1000000000 : ℝ)] ![(43572645400363/100000000000000 : ℝ), (2669645402319/6250000000000 : ℝ), (27426056293/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53448743/100000000 : ℝ)|^1041 ≤ (43572645400363/100000000000000 : ℝ)^785
        have hw : |(53448743/100000000 : ℝ)|=(53448743/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265285763/10000000000 : ℝ)|^1041 ≤ (2669645402319/6250000000000 : ℝ)^785
        have hw : |(5265285763/10000000000 : ℝ)|=(5265285763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223525603/1000000000 : ℝ)|^1041 ≤ (27426056293/200000000000 : ℝ)^785
        have hw : |(-223525603/1000000000 : ℝ)|=(223525603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s6_3 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4365642299/10000000000 : ℝ)*x 0 + (4240109251/10000000000 : ℝ)*x 1 + (224744011/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365642299/10000000000 : ℝ)^1041 ≤ (2082296619941/6250000000000 : ℝ)^785 := by
    have hnat : (4365642299 : ℕ)^1041*6250000000000^785 ≤ 2082296619941^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365642299 10000000000 2082296619941 6250000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240109251/10000000000 : ℝ)^1041 ≤ (6410460649523/20000000000000 : ℝ)^785 := by
    have hnat : (4240109251 : ℕ)^1041*20000000000000^785 ≤ 6410460649523^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240109251 10000000000 6410460649523 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224744011/500000000 : ℝ)^1041 ≤ (1731547540471/5000000000000 : ℝ)^785 := by
    have hnat : (224744011 : ℕ)^1041*5000000000000^785 ≤ 1731547540471^785*500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224744011 500000000 1731547540471 5000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365642299/10000000000 : ℝ), (4240109251/10000000000 : ℝ), (224744011/500000000 : ℝ)] ![(2082296619941/6250000000000 : ℝ), (6410460649523/20000000000000 : ℝ), (1731547540471/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365642299/10000000000 : ℝ)|^1041 ≤ (2082296619941/6250000000000 : ℝ)^785
        have hw : |(4365642299/10000000000 : ℝ)|=(4365642299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240109251/10000000000 : ℝ)|^1041 ≤ (6410460649523/20000000000000 : ℝ)^785
        have hw : |(4240109251/10000000000 : ℝ)|=(4240109251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224744011/500000000 : ℝ)|^1041 ≤ (1731547540471/5000000000000 : ℝ)^785
        have hw : |(224744011/500000000 : ℝ)|=(224744011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s6_4 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-434042203/2000000000 : ℝ)*x 0 + (1053121907/2000000000 : ℝ)*x 1 + (5393196203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434042203/2000000000 : ℝ)^1041 ≤ (1318637838327/10000000000000 : ℝ)^785 := by
    have hnat : (434042203 : ℕ)^1041*10000000000000^785 ≤ 1318637838327^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434042203 2000000000 1318637838327 10000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053121907/2000000000 : ℝ)^1041 ≤ (8543561924083/20000000000000 : ℝ)^785 := by
    have hnat : (1053121907 : ℕ)^1041*20000000000000^785 ≤ 8543561924083^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053121907 2000000000 8543561924083 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393196203/10000000000 : ℝ)^1041 ≤ (22047905989243/50000000000000 : ℝ)^785 := by
    have hnat : (5393196203 : ℕ)^1041*50000000000000^785 ≤ 22047905989243^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393196203 10000000000 22047905989243 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434042203/2000000000 : ℝ), (1053121907/2000000000 : ℝ), (5393196203/10000000000 : ℝ)] ![(1318637838327/10000000000000 : ℝ), (8543561924083/20000000000000 : ℝ), (22047905989243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434042203/2000000000 : ℝ)|^1041 ≤ (1318637838327/10000000000000 : ℝ)^785
        have hw : |(-434042203/2000000000 : ℝ)|=(434042203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053121907/2000000000 : ℝ)|^1041 ≤ (8543561924083/20000000000000 : ℝ)^785
        have hw : |(1053121907/2000000000 : ℝ)|=(1053121907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393196203/10000000000 : ℝ)|^1041 ≤ (22047905989243/50000000000000 : ℝ)^785
        have hw : |(5393196203/10000000000 : ℝ)|=(5393196203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s6_5 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (664050271/1250000000 : ℝ)*x 0 + (-2107345589/10000000000 : ℝ)*x 1 + (5393196233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664050271/1250000000 : ℝ)^1041 ≤ (21610972089413/50000000000000 : ℝ)^785 := by
    have hnat : (664050271 : ℕ)^1041*50000000000000^785 ≤ 21610972089413^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664050271 1250000000 21610972089413 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107345589/10000000000 : ℝ)^1041 ≤ (6341121752861/50000000000000 : ℝ)^785 := by
    have hnat : (2107345589 : ℕ)^1041*50000000000000^785 ≤ 6341121752861^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107345589 10000000000 6341121752861 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393196233/10000000000 : ℝ)^1041 ≤ (44095812303763/100000000000000 : ℝ)^785 := by
    have hnat : (5393196233 : ℕ)^1041*100000000000000^785 ≤ 44095812303763^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393196233 10000000000 44095812303763 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664050271/1250000000 : ℝ), (-2107345589/10000000000 : ℝ), (5393196233/10000000000 : ℝ)] ![(21610972089413/50000000000000 : ℝ), (6341121752861/50000000000000 : ℝ), (44095812303763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664050271/1250000000 : ℝ)|^1041 ≤ (21610972089413/50000000000000 : ℝ)^785
        have hw : |(664050271/1250000000 : ℝ)|=(664050271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107345589/10000000000 : ℝ)|^1041 ≤ (6341121752861/50000000000000 : ℝ)^785
        have hw : |(-2107345589/10000000000 : ℝ)|=(2107345589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393196233/10000000000 : ℝ)|^1041 ≤ (44095812303763/100000000000000 : ℝ)^785
        have hw : |(5393196233/10000000000 : ℝ)|=(5393196233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s6_6 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1062480461/2000000000 : ℝ)*x 0 + (168537373/312500000 : ℝ)*x 1 + (-1053672903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062480461/2000000000 : ℝ)^1041 ≤ (10805486414241/25000000000000 : ℝ)^785 := by
    have hnat : (1062480461 : ℕ)^1041*25000000000000^785 ≤ 10805486414241^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062480461 2000000000 10805486414241 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168537373/312500000 : ℝ)^1041 ≤ (68899701693/156250000000 : ℝ)^785 := by
    have hnat : (168537373 : ℕ)^1041*156250000000^785 ≤ 68899701693^785*312500000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168537373 312500000 68899701693 156250000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053672903/5000000000 : ℝ)^1041 ≤ (396320163673/3125000000000 : ℝ)^785 := by
    have hnat : (1053672903 : ℕ)^1041*3125000000000^785 ≤ 396320163673^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053672903 5000000000 396320163673 3125000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062480461/2000000000 : ℝ), (168537373/312500000 : ℝ), (-1053672903/5000000000 : ℝ)] ![(10805486414241/25000000000000 : ℝ), (68899701693/156250000000 : ℝ), (396320163673/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062480461/2000000000 : ℝ)|^1041 ≤ (10805486414241/25000000000000 : ℝ)^785
        have hw : |(1062480461/2000000000 : ℝ)|=(1062480461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168537373/312500000 : ℝ)|^1041 ≤ (68899701693/156250000000 : ℝ)^785
        have hw : |(168537373/312500000 : ℝ)|=(168537373/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1053672903/5000000000 : ℝ)|^1041 ≤ (396320163673/3125000000000 : ℝ)^785
        have hw : |(-1053672903/5000000000 : ℝ)|=(1053672903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s6_7 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (436565221/1000000000 : ℝ)*x 0 + (4494236803/10000000000 : ℝ)*x 1 + (265047187/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436565221/1000000000 : ℝ)^1041 ≤ (16658423110937/50000000000000 : ℝ)^785 := by
    have hnat : (436565221 : ℕ)^1041*50000000000000^785 ≤ 16658423110937^785*1000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436565221 1000000000 16658423110937 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494236803/10000000000 : ℝ)^1041 ≤ (6924875422251/20000000000000 : ℝ)^785 := by
    have hnat : (4494236803 : ℕ)^1041*20000000000000^785 ≤ 6924875422251^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494236803 10000000000 6924875422251 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265047187/625000000 : ℝ)^1041 ≤ (3205877664719/10000000000000 : ℝ)^785 := by
    have hnat : (265047187 : ℕ)^1041*10000000000000^785 ≤ 3205877664719^785*625000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265047187 625000000 3205877664719 10000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436565221/1000000000 : ℝ), (4494236803/10000000000 : ℝ), (265047187/625000000 : ℝ)] ![(16658423110937/50000000000000 : ℝ), (6924875422251/20000000000000 : ℝ), (3205877664719/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436565221/1000000000 : ℝ)|^1041 ≤ (16658423110937/50000000000000 : ℝ)^785
        have hw : |(436565221/1000000000 : ℝ)|=(436565221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494236803/10000000000 : ℝ)|^1041 ≤ (6924875422251/20000000000000 : ℝ)^785
        have hw : |(4494236803/10000000000 : ℝ)|=(4494236803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265047187/625000000 : ℝ)|^1041 ≤ (3205877664719/10000000000000 : ℝ)^785
        have hw : |(265047187/625000000 : ℝ)|=(265047187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1135_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11337/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14053/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2261/20000 : ℝ) ^ (8327/2048 : ℝ) ≤ (7073686199202673/50000000000000000000 : ℝ) := by
    have hpowers : (2261/20000 : ℝ)^8327 ≤ (7073686199202673/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2261 : ℕ)^8327*50000000000000000000^2048 ≤ 7073686199202673^2048*20000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2261 20000 7073686199202673 50000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2261/20000 : ℝ)) (X := (7073686199202673/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7043/50000 : ℝ) ^ (8327/2048 : ℝ) ≤ (6919433582842797/20000000000000000000 : ℝ) := by
    have hpowers : (7043/50000 : ℝ)^8327 ≤ (6919433582842797/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7043 : ℕ)^8327*20000000000000000000^2048 ≤ 6919433582842797^2048*50000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7043 50000 6919433582842797 20000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7043/50000 : ℝ)) (X := (6919433582842797/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007073686199202673/25000000000000000000 : ℝ) ≤ (1250086978288381/1250000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (25007073686199202673/25000000000000000000 : ℝ)^2048 ≤ (1250086978288381/1250000000000000 : ℝ)^8327 := by
      have hnat : (25007073686199202673 : ℕ)^2048*1250000000000000^8327 ≤ 1250086978288381^8327*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007073686199202673 25000000000000000000 1250086978288381 1250000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250086978288381/1250000000000000 : ℝ)) (X := (25007073686199202673/25000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048744540312619331/100000000000000000000 : ℝ) ≤ (400047945467641/400000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (100048744540312619331/100000000000000000000 : ℝ)^2048 ≤ (400047945467641/400000000000000 : ℝ)^8327 := by
      have hnat : (100048744540312619331 : ℕ)^2048*400000000000000^8327 ≤ 400047945467641^8327*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048744540312619331 100000000000000000000 400047945467641 400000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400047945467641/400000000000000 : ℝ)) (X := (100048744540312619331/100000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006919433582842797/10000000000000000000 : ℝ) ≤ (5000850723537501/5000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (10006919433582842797/10000000000000000000 : ℝ)^2048 ≤ (5000850723537501/5000000000000000 : ℝ)^8327 := by
      have hnat : (10006919433582842797 : ℕ)^2048*5000000000000000^8327 ≤ 5000850723537501^8327*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006919433582842797 10000000000000000000 5000850723537501 5000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000850723537501/5000000000000000 : ℝ)) (X := (10006919433582842797/10000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7073686199202673/50000000000000000000 : ℝ) ≤ ((13900283275089090259/13905000000000000000 : ℝ)+2*(502810383977/278100000000000 : ℝ)*(2261/20000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (13900283275089090259/13905000000000000000 : ℝ)+2*(502810383977/278100000000000 : ℝ)*(2261/20000 : ℝ)=(1250086978288381/1250000000000000 : ℝ) by norm_num, show 1+2*(7073686199202673/50000000000000000000 : ℝ)=(25007073686199202673/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6919433582842797/20000000000000000000 : ℝ)+(7073686199202673/50000000000000000000 : ℝ) ≤ ((13900283275089090259/13905000000000000000 : ℝ)+(502810383977/278100000000000 : ℝ)*((7043/50000 : ℝ)+(2261/20000 : ℝ)))^(8327/2048 : ℝ) := by
    rw [show (13900283275089090259/13905000000000000000 : ℝ)+(502810383977/278100000000000 : ℝ)*((7043/50000 : ℝ)+(2261/20000 : ℝ))=(400047945467641/400000000000000 : ℝ) by norm_num, show 1+(6919433582842797/20000000000000000000 : ℝ)+(7073686199202673/50000000000000000000 : ℝ)=(100048744540312619331/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6919433582842797/20000000000000000000 : ℝ) ≤ ((13900283275089090259/13905000000000000000 : ℝ)+2*(502810383977/278100000000000 : ℝ)*(7043/50000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (13900283275089090259/13905000000000000000 : ℝ)+2*(502810383977/278100000000000 : ℝ)*(7043/50000 : ℝ)=(5000850723537501/5000000000000000 : ℝ) by norm_num, show 1+2*(6919433582842797/20000000000000000000 : ℝ)=(10006919433582842797/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13900283275089090259/13905000000000000000 : ℝ)*(X 1 0+X 2 0)+(502810383977/278100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (13900283275089090259/13905000000000000000 : ℝ)) (alpha := (502810383977/278100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13900283275089090259/13905000000000000000 : ℝ)*(X 0 1+X 2 1)+(502810383977/278100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (13900283275089090259/13905000000000000000 : ℝ)) (alpha := (502810383977/278100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13900283275089090259/13905000000000000000 : ℝ)*(X 0 2+X 1 2)+(502810383977/278100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (13900283275089090259/13905000000000000000 : ℝ)) (alpha := (502810383977/278100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-271275743/1250000000 : ℝ)*X 0 0+(1348380303/2500000000 : ℝ)*X 0 1+(526528577/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672437167/5000000000 : ℝ)*X 1 0+(-2235256003/10000000000 : ℝ)*X 1 1+(21061143/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53448743/100000000 : ℝ)*X 2 0+(5265285763/10000000000 : ℝ)*X 2 1+(-223525603/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365642299/10000000000 : ℝ)*X 0 0+(4240109251/10000000000 : ℝ)*X 0 1+(224744011/500000000 : ℝ)*X 0 2+(4365642299/10000000000 : ℝ)*X 1 0+(4240109251/10000000000 : ℝ)*X 1 1+(224744011/500000000 : ℝ)*X 1 2+(4365642299/10000000000 : ℝ)*X 2 0+(4240109251/10000000000 : ℝ)*X 2 1+(224744011/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-434042203/2000000000 : ℝ)*X 0 0+(1053121907/2000000000 : ℝ)*X 0 1+(5393196203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664050271/1250000000 : ℝ)*X 1 0+(-2107345589/10000000000 : ℝ)*X 1 1+(5393196233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062480461/2000000000 : ℝ)*X 2 0+(168537373/312500000 : ℝ)*X 2 1+(-1053672903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436565221/1000000000 : ℝ)*X 0 0+(4494236803/10000000000 : ℝ)*X 0 1+(265047187/625000000 : ℝ)*X 0 2+(436565221/1000000000 : ℝ)*X 1 0+(4494236803/10000000000 : ℝ)*X 1 1+(265047187/625000000 : ℝ)*X 1 2+(436565221/1000000000 : ℝ)*X 2 0+(4494236803/10000000000 : ℝ)*X 2 1+(265047187/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60048027256048979123765763/25750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (299882847/50000000000000 : ℝ)*(base19) + (522009231/100000000000000 : ℝ)*(base23) + (17054429/100000000000000 : ℝ)*(lower2) + (36904659/50000000000000 : ℝ)*(upper3) + (1004211/50000000000000 : ℝ)*(lower4) + (5861651526721513/100000000000000 : ℝ)*(major0) + (5861651526721513/100000000000000 : ℝ)*(major1) + (5861651526721513/100000000000000 : ℝ)*(major2) + (7798174954256321/100000000000000 : ℝ)*(sp0) + (1949547391405143/25000000000000 : ℝ)*(sp1) + (1949547410844259/25000000000000 : ℝ)*(sp2) + (392510268178747/10000000000000 : ℝ)*(sp3) + (7605564973/50000000000000 : ℝ)*(sp4) + (10128537201/100000000000000 : ℝ)*(sp7) + (392511281032467/10000000000000 : ℝ)*(f.failure) + (3899095082693133/50000000000000 : ℝ)*(f.sum) + (44752546566829/13905000000000000000000000000 : ℝ)*base66 + (3276525798543408133/1390500000000000000000000000000000 : ℝ)*base68 + (19316413934125908133/1390500000000000000000000000000000 : ℝ)*base70 + (3494343803839908133/1390500000000000000000000000000000 : ℝ)*base72 + (1830452604173/1738125000000000000000000000 : ℝ)*base74 + (20093412674098091867/1390500000000000000000000000000000 : ℝ)*base75 + (18597086786995908133/1390500000000000000000000000000000 : ℝ)*base78 + (16035124334963591867/1390500000000000000000000000000000 : ℝ)*base79 + (32711607931841/13905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (3203971/250000000000000000000 : ℝ)*base90 + (3203971/250000000000000000000 : ℝ)*base92 + (3203971/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1642243370044129033322524147/231750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (779186381/50000000000000 : ℝ)*(base19) + (2657147/156250000000 : ℝ)*(base23) + (139313/1250000000000 : ℝ)*(upper2) + (38485771/25000000000000 : ℝ)*(upper3) + (94223171/50000000000000 : ℝ)*(upper5) + (5891434161311567/100000000000000 : ℝ)*(major0) + (5891434161311567/100000000000000 : ℝ)*(major1) + (5891434161311567/100000000000000 : ℝ)*(major2) + (918583199/2000000000000 : ℝ)*(sp1) + (6538677279/20000000000000 : ℝ)*(sp2) + (489863253563231/6250000000000 : ℝ)*(sp4) + (1567552913895797/20000000000000 : ℝ)*(sp5) + (3918888831525611/50000000000000 : ℝ)*(sp6) + (986264007350597/25000000000000 : ℝ)*(sp7) + (986264007350597/25000000000000 : ℝ)*(f.failure) + (489863253563231/6250000000000 : ℝ)*(f.sum) + (63053740624241/13905000000000000000000000000 : ℝ)*base66 + (4104757370559675853/1390500000000000000000000000000000 : ℝ)*base67 + (9810111997029675853/1390500000000000000000000000000000 : ℝ)*base69 + (2553281083148324147/1390500000000000000000000000000000 : ℝ)*base72 + (22381638780943/6952500000000000000000000000 : ℝ)*base74 + (3571514557541175853/1390500000000000000000000000000000 : ℝ)*base75 + (5627471387063324147/1390500000000000000000000000000000 : ℝ)*base78 + (21294804141521175853/1390500000000000000000000000000000 : ℝ)*base79 + (51096741706789/13905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4269339/625000000000000000000 : ℝ)*base89 + (4269339/625000000000000000000 : ℝ)*base91 + (4269339/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1135_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1135_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1135_s7_0 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085116713/5000000000 : ℝ)*x 0 + (5393188347/10000000000 : ℝ)*x 1 + (5265600667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085116713/5000000000 : ℝ)^1041 ≤ (13186558962007/100000000000000 : ℝ)^785 := by
    have hnat : (1085116713 : ℕ)^1041*100000000000000^785 ≤ 13186558962007^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085116713 5000000000 13186558962007 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393188347/10000000000 : ℝ)^1041 ≤ (11023931699821/25000000000000 : ℝ)^785 := by
    have hnat : (5393188347 : ℕ)^1041*25000000000000^785 ≤ 11023931699821^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393188347 10000000000 11023931699821 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265600667/10000000000 : ℝ)^1041 ≤ (10679428554083/25000000000000 : ℝ)^785 := by
    have hnat : (5265600667 : ℕ)^1041*25000000000000^785 ≤ 10679428554083^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265600667 10000000000 10679428554083 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085116713/5000000000 : ℝ), (5393188347/10000000000 : ℝ), (5265600667/10000000000 : ℝ)] ![(13186558962007/100000000000000 : ℝ), (11023931699821/25000000000000 : ℝ), (10679428554083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085116713/5000000000 : ℝ)|^1041 ≤ (13186558962007/100000000000000 : ℝ)^785
        have hw : |(-1085116713/5000000000 : ℝ)|=(1085116713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393188347/10000000000 : ℝ)|^1041 ≤ (11023931699821/25000000000000 : ℝ)^785
        have hw : |(5393188347/10000000000 : ℝ)|=(5393188347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265600667/10000000000 : ℝ)|^1041 ≤ (10679428554083/25000000000000 : ℝ)^785
        have hw : |(5265600667/10000000000 : ℝ)|=(5265600667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s7_1 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336197789/2500000000 : ℝ)*x 0 + (-2234950079/10000000000 : ℝ)*x 1 + (1316400169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336197789/2500000000 : ℝ)^1041 ≤ (43571746550167/100000000000000 : ℝ)^785 := by
    have hnat : (1336197789 : ℕ)^1041*100000000000000^785 ≤ 43571746550167^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336197789 2500000000 43571746550167 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2234950079/10000000000 : ℝ)^1041 ≤ (1713817390123/12500000000000 : ℝ)^785 := by
    have hnat : (2234950079 : ℕ)^1041*12500000000000^785 ≤ 1713817390123^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234950079 10000000000 1713817390123 12500000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316400169/2500000000 : ℝ)^1041 ≤ (10679428578289/25000000000000 : ℝ)^785 := by
    have hnat : (1316400169 : ℕ)^1041*25000000000000^785 ≤ 10679428578289^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316400169 2500000000 10679428578289 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336197789/2500000000 : ℝ), (-2234950079/10000000000 : ℝ), (1316400169/2500000000 : ℝ)] ![(43571746550167/100000000000000 : ℝ), (1713817390123/12500000000000 : ℝ), (10679428578289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336197789/2500000000 : ℝ)|^1041 ≤ (43571746550167/100000000000000 : ℝ)^785
        have hw : |(1336197789/2500000000 : ℝ)|=(1336197789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2234950079/10000000000 : ℝ)|^1041 ≤ (1713817390123/12500000000000 : ℝ)^785
        have hw : |(-2234950079/10000000000 : ℝ)|=(2234950079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316400169/2500000000 : ℝ)|^1041 ≤ (10679428578289/25000000000000 : ℝ)^785
        have hw : |(1316400169/2500000000 : ℝ)|=(1316400169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s7_2 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672395419/5000000000 : ℝ)*x 0 + (329100051/625000000 : ℝ)*x 1 + (-2234950317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672395419/5000000000 : ℝ)^1041 ≤ (43571743112353/100000000000000 : ℝ)^785 := by
    have hnat : (2672395419 : ℕ)^1041*100000000000000^785 ≤ 43571743112353^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672395419 5000000000 43571743112353 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329100051/625000000 : ℝ)^1041 ≤ (4271771581931/10000000000000 : ℝ)^785 := by
    have hnat : (329100051 : ℕ)^1041*10000000000000^785 ≤ 4271771581931^785*625000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329100051 625000000 4271771581931 10000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234950317/10000000000 : ℝ)^1041 ≤ (13710541057159/100000000000000 : ℝ)^785 := by
    have hnat : (2234950317 : ℕ)^1041*100000000000000^785 ≤ 13710541057159^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234950317 10000000000 13710541057159 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672395419/5000000000 : ℝ), (329100051/625000000 : ℝ), (-2234950317/10000000000 : ℝ)] ![(43571743112353/100000000000000 : ℝ), (4271771581931/10000000000000 : ℝ), (13710541057159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672395419/5000000000 : ℝ)|^1041 ≤ (43571743112353/100000000000000 : ℝ)^785
        have hw : |(2672395419/5000000000 : ℝ)|=(2672395419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329100051/625000000 : ℝ)|^1041 ≤ (4271771581931/10000000000000 : ℝ)^785
        have hw : |(329100051/625000000 : ℝ)|=(329100051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2234950317/10000000000 : ℝ)|^1041 ≤ (13710541057159/100000000000000 : ℝ)^785
        have hw : |(-2234950317/10000000000 : ℝ)|=(2234950317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s7_3 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2182829341/5000000000 : ℝ)*x 0 + (530093829/1250000000 : ℝ)*x 1 + (4494234671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182829341/5000000000 : ℝ)^1041 ≤ (33316911720839/100000000000000 : ℝ)^785 := by
    have hnat : (2182829341 : ℕ)^1041*100000000000000^785 ≤ 33316911720839^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182829341 5000000000 33316911720839 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530093829/1250000000 : ℝ)^1041 ≤ (32058732938151/100000000000000 : ℝ)^785 := by
    have hnat : (530093829 : ℕ)^1041*100000000000000^785 ≤ 32058732938151^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530093829 1250000000 32058732938151 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494234671/10000000000 : ℝ)^1041 ≤ (34624355329431/100000000000000 : ℝ)^785 := by
    have hnat : (4494234671 : ℕ)^1041*100000000000000^785 ≤ 34624355329431^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494234671 10000000000 34624355329431 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182829341/5000000000 : ℝ), (530093829/1250000000 : ℝ), (4494234671/10000000000 : ℝ)] ![(33316911720839/100000000000000 : ℝ), (32058732938151/100000000000000 : ℝ), (34624355329431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182829341/5000000000 : ℝ)|^1041 ≤ (33316911720839/100000000000000 : ℝ)^785
        have hw : |(2182829341/5000000000 : ℝ)|=(2182829341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530093829/1250000000 : ℝ)|^1041 ≤ (32058732938151/100000000000000 : ℝ)^785
        have hw : |(530093829/1250000000 : ℝ)|=(530093829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494234671/10000000000 : ℝ)|^1041 ≤ (34624355329431/100000000000000 : ℝ)^785
        have hw : |(4494234671/10000000000 : ℝ)|=(4494234671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s7_4 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085119077/5000000000 : ℝ)*x 0 + (5265921299/10000000000 : ℝ)*x 1 + (5392866689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085119077/5000000000 : ℝ)^1041 ≤ (3296649264597/25000000000000 : ℝ)^785 := by
    have hnat : (1085119077 : ℕ)^1041*25000000000000^785 ≤ 3296649264597^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085119077 5000000000 3296649264597 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265921299/10000000000 : ℝ)^1041 ≤ (21360581843017/50000000000000 : ℝ)^785 := by
    have hnat : (5265921299 : ℕ)^1041*50000000000000^785 ≤ 21360581843017^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265921299 10000000000 21360581843017 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392866689/10000000000 : ℝ)^1041 ≤ (44092239235781/100000000000000 : ℝ)^785 := by
    have hnat : (5392866689 : ℕ)^1041*100000000000000^785 ≤ 44092239235781^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392866689 10000000000 44092239235781 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085119077/5000000000 : ℝ), (5265921299/10000000000 : ℝ), (5392866689/10000000000 : ℝ)] ![(3296649264597/25000000000000 : ℝ), (21360581843017/50000000000000 : ℝ), (44092239235781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085119077/5000000000 : ℝ)|^1041 ≤ (3296649264597/25000000000000 : ℝ)^785
        have hw : |(-1085119077/5000000000 : ℝ)|=(1085119077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265921299/10000000000 : ℝ)|^1041 ≤ (21360581843017/50000000000000 : ℝ)^785
        have hw : |(5265921299/10000000000 : ℝ)|=(5265921299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392866689/10000000000 : ℝ)|^1041 ≤ (44092239235781/100000000000000 : ℝ)^785
        have hw : |(5392866689/10000000000 : ℝ)|=(5392866689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s7_5 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312482929/10000000000 : ℝ)*x 0 + (-421536823/2000000000 : ℝ)*x 1 + (1078573337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312482929/10000000000 : ℝ)^1041 ≤ (10805703884491/25000000000000 : ℝ)^785 := by
    have hnat : (5312482929 : ℕ)^1041*25000000000000^785 ≤ 10805703884491^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312482929 10000000000 10805703884491 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421536823/2000000000 : ℝ)^1041 ≤ (12684945253499/100000000000000 : ℝ)^785 := by
    have hnat : (421536823 : ℕ)^1041*100000000000000^785 ≤ 12684945253499^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421536823 2000000000 12684945253499 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078573337/2000000000 : ℝ)^1041 ≤ (11023059798103/25000000000000 : ℝ)^785 := by
    have hnat : (1078573337 : ℕ)^1041*25000000000000^785 ≤ 11023059798103^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078573337 2000000000 11023059798103 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312482929/10000000000 : ℝ), (-421536823/2000000000 : ℝ), (1078573337/2000000000 : ℝ)] ![(10805703884491/25000000000000 : ℝ), (12684945253499/100000000000000 : ℝ), (11023059798103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312482929/10000000000 : ℝ)|^1041 ≤ (10805703884491/25000000000000 : ℝ)^785
        have hw : |(5312482929/10000000000 : ℝ)|=(5312482929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421536823/2000000000 : ℝ)|^1041 ≤ (12684945253499/100000000000000 : ℝ)^785
        have hw : |(-421536823/2000000000 : ℝ)|=(421536823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078573337/2000000000 : ℝ)|^1041 ≤ (11023059798103/25000000000000 : ℝ)^785
        have hw : |(1078573337/2000000000 : ℝ)|=(1078573337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s7_6 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (212499317/400000000 : ℝ)*x 0 + (2696433343/5000000000 : ℝ)*x 1 + (-2107684119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212499317/400000000 : ℝ)^1041 ≤ (21611407747403/50000000000000 : ℝ)^785 := by
    have hnat : (212499317 : ℕ)^1041*50000000000000^785 ≤ 21611407747403^785*400000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212499317 400000000 21611407747403 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696433343/5000000000 : ℝ)^1041 ≤ (22046119601627/50000000000000 : ℝ)^785 := by
    have hnat : (2696433343 : ℕ)^1041*50000000000000^785 ≤ 22046119601627^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696433343 5000000000 22046119601627 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107684119/10000000000 : ℝ)^1041 ≤ (12684945285423/100000000000000 : ℝ)^785 := by
    have hnat : (2107684119 : ℕ)^1041*100000000000000^785 ≤ 12684945285423^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107684119 10000000000 12684945285423 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212499317/400000000 : ℝ), (2696433343/5000000000 : ℝ), (-2107684119/10000000000 : ℝ)] ![(21611407747403/50000000000000 : ℝ), (22046119601627/50000000000000 : ℝ), (12684945285423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212499317/400000000 : ℝ)|^1041 ≤ (21611407747403/50000000000000 : ℝ)^785
        have hw : |(212499317/400000000 : ℝ)|=(212499317/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696433343/5000000000 : ℝ)|^1041 ≤ (22046119601627/50000000000000 : ℝ)^785
        have hw : |(2696433343/5000000000 : ℝ)|=(2696433343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107684119/10000000000 : ℝ)|^1041 ≤ (12684945285423/100000000000000 : ℝ)^785
        have hw : |(-2107684119/10000000000 : ℝ)|=(2107684119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s7_7 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4365668573/10000000000 : ℝ)*x 0 + (561699707/1250000000 : ℝ)*x 1 + (848277961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365668573/10000000000 : ℝ)^1041 ≤ (33317011821373/100000000000000 : ℝ)^785 := by
    have hnat : (4365668573 : ℕ)^1041*100000000000000^785 ≤ 33317011821373^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365668573 10000000000 33317011821373 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561699707/1250000000 : ℝ)^1041 ≤ (34617847342919/100000000000000 : ℝ)^785 := by
    have hnat : (561699707 : ℕ)^1041*100000000000000^785 ≤ 34617847342919^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561699707 1250000000 34617847342919 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848277961/2000000000 : ℝ)^1041 ≤ (16032570404759/50000000000000 : ℝ)^785 := by
    have hnat : (848277961 : ℕ)^1041*50000000000000^785 ≤ 16032570404759^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848277961 2000000000 16032570404759 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365668573/10000000000 : ℝ), (561699707/1250000000 : ℝ), (848277961/2000000000 : ℝ)] ![(33317011821373/100000000000000 : ℝ), (34617847342919/100000000000000 : ℝ), (16032570404759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365668573/10000000000 : ℝ)|^1041 ≤ (33317011821373/100000000000000 : ℝ)^785
        have hw : |(4365668573/10000000000 : ℝ)|=(4365668573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561699707/1250000000 : ℝ)|^1041 ≤ (34617847342919/100000000000000 : ℝ)^785
        have hw : |(561699707/1250000000 : ℝ)|=(561699707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848277961/2000000000 : ℝ)|^1041 ≤ (16032570404759/50000000000000 : ℝ)^785
        have hw : |(848277961/2000000000 : ℝ)|=(848277961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1135_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11343/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7023/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11337/100000 : ℝ) ^ (8327/2048 : ℝ) ≤ (2862180513422221/20000000000000000000 : ℝ) := by
    have hpowers : (11337/100000 : ℝ)^8327 ≤ (2862180513422221/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11337 : ℕ)^8327*20000000000000000000^2048 ≤ 2862180513422221^2048*100000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11337 100000 2862180513422221 20000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11337/100000 : ℝ)) (X := (2862180513422221/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14053/100000 : ℝ) ^ (8327/2048 : ℝ) ≤ (34268796431631367/100000000000000000000 : ℝ) := by
    have hpowers : (14053/100000 : ℝ)^8327 ≤ (34268796431631367/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14053 : ℕ)^8327*100000000000000000000^2048 ≤ 34268796431631367^2048*100000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14053 100000 34268796431631367 100000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14053/100000 : ℝ)) (X := (34268796431631367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002862180513422221/10000000000000000000 : ℝ) ≤ (10000703868529577/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (10002862180513422221/10000000000000000000 : ℝ)^2048 ≤ (10000703868529577/10000000000000000 : ℝ)^8327 := by
      have hnat : (10002862180513422221 : ℕ)^2048*10000000000000000^8327 ≤ 10000703868529577^8327*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002862180513422221 10000000000000000000 10000703868529577 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000703868529577/10000000000000000 : ℝ)) (X := (10002862180513422221/10000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506072462374842809/12500000000000000000 : ℝ) ≤ (10001194583956701/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (12506072462374842809/12500000000000000000 : ℝ)^2048 ≤ (10001194583956701/10000000000000000 : ℝ)^8327 := by
      have hnat : (12506072462374842809 : ℕ)^2048*10000000000000000^8327 ≤ 10001194583956701^8327*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506072462374842809 12500000000000000000 10001194583956701 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001194583956701/10000000000000000 : ℝ)) (X := (12506072462374842809/12500000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034268796431631367/50000000000000000000 : ℝ) ≤ (400067411975353/400000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (50034268796431631367/50000000000000000000 : ℝ)^2048 ≤ (400067411975353/400000000000000 : ℝ)^8327 := by
      have hnat : (50034268796431631367 : ℕ)^2048*400000000000000^8327 ≤ 400067411975353^8327*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034268796431631367 50000000000000000000 400067411975353 400000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400067411975353/400000000000000 : ℝ)) (X := (50034268796431631367/50000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2862180513422221/20000000000000000000 : ℝ) ≤ ((6787696306332930389/6790000000000000000 : ℝ)+2*(122678856781/67900000000000 : ℝ)*(11337/100000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (6787696306332930389/6790000000000000000 : ℝ)+2*(122678856781/67900000000000 : ℝ)*(11337/100000 : ℝ)=(10000703868529577/10000000000000000 : ℝ) by norm_num, show 1+2*(2862180513422221/20000000000000000000 : ℝ)=(10002862180513422221/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34268796431631367/100000000000000000000 : ℝ)+(2862180513422221/20000000000000000000 : ℝ) ≤ ((6787696306332930389/6790000000000000000 : ℝ)+(122678856781/67900000000000 : ℝ)*((14053/100000 : ℝ)+(11337/100000 : ℝ)))^(8327/2048 : ℝ) := by
    rw [show (6787696306332930389/6790000000000000000 : ℝ)+(122678856781/67900000000000 : ℝ)*((14053/100000 : ℝ)+(11337/100000 : ℝ))=(10001194583956701/10000000000000000 : ℝ) by norm_num, show 1+(34268796431631367/100000000000000000000 : ℝ)+(2862180513422221/20000000000000000000 : ℝ)=(12506072462374842809/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34268796431631367/100000000000000000000 : ℝ) ≤ ((6787696306332930389/6790000000000000000 : ℝ)+2*(122678856781/67900000000000 : ℝ)*(14053/100000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (6787696306332930389/6790000000000000000 : ℝ)+2*(122678856781/67900000000000 : ℝ)*(14053/100000 : ℝ)=(400067411975353/400000000000000 : ℝ) by norm_num, show 1+2*(34268796431631367/100000000000000000000 : ℝ)=(50034268796431631367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6787696306332930389/6790000000000000000 : ℝ)*(X 1 0+X 2 0)+(122678856781/67900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (6787696306332930389/6790000000000000000 : ℝ)) (alpha := (122678856781/67900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6787696306332930389/6790000000000000000 : ℝ)*(X 0 1+X 2 1)+(122678856781/67900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (6787696306332930389/6790000000000000000 : ℝ)) (alpha := (122678856781/67900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6787696306332930389/6790000000000000000 : ℝ)*(X 0 2+X 1 2)+(122678856781/67900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (6787696306332930389/6790000000000000000 : ℝ)) (alpha := (122678856781/67900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1085116713/5000000000 : ℝ)*X 0 0+(5393188347/10000000000 : ℝ)*X 0 1+(5265600667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336197789/2500000000 : ℝ)*X 1 0+(-2234950079/10000000000 : ℝ)*X 1 1+(1316400169/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672395419/5000000000 : ℝ)*X 2 0+(329100051/625000000 : ℝ)*X 2 1+(-2234950317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182829341/5000000000 : ℝ)*X 0 0+(530093829/1250000000 : ℝ)*X 0 1+(4494234671/10000000000 : ℝ)*X 0 2+(2182829341/5000000000 : ℝ)*X 1 0+(530093829/1250000000 : ℝ)*X 1 1+(4494234671/10000000000 : ℝ)*X 1 2+(2182829341/5000000000 : ℝ)*X 2 0+(530093829/1250000000 : ℝ)*X 2 1+(4494234671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1085119077/5000000000 : ℝ)*X 0 0+(5265921299/10000000000 : ℝ)*X 0 1+(5392866689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312482929/10000000000 : ℝ)*X 1 0+(-421536823/2000000000 : ℝ)*X 1 1+(1078573337/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212499317/400000000 : ℝ)*X 2 0+(2696433343/5000000000 : ℝ)*X 2 1+(-2107684119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365668573/10000000000 : ℝ)*X 0 0+(561699707/1250000000 : ℝ)*X 0 1+(848277961/2000000000 : ℝ)*X 0 2+(4365668573/10000000000 : ℝ)*X 1 0+(561699707/1250000000 : ℝ)*X 1 1+(848277961/2000000000 : ℝ)*X 1 2+(4365668573/10000000000 : ℝ)*X 2 0+(561699707/1250000000 : ℝ)*X 2 1+(848277961/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (806788623481596115837735329/84875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1892982073/100000000000000 : ℝ)*(base19) + (1417689163/100000000000000 : ℝ)*(base23) + (32007181/50000000000000 : ℝ)*(upper2) + (118499143/25000000000000 : ℝ)*(upper3) + (3440257/5000000000000 : ℝ)*(upper4) + (1472864322938513/25000000000000 : ℝ)*(major0) + (1472864322938513/25000000000000 : ℝ)*(major1) + (1472864322938513/25000000000000 : ℝ)*(major2) + (1567561803663157/20000000000000 : ℝ)*(sp0) + (195946021388251/2500000000000 : ℝ)*(sp1) + (156756826616459/2000000000000 : ℝ)*(sp2) + (1972521447129031/50000000000000 : ℝ)*(sp3) + (33730196327/100000000000000 : ℝ)*(sp4) + (28623884263/100000000000000 : ℝ)*(sp7) + (1972535759071163/50000000000000 : ℝ)*(f.failure) + (489865171782007/6250000000000 : ℝ)*(f.sum) + (3316244348313/3395000000000000000000000000 : ℝ)*base66 + (3346933347041471557/169750000000000000000000000000000 : ℝ)*base67 + (2070349294425221557/169750000000000000000000000000000 : ℝ)*base69 + (2826992773317221557/169750000000000000000000000000000 : ℝ)*base71 + (822488999393/848750000000000000000000000 : ℝ)*base73 + (552575987070721557/169750000000000000000000000000000 : ℝ)*base75 + (343225271417778443/169750000000000000000000000000000 : ℝ)*base78 + (462681203140528443/169750000000000000000000000000000 : ℝ)*base80 + (5983899385353/3395000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2865781/1250000000000000000000 : ℝ)*base89 + (2865781/1250000000000000000000 : ℝ)*base91 + (2865781/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (179604189671640673232931843/24250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (702394591/50000000000000 : ℝ)*(base19) + (751255343/50000000000000 : ℝ)*(base23) + (74778493/50000000000000 : ℝ)*(upper3) + (48293529/100000000000000 : ℝ)*(lower4) + (154699059/100000000000000 : ℝ)*(upper5) + (2960596308501797/50000000000000 : ℝ)*(major0) + (2960596308501797/50000000000000 : ℝ)*(major1) + (2960596308501797/50000000000000 : ℝ)*(major2) + (38855399151/100000000000000 : ℝ)*(sp1) + (40951799877/100000000000000 : ℝ)*(sp2) + (3938700964730617/50000000000000 : ℝ)*(sp4) + (7877361669272901/100000000000000 : ℝ)*(sp5) + (492334967196917/6250000000000 : ℝ)*(sp6) + (792996611533467/20000000000000 : ℝ)*(sp7) + (792996611533467/20000000000000 : ℝ)*(f.failure) + (3938700964730617/50000000000000 : ℝ)*(f.sum) + (825775192987/485000000000000000000000000 : ℝ)*base65 + (430713135835872719/48500000000000000000000000000000 : ℝ)*base67 + (46874326651627281/48500000000000000000000000000000 : ℝ)*base70 + (336415128356872719/48500000000000000000000000000000 : ℝ)*base71 + (1002021163029/242500000000000000000000000 : ℝ)*base74 + (187080214150872719/48500000000000000000000000000000 : ℝ)*base75 + (167543611718372719/48500000000000000000000000000000 : ℝ)*base77 + (303760662577127281/48500000000000000000000000000000 : ℝ)*base80 + (280349462457/121250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2916971/500000000000000000000 : ℝ)*base90 + (2916971/500000000000000000000 : ℝ)*base92 + (2916971/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1135_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1135_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1135_s8_0 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170241279/10000000000 : ℝ)*x 0 + (5393121403/10000000000 : ℝ)*x 1 + (2632831127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170241279/10000000000 : ℝ)^1041 ≤ (3296655559609/25000000000000 : ℝ)^785 := by
    have hnat : (2170241279 : ℕ)^1041*25000000000000^785 ≤ 3296655559609^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170241279 10000000000 3296655559609 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393121403/10000000000 : ℝ)^1041 ≤ (8819000191231/20000000000000 : ℝ)^785 := by
    have hnat : (5393121403 : ℕ)^1041*20000000000000^785 ≤ 8819000191231^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393121403 10000000000 8819000191231 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632831127/5000000000 : ℝ)^1041 ≤ (667474637269/1562500000000 : ℝ)^785 := by
    have hnat : (2632831127 : ℕ)^1041*1562500000000^785 ≤ 667474637269^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632831127 5000000000 667474637269 1562500000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170241279/10000000000 : ℝ), (5393121403/10000000000 : ℝ), (2632831127/5000000000 : ℝ)] ![(3296655559609/25000000000000 : ℝ), (8819000191231/20000000000000 : ℝ), (667474637269/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170241279/10000000000 : ℝ)|^1041 ≤ (3296655559609/25000000000000 : ℝ)^785
        have hw : |(-2170241279/10000000000 : ℝ)|=(2170241279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393121403/10000000000 : ℝ)|^1041 ≤ (8819000191231/20000000000000 : ℝ)^785
        have hw : |(5393121403/10000000000 : ℝ)|=(5393121403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632831127/5000000000 : ℝ)|^1041 ≤ (667474637269/1562500000000 : ℝ)^785
        have hw : |(2632831127/5000000000 : ℝ)|=(2632831127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s8_1 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672386803/5000000000 : ℝ)*x 0 + (-1117445977/5000000000 : ℝ)*x 1 + (658207783/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672386803/5000000000 : ℝ)^1041 ≤ (8714311364367/20000000000000 : ℝ)^785 := by
    have hnat : (2672386803 : ℕ)^1041*20000000000000^785 ≤ 8714311364367^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672386803 5000000000 8714311364367 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117445977/5000000000 : ℝ)^1041 ≤ (2742013252997/20000000000000 : ℝ)^785 := by
    have hnat : (1117445977 : ℕ)^1041*20000000000000^785 ≤ 2742013252997^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117445977 5000000000 2742013252997 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658207783/1250000000 : ℝ)^1041 ≤ (42718376892799/100000000000000 : ℝ)^785 := by
    have hnat : (658207783 : ℕ)^1041*100000000000000^785 ≤ 42718376892799^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658207783 1250000000 42718376892799 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672386803/5000000000 : ℝ), (-1117445977/5000000000 : ℝ), (658207783/1250000000 : ℝ)] ![(8714311364367/20000000000000 : ℝ), (2742013252997/20000000000000 : ℝ), (42718376892799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672386803/5000000000 : ℝ)|^1041 ≤ (8714311364367/20000000000000 : ℝ)^785
        have hw : |(2672386803/5000000000 : ℝ)|=(2672386803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1117445977/5000000000 : ℝ)|^1041 ≤ (2742013252997/20000000000000 : ℝ)^785
        have hw : |(-1117445977/5000000000 : ℝ)|=(1117445977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658207783/1250000000 : ℝ)|^1041 ≤ (42718376892799/100000000000000 : ℝ)^785
        have hw : |(658207783/1250000000 : ℝ)|=(658207783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s8_2 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672386817/5000000000 : ℝ)*x 0 + (1316415563/2500000000 : ℝ)*x 1 + (-2234891933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672386817/5000000000 : ℝ)^1041 ≤ (8714311424907/20000000000000 : ℝ)^785 := by
    have hnat : (2672386817 : ℕ)^1041*20000000000000^785 ≤ 8714311424907^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672386817 5000000000 8714311424907 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316415563/2500000000 : ℝ)^1041 ≤ (427183767637/1000000000000 : ℝ)^785 := by
    have hnat : (1316415563 : ℕ)^1041*1000000000000^785 ≤ 427183767637^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316415563 2500000000 427183767637 1000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234891933/10000000000 : ℝ)^1041 ≤ (3427516523537/25000000000000 : ℝ)^785 := by
    have hnat : (2234891933 : ℕ)^1041*25000000000000^785 ≤ 3427516523537^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234891933 10000000000 3427516523537 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672386817/5000000000 : ℝ), (1316415563/2500000000 : ℝ), (-2234891933/10000000000 : ℝ)] ![(8714311424907/20000000000000 : ℝ), (427183767637/1000000000000 : ℝ), (3427516523537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672386817/5000000000 : ℝ)|^1041 ≤ (8714311424907/20000000000000 : ℝ)^785
        have hw : |(2672386817/5000000000 : ℝ)|=(2672386817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316415563/2500000000 : ℝ)|^1041 ≤ (427183767637/1000000000000 : ℝ)^785
        have hw : |(1316415563/2500000000 : ℝ)|=(1316415563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2234891933/10000000000 : ℝ)|^1041 ≤ (3427516523537/25000000000000 : ℝ)^785
        have hw : |(-2234891933/10000000000 : ℝ)|=(2234891933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s8_3 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1091415517/2500000000 : ℝ)*x 0 + (21204389/50000000 : ℝ)*x 1 + (1123526633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091415517/2500000000 : ℝ)^1041 ≤ (8329236497097/25000000000000 : ℝ)^785 := by
    have hnat : (1091415517 : ℕ)^1041*25000000000000^785 ≤ 8329236497097^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091415517 2500000000 8329236497097 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21204389/50000000 : ℝ)^1041 ≤ (16030003902247/50000000000000 : ℝ)^785 := by
    have hnat : (21204389 : ℕ)^1041*50000000000000^785 ≤ 16030003902247^785*50000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21204389 50000000 16030003902247 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123526633/2500000000 : ℝ)^1041 ≤ (17311523094351/50000000000000 : ℝ)^785 := by
    have hnat : (1123526633 : ℕ)^1041*50000000000000^785 ≤ 17311523094351^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123526633 2500000000 17311523094351 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091415517/2500000000 : ℝ), (21204389/50000000 : ℝ), (1123526633/2500000000 : ℝ)] ![(8329236497097/25000000000000 : ℝ), (16030003902247/50000000000000 : ℝ), (17311523094351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091415517/2500000000 : ℝ)|^1041 ≤ (8329236497097/25000000000000 : ℝ)^785
        have hw : |(1091415517/2500000000 : ℝ)|=(1091415517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21204389/50000000 : ℝ)|^1041 ≤ (16030003902247/50000000000000 : ℝ)^785
        have hw : |(21204389/50000000 : ℝ)|=(21204389/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123526633/2500000000 : ℝ)|^1041 ≤ (17311523094351/50000000000000 : ℝ)^785
        have hw : |(1123526633/2500000000 : ℝ)|=(1123526633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s8_4 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-542561479/2500000000 : ℝ)*x 0 + (210639293/400000000 : ℝ)*x 1 + (2696400183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542561479/2500000000 : ℝ)^1041 ≤ (6593329800809/50000000000000 : ℝ)^785 := by
    have hnat : (542561479 : ℕ)^1041*50000000000000^785 ≤ 6593329800809^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542561479 2500000000 6593329800809 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210639293/400000000 : ℝ)^1041 ≤ (42721820232561/100000000000000 : ℝ)^785 := by
    have hnat : (210639293 : ℕ)^1041*100000000000000^785 ≤ 42721820232561^785*400000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210639293 400000000 42721820232561 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696400183/5000000000 : ℝ)^1041 ≤ (11022880034961/25000000000000 : ℝ)^785 := by
    have hnat : (2696400183 : ℕ)^1041*25000000000000^785 ≤ 11022880034961^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696400183 5000000000 11022880034961 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542561479/2500000000 : ℝ), (210639293/400000000 : ℝ), (2696400183/5000000000 : ℝ)] ![(6593329800809/50000000000000 : ℝ), (42721820232561/100000000000000 : ℝ), (11022880034961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542561479/2500000000 : ℝ)|^1041 ≤ (6593329800809/50000000000000 : ℝ)^785
        have hw : |(-542561479/2500000000 : ℝ)|=(542561479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210639293/400000000 : ℝ)|^1041 ≤ (42721820232561/100000000000000 : ℝ)^785
        have hw : |(210639293/400000000 : ℝ)|=(210639293/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696400183/5000000000 : ℝ)|^1041 ≤ (11022880034961/25000000000000 : ℝ)^785
        have hw : |(2696400183/5000000000 : ℝ)|=(2696400183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s8_5 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (106249963/200000000 : ℝ)*x 0 + (-421550757/2000000000 : ℝ)*x 1 + (2696400127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106249963/200000000 : ℝ)^1041 ≤ (43222979763227/100000000000000 : ℝ)^785 := by
    have hnat : (106249963 : ℕ)^1041*100000000000000^785 ≤ 43222979763227^785*200000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106249963 200000000 43222979763227 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421550757/2000000000 : ℝ)^1041 ≤ (12685501301519/100000000000000 : ℝ)^785 := by
    have hnat : (421550757 : ℕ)^1041*100000000000000^785 ≤ 12685501301519^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421550757 2000000000 12685501301519 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696400127/5000000000 : ℝ)^1041 ≤ (22045759462753/50000000000000 : ℝ)^785 := by
    have hnat : (2696400127 : ℕ)^1041*50000000000000^785 ≤ 22045759462753^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696400127 5000000000 22045759462753 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106249963/200000000 : ℝ), (-421550757/2000000000 : ℝ), (2696400127/5000000000 : ℝ)] ![(43222979763227/100000000000000 : ℝ), (12685501301519/100000000000000 : ℝ), (22045759462753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106249963/200000000 : ℝ)|^1041 ≤ (43222979763227/100000000000000 : ℝ)^785
        have hw : |(106249963/200000000 : ℝ)|=(106249963/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421550757/2000000000 : ℝ)|^1041 ≤ (12685501301519/100000000000000 : ℝ)^785
        have hw : |(-421550757/2000000000 : ℝ)|=(421550757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696400127/5000000000 : ℝ)|^1041 ≤ (22045759462753/50000000000000 : ℝ)^785
        have hw : |(2696400127/5000000000 : ℝ)|=(2696400127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s8_6 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312497993/10000000000 : ℝ)*x 0 + (539280037/1000000000 : ℝ)*x 1 + (-26346923/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312497993/10000000000 : ℝ)^1041 ≤ (43222978069293/100000000000000 : ℝ)^785 := by
    have hnat : (5312497993 : ℕ)^1041*100000000000000^785 ≤ 43222978069293^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312497993 10000000000 43222978069293 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539280037/1000000000 : ℝ)^1041 ≤ (22045760091607/50000000000000 : ℝ)^785 := by
    have hnat : (539280037 : ℕ)^1041*50000000000000^785 ≤ 22045760091607^785*1000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539280037 1000000000 22045760091607 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26346923/125000000 : ℝ)^1041 ≤ (6342750870243/50000000000000 : ℝ)^785 := by
    have hnat : (26346923 : ℕ)^1041*50000000000000^785 ≤ 6342750870243^785*125000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26346923 125000000 6342750870243 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312497993/10000000000 : ℝ), (539280037/1000000000 : ℝ), (-26346923/125000000 : ℝ)] ![(43222978069293/100000000000000 : ℝ), (22045760091607/50000000000000 : ℝ), (6342750870243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312497993/10000000000 : ℝ)|^1041 ≤ (43222978069293/100000000000000 : ℝ)^785
        have hw : |(5312497993/10000000000 : ℝ)|=(5312497993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539280037/1000000000 : ℝ)|^1041 ≤ (22045760091607/50000000000000 : ℝ)^785
        have hw : |(539280037/1000000000 : ℝ)|=(539280037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26346923/125000000 : ℝ)|^1041 ≤ (6342750870243/50000000000000 : ℝ)^785
        have hw : |(-26346923/125000000 : ℝ)|=(26346923/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s8_7 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4365671787/10000000000 : ℝ)*x 0 + (4493470639/10000000000 : ℝ)*x 1 + (4241515993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365671787/10000000000 : ℝ)^1041 ≤ (8329261087061/25000000000000 : ℝ)^785 := by
    have hnat : (4365671787 : ℕ)^1041*25000000000000^785 ≤ 8329261087061^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365671787 10000000000 8329261087061 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493470639/10000000000 : ℝ)^1041 ≤ (17308274862557/50000000000000 : ℝ)^785 := by
    have hnat : (4493470639 : ℕ)^1041*50000000000000^785 ≤ 17308274862557^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493470639 10000000000 17308274862557 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241515993/10000000000 : ℝ)^1041 ≤ (32066405913433/100000000000000 : ℝ)^785 := by
    have hnat : (4241515993 : ℕ)^1041*100000000000000^785 ≤ 32066405913433^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241515993 10000000000 32066405913433 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365671787/10000000000 : ℝ), (4493470639/10000000000 : ℝ), (4241515993/10000000000 : ℝ)] ![(8329261087061/25000000000000 : ℝ), (17308274862557/50000000000000 : ℝ), (32066405913433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365671787/10000000000 : ℝ)|^1041 ≤ (8329261087061/25000000000000 : ℝ)^785
        have hw : |(4365671787/10000000000 : ℝ)|=(4365671787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493470639/10000000000 : ℝ)|^1041 ≤ (17308274862557/50000000000000 : ℝ)^785
        have hw : |(4493470639/10000000000 : ℝ)|=(4493470639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241515993/10000000000 : ℝ)|^1041 ≤ (32066405913433/100000000000000 : ℝ)^785
        have hw : |(4241515993/10000000000 : ℝ)|=(4241515993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1135_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2269/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2809/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11343/100000 : ℝ) ^ (8327/2048 : ℝ) ≤ (14341722456191007/100000000000000000000 : ℝ) := by
    have hpowers : (11343/100000 : ℝ)^8327 ≤ (14341722456191007/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11343 : ℕ)^8327*100000000000000000000^2048 ≤ 14341722456191007^2048*100000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11343 100000 14341722456191007 100000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11343/100000 : ℝ)) (X := (14341722456191007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7023/50000 : ℝ) ^ (8327/2048 : ℝ) ≤ (8549861274279213/25000000000000000000 : ℝ) := by
    have hpowers : (7023/50000 : ℝ)^8327 ≤ (8549861274279213/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7023 : ℕ)^8327*25000000000000000000^2048 ≤ 8549861274279213^2048*50000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7023 50000 8549861274279213 25000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7023/50000 : ℝ)) (X := (8549861274279213/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014341722456191007/50000000000000000000 : ℝ) ≤ (10000705384213473/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (50014341722456191007/50000000000000000000 : ℝ)^2048 ≤ (10000705384213473/10000000000000000 : ℝ)^8327 := by
      have hnat : (50014341722456191007 : ℕ)^2048*10000000000000000^8327 ≤ 10000705384213473^8327*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014341722456191007 50000000000000000000 10000705384213473 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000705384213473/10000000000000000 : ℝ)) (X := (50014341722456191007/50000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048541167553307859/100000000000000000000 : ℝ) ≤ (10001193636634531/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (100048541167553307859/100000000000000000000 : ℝ)^2048 ≤ (10001193636634531/10000000000000000 : ℝ)^8327 := by
      have hnat : (100048541167553307859 : ℕ)^2048*10000000000000000^8327 ≤ 10001193636634531^8327*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048541167553307859 100000000000000000000 10001193636634531 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001193636634531/10000000000000000 : ℝ)) (X := (100048541167553307859/100000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508549861274279213/12500000000000000000 : ℝ) ≤ (10001681889055589/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (12508549861274279213/12500000000000000000 : ℝ)^2048 ≤ (10001681889055589/10000000000000000 : ℝ)^8327 := by
      have hnat : (12508549861274279213 : ℕ)^2048*10000000000000000^8327 ≤ 10001681889055589^8327*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508549861274279213 12500000000000000000 10001681889055589 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001681889055589/10000000000000000 : ℝ)) (X := (12508549861274279213/12500000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14341722456191007/100000000000000000000 : ℝ) ≤ ((9006943386368298577/9010000000000000000 : ℝ)+2*(244126210529/135150000000000 : ℝ)*(11343/100000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (9006943386368298577/9010000000000000000 : ℝ)+2*(244126210529/135150000000000 : ℝ)*(11343/100000 : ℝ)=(10000705384213473/10000000000000000 : ℝ) by norm_num, show 1+2*(14341722456191007/100000000000000000000 : ℝ)=(50014341722456191007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8549861274279213/25000000000000000000 : ℝ)+(14341722456191007/100000000000000000000 : ℝ) ≤ ((9006943386368298577/9010000000000000000 : ℝ)+(244126210529/135150000000000 : ℝ)*((7023/50000 : ℝ)+(11343/100000 : ℝ)))^(8327/2048 : ℝ) := by
    rw [show (9006943386368298577/9010000000000000000 : ℝ)+(244126210529/135150000000000 : ℝ)*((7023/50000 : ℝ)+(11343/100000 : ℝ))=(10001193636634531/10000000000000000 : ℝ) by norm_num, show 1+(8549861274279213/25000000000000000000 : ℝ)+(14341722456191007/100000000000000000000 : ℝ)=(100048541167553307859/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8549861274279213/25000000000000000000 : ℝ) ≤ ((9006943386368298577/9010000000000000000 : ℝ)+2*(244126210529/135150000000000 : ℝ)*(7023/50000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (9006943386368298577/9010000000000000000 : ℝ)+2*(244126210529/135150000000000 : ℝ)*(7023/50000 : ℝ)=(10001681889055589/10000000000000000 : ℝ) by norm_num, show 1+2*(8549861274279213/25000000000000000000 : ℝ)=(12508549861274279213/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9006943386368298577/9010000000000000000 : ℝ)*(X 1 0+X 2 0)+(244126210529/135150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (9006943386368298577/9010000000000000000 : ℝ)) (alpha := (244126210529/135150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9006943386368298577/9010000000000000000 : ℝ)*(X 0 1+X 2 1)+(244126210529/135150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (9006943386368298577/9010000000000000000 : ℝ)) (alpha := (244126210529/135150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9006943386368298577/9010000000000000000 : ℝ)*(X 0 2+X 1 2)+(244126210529/135150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (9006943386368298577/9010000000000000000 : ℝ)) (alpha := (244126210529/135150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2170241279/10000000000 : ℝ)*X 0 0+(5393121403/10000000000 : ℝ)*X 0 1+(2632831127/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672386803/5000000000 : ℝ)*X 1 0+(-1117445977/5000000000 : ℝ)*X 1 1+(658207783/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672386817/5000000000 : ℝ)*X 2 0+(1316415563/2500000000 : ℝ)*X 2 1+(-2234891933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091415517/2500000000 : ℝ)*X 0 0+(21204389/50000000 : ℝ)*X 0 1+(1123526633/2500000000 : ℝ)*X 0 2+(1091415517/2500000000 : ℝ)*X 1 0+(21204389/50000000 : ℝ)*X 1 1+(1123526633/2500000000 : ℝ)*X 1 2+(1091415517/2500000000 : ℝ)*X 2 0+(21204389/50000000 : ℝ)*X 2 1+(1123526633/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-542561479/2500000000 : ℝ)*X 0 0+(210639293/400000000 : ℝ)*X 0 1+(2696400183/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106249963/200000000 : ℝ)*X 1 0+(-421550757/2000000000 : ℝ)*X 1 1+(2696400127/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312497993/10000000000 : ℝ)*X 2 0+(539280037/1000000000 : ℝ)*X 2 1+(-26346923/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365671787/10000000000 : ℝ)*X 0 0+(4493470639/10000000000 : ℝ)*X 0 1+(4241515993/10000000000 : ℝ)*X 0 2+(4365671787/10000000000 : ℝ)*X 1 0+(4493470639/10000000000 : ℝ)*X 1 1+(4241515993/10000000000 : ℝ)*X 1 2+(4365671787/10000000000 : ℝ)*X 2 0+(4493470639/10000000000 : ℝ)*X 2 1+(4241515993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1145002603007522312529532653/450500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301032609/50000000000000 : ℝ)*(base19) + (299700629/50000000000000 : ℝ)*(base23) + (28970587/50000000000000 : ℝ)*(upper3) + (23391749/100000000000000 : ℝ)*(upper4) + (33909361/50000000000000 : ℝ)*(upper5) + (5897352831273663/100000000000000 : ℝ)*(major0) + (5897352831273663/100000000000000 : ℝ)*(major1) + (5897352831273663/100000000000000 : ℝ)*(major2) + (7845667775286309/100000000000000 : ℝ)*(sp0) + (7845685652535863/100000000000000 : ℝ)*(sp1) + (7845685655199823/100000000000000 : ℝ)*(sp2) + (1974504499235673/50000000000000 : ℝ)*(sp3) + (4619828693/25000000000000 : ℝ)*(sp4) + (516237701/5000000000000 : ℝ)*(sp7) + (1974509661612683/50000000000000 : ℝ)*(f.failure) + (7845686254601081/100000000000000 : ℝ)*(f.sum) + (5065854325207/4505000000000000000000000000 : ℝ)*base66 + (4788016457944722449/901000000000000000000000000000000 : ℝ)*base68 + (2055576828392277551/901000000000000000000000000000000 : ℝ)*base69 + (8967084428283722449/901000000000000000000000000000000 : ℝ)*base72 + (411047843893/1126250000000000000000000000 : ℝ)*base74 + (9198531973001722449/901000000000000000000000000000000 : ℝ)*base76 + (16764543213312277551/901000000000000000000000000000000 : ℝ)*base77 + (5242124935013722449/901000000000000000000000000000000 : ℝ)*base80 + (4929033727047/4505000000000000000000000000 : ℝ)*base82 + (2462021/1250000000000000000000 : ℝ)*base89 + (2462021/1250000000000000000000 : ℝ)*base91 + (2462021/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2101013928880611979359/180200000000000000000000000 : ℝ) := by norm_num
    linear_combination (60787471/3125000000000 : ℝ)*(base19) + (274609743/12500000000000 : ℝ)*(base23) + (353933991/50000000000000 : ℝ)*(lower1) + (25002313/25000000000000 : ℝ)*(upper3) + (48674177/20000000000000 : ℝ)*(lower4) + (190942481/100000000000000 : ℝ)*(upper5) + (237083758979313/4000000000000 : ℝ)*(major0) + (237083758979313/4000000000000 : ℝ)*(major1) + (237083758979313/4000000000000 : ℝ)*(major2) + (4378503041/100000000000000 : ℝ)*(sp2) + (7885252801714847/100000000000000 : ℝ)*(sp4) + (315410034260631/4000000000000 : ℝ)*(sp5) + (3942623113166931/50000000000000 : ℝ)*(sp6) + (99223368965149/2500000000000 : ℝ)*(sp7) + (99223368965149/2500000000000 : ℝ)*(f.failure) + (7885252801714847/100000000000000 : ℝ)*(f.sum) + (3289953274139/450500000000000000000000000 : ℝ)*base66 + (2274698406473537601/36040000000000000000000000000000 : ℝ)*base67 + (234909676521142399/36040000000000000000000000000000 : ℝ)*base70 + (1497777026668662399/36040000000000000000000000000000 : ℝ)*base72 + (218362491201/36040000000000000000000000 : ℝ)*base73 + (834823329963062399/36040000000000000000000000000000 : ℝ)*base76 + (109057590022937601/36040000000000000000000000000000 : ℝ)*base77 + (328323680261657601/36040000000000000000000000000000 : ℝ)*base79 + (7933194383657/901000000000000000000000000 : ℝ)*base82 + (138763/62500000000000000000 : ℝ)*base89 + (138763/62500000000000000000 : ℝ)*base91 + (138763/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1135_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1135_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1135_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1135_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1135_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1135_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1135_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
