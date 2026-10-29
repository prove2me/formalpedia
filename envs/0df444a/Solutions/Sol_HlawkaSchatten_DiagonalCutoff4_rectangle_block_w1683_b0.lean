-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1683_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:32:59.906666+00:00
-- url     : https://prove2.me/submissions/39b55428-2fcf-4187-90f2-8380c92a75d0

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
theorem support_rectangle_w1683_s0_0 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-355004971/2500000000 : ℝ)*x 0 + (2877641061/5000000000 : ℝ)*x 1 + (1232363561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355004971/2500000000 : ℝ)^5087 ≤ (8682539136381/100000000000000 : ℝ)^4063 := by
    have hnat : (355004971 : ℕ)^5087*100000000000000^4063 ≤ 8682539136381^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355004971 2500000000 8682539136381 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2877641061/5000000000 : ℝ)^5087 ≤ (50072131887061/100000000000000 : ℝ)^4063 := by
    have hnat : (2877641061 : ℕ)^5087*100000000000000^4063 ≤ 50072131887061^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2877641061 5000000000 50072131887061 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1232363561/2500000000 : ℝ)^5087 ≤ (41245328967309/100000000000000 : ℝ)^4063 := by
    have hnat : (1232363561 : ℕ)^5087*100000000000000^4063 ≤ 41245328967309^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232363561 2500000000 41245328967309 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-355004971/2500000000 : ℝ), (2877641061/5000000000 : ℝ), (1232363561/2500000000 : ℝ)] ![(8682539136381/100000000000000 : ℝ), (50072131887061/100000000000000 : ℝ), (41245328967309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-355004971/2500000000 : ℝ)|^5087 ≤ (8682539136381/100000000000000 : ℝ)^4063
        have hw : |(-355004971/2500000000 : ℝ)|=(355004971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2877641061/5000000000 : ℝ)|^5087 ≤ (50072131887061/100000000000000 : ℝ)^4063
        have hw : |(2877641061/5000000000 : ℝ)|=(2877641061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1232363561/2500000000 : ℝ)|^5087 ≤ (41245328967309/100000000000000 : ℝ)^4063
        have hw : |(1232363561/2500000000 : ℝ)|=(1232363561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s0_1 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5423779563/10000000000 : ℝ)*x 0 + (-467855717/2500000000 : ℝ)*x 1 + (4929455307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5423779563/10000000000 : ℝ)^5087 ≤ (23243848567877/50000000000000 : ℝ)^4063 := by
    have hnat : (5423779563 : ℕ)^5087*50000000000000^4063 ≤ 23243848567877^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423779563 10000000000 23243848567877 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (467855717/2500000000 : ℝ)^5087 ≤ (12266962739827/100000000000000 : ℝ)^4063 := by
    have hnat : (467855717 : ℕ)^5087*100000000000000^4063 ≤ 12266962739827^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467855717 2500000000 12266962739827 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4929455307/10000000000 : ℝ)^5087 ≤ (20622670051589/50000000000000 : ℝ)^4063 := by
    have hnat : (4929455307 : ℕ)^5087*50000000000000^4063 ≤ 20622670051589^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4929455307 10000000000 20622670051589 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5423779563/10000000000 : ℝ), (-467855717/2500000000 : ℝ), (4929455307/10000000000 : ℝ)] ![(23243848567877/50000000000000 : ℝ), (12266962739827/100000000000000 : ℝ), (20622670051589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5423779563/10000000000 : ℝ)|^5087 ≤ (23243848567877/50000000000000 : ℝ)^4063
        have hw : |(5423779563/10000000000 : ℝ)|=(5423779563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-467855717/2500000000 : ℝ)|^5087 ≤ (12266962739827/100000000000000 : ℝ)^4063
        have hw : |(-467855717/2500000000 : ℝ)|=(467855717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4929455307/10000000000 : ℝ)|^5087 ≤ (20622670051589/50000000000000 : ℝ)^4063
        have hw : |(4929455307/10000000000 : ℝ)|=(4929455307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s0_2 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5423781373/10000000000 : ℝ)*x 0 + (1232363557/2500000000 : ℝ)*x 1 + (-1871421879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5423781373/10000000000 : ℝ)^5087 ≤ (9297543311869/20000000000000 : ℝ)^4063 := by
    have hnat : (5423781373 : ℕ)^5087*20000000000000^4063 ≤ 9297543311869^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423781373 10000000000 9297543311869 20000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1232363557/2500000000 : ℝ)^5087 ≤ (20622664399847/50000000000000 : ℝ)^4063 := by
    have hnat : (1232363557 : ℕ)^5087*50000000000000^4063 ≤ 20622664399847^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232363557 2500000000 20622664399847 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871421879/10000000000 : ℝ)^5087 ≤ (12266954623187/100000000000000 : ℝ)^4063 := by
    have hnat : (1871421879 : ℕ)^5087*100000000000000^4063 ≤ 12266954623187^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871421879 10000000000 12266954623187 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5423781373/10000000000 : ℝ), (1232363557/2500000000 : ℝ), (-1871421879/10000000000 : ℝ)] ![(9297543311869/20000000000000 : ℝ), (20622664399847/50000000000000 : ℝ), (12266954623187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5423781373/10000000000 : ℝ)|^5087 ≤ (9297543311869/20000000000000 : ℝ)^4063
        have hw : |(5423781373/10000000000 : ℝ)|=(5423781373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1232363557/2500000000 : ℝ)|^5087 ≤ (20622664399847/50000000000000 : ℝ)^4063
        have hw : |(1232363557/2500000000 : ℝ)|=(1232363557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1871421879/10000000000 : ℝ)|^5087 ≤ (12266954623187/100000000000000 : ℝ)^4063
        have hw : |(-1871421879/10000000000 : ℝ)|=(1871421879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s0_3 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4062761581/10000000000 : ℝ)*x 0 + (1521913623/5000000000 : ℝ)*x 1 + (5291183621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4062761581/10000000000 : ℝ)^5087 ≤ (4047085582277/12500000000000 : ℝ)^4063 := by
    have hnat : (4062761581 : ℕ)^5087*12500000000000^4063 ≤ 4047085582277^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4062761581 10000000000 4047085582277 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1521913623/5000000000 : ℝ)^5087 ≤ (22554129752071/100000000000000 : ℝ)^4063 := by
    have hnat : (1521913623 : ℕ)^5087*100000000000000^4063 ≤ 22554129752071^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521913623 5000000000 22554129752071 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5291183621/10000000000 : ℝ)^5087 ≤ (45069185573667/100000000000000 : ℝ)^4063 := by
    have hnat : (5291183621 : ℕ)^5087*100000000000000^4063 ≤ 45069185573667^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291183621 10000000000 45069185573667 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4062761581/10000000000 : ℝ), (1521913623/5000000000 : ℝ), (5291183621/10000000000 : ℝ)] ![(4047085582277/12500000000000 : ℝ), (22554129752071/100000000000000 : ℝ), (45069185573667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4062761581/10000000000 : ℝ)|^5087 ≤ (4047085582277/12500000000000 : ℝ)^4063
        have hw : |(4062761581/10000000000 : ℝ)|=(4062761581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1521913623/5000000000 : ℝ)|^5087 ≤ (22554129752071/100000000000000 : ℝ)^4063
        have hw : |(1521913623/5000000000 : ℝ)|=(1521913623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5291183621/10000000000 : ℝ)|^5087 ≤ (45069185573667/100000000000000 : ℝ)^4063
        have hw : |(5291183621/10000000000 : ℝ)|=(5291183621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s0_4 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1422165351/10000000000 : ℝ)*x 0 + (2475165703/5000000000 : ℝ)*x 1 + (1433418803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1422165351/10000000000 : ℝ)^5087 ≤ (8698966645829/100000000000000 : ℝ)^4063 := by
    have hnat : (1422165351 : ℕ)^5087*100000000000000^4063 ≤ 8698966645829^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422165351 10000000000 8698966645829 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2475165703/5000000000 : ℝ)^5087 ≤ (41464152378953/100000000000000 : ℝ)^4063 := by
    have hnat : (2475165703 : ℕ)^5087*100000000000000^4063 ≤ 41464152378953^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2475165703 5000000000 41464152378953 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1433418803/2500000000 : ℝ)^5087 ≤ (1993475238499/4000000000000 : ℝ)^4063 := by
    have hnat : (1433418803 : ℕ)^5087*4000000000000^4063 ≤ 1993475238499^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1433418803 2500000000 1993475238499 4000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1422165351/10000000000 : ℝ), (2475165703/5000000000 : ℝ), (1433418803/2500000000 : ℝ)] ![(8698966645829/100000000000000 : ℝ), (41464152378953/100000000000000 : ℝ), (1993475238499/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1422165351/10000000000 : ℝ)|^5087 ≤ (8698966645829/100000000000000 : ℝ)^4063
        have hw : |(-1422165351/10000000000 : ℝ)|=(1422165351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2475165703/5000000000 : ℝ)|^5087 ≤ (41464152378953/100000000000000 : ℝ)^4063
        have hw : |(2475165703/5000000000 : ℝ)|=(2475165703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1433418803/2500000000 : ℝ)|^5087 ≤ (1993475238499/4000000000000 : ℝ)^4063
        have hw : |(1433418803/2500000000 : ℝ)|=(1433418803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s0_5 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199264577/10000000000 : ℝ)*x 0 + (-533601217/5000000000 : ℝ)*x 1 + (5733675359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199264577/10000000000 : ℝ)^5087 ≤ (22045533671041/50000000000000 : ℝ)^4063 := by
    have hnat : (5199264577 : ℕ)^5087*50000000000000^4063 ≤ 22045533671041^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199264577 10000000000 22045533671041 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533601217/5000000000 : ℝ)^5087 ≤ (6072050085849/100000000000000 : ℝ)^4063 := by
    have hnat : (533601217 : ℕ)^5087*100000000000000^4063 ≤ 6072050085849^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533601217 5000000000 6072050085849 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5733675359/10000000000 : ℝ)^5087 ≤ (49836882562217/100000000000000 : ℝ)^4063 := by
    have hnat : (5733675359 : ℕ)^5087*100000000000000^4063 ≤ 49836882562217^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5733675359 10000000000 49836882562217 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199264577/10000000000 : ℝ), (-533601217/5000000000 : ℝ), (5733675359/10000000000 : ℝ)] ![(22045533671041/50000000000000 : ℝ), (6072050085849/100000000000000 : ℝ), (49836882562217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199264577/10000000000 : ℝ)|^5087 ≤ (22045533671041/50000000000000 : ℝ)^4063
        have hw : |(5199264577/10000000000 : ℝ)|=(5199264577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533601217/5000000000 : ℝ)|^5087 ≤ (6072050085849/100000000000000 : ℝ)^4063
        have hw : |(-533601217/5000000000 : ℝ)|=(533601217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5733675359/10000000000 : ℝ)|^5087 ≤ (49836882562217/100000000000000 : ℝ)^4063
        have hw : |(5733675359/10000000000 : ℝ)|=(5733675359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s0_6 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199264583/10000000000 : ℝ)*x 0 + (1146735077/2000000000 : ℝ)*x 1 + (-66700149/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199264583/10000000000 : ℝ)^5087 ≤ (11022766851447/25000000000000 : ℝ)^4063 := by
    have hnat : (5199264583 : ℕ)^5087*25000000000000^4063 ≤ 11022766851447^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199264583 10000000000 11022766851447 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146735077/2000000000 : ℝ)^5087 ≤ (12459220711291/25000000000000 : ℝ)^4063 := by
    have hnat : (1146735077 : ℕ)^5087*25000000000000^4063 ≤ 12459220711291^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146735077 2000000000 12459220711291 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66700149/625000000 : ℝ)^5087 ≤ (3036024864833/50000000000000 : ℝ)^4063 := by
    have hnat : (66700149 : ℕ)^5087*50000000000000^4063 ≤ 3036024864833^4063*625000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66700149 625000000 3036024864833 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199264583/10000000000 : ℝ), (1146735077/2000000000 : ℝ), (-66700149/625000000 : ℝ)] ![(11022766851447/25000000000000 : ℝ), (12459220711291/25000000000000 : ℝ), (3036024864833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199264583/10000000000 : ℝ)|^5087 ≤ (11022766851447/25000000000000 : ℝ)^4063
        have hw : |(5199264583/10000000000 : ℝ)|=(5199264583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1146735077/2000000000 : ℝ)|^5087 ≤ (12459220711291/25000000000000 : ℝ)^4063
        have hw : |(1146735077/2000000000 : ℝ)|=(1146735077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66700149/625000000 : ℝ)|^5087 ≤ (3036024864833/50000000000000 : ℝ)^4063
        have hw : |(-66700149/625000000 : ℝ)|=(66700149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s0_7 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2034299917/5000000000 : ℝ)*x 0 + (5234369131/10000000000 : ℝ)*x 1 + (775656531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2034299917/5000000000 : ℝ)^5087 ≤ (8108736734493/25000000000000 : ℝ)^4063 := by
    have hnat : (2034299917 : ℕ)^5087*25000000000000^4063 ≤ 8108736734493^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034299917 5000000000 8108736734493 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234369131/10000000000 : ℝ)^5087 ≤ (44464107687633/100000000000000 : ℝ)^4063 := by
    have hnat : (5234369131 : ℕ)^5087*100000000000000^4063 ≤ 44464107687633^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234369131 10000000000 44464107687633 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (775656531/2500000000 : ℝ)^5087 ≤ (2887618170481/12500000000000 : ℝ)^4063 := by
    have hnat : (775656531 : ℕ)^5087*12500000000000^4063 ≤ 2887618170481^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775656531 2500000000 2887618170481 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2034299917/5000000000 : ℝ), (5234369131/10000000000 : ℝ), (775656531/2500000000 : ℝ)] ![(8108736734493/25000000000000 : ℝ), (44464107687633/100000000000000 : ℝ), (2887618170481/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2034299917/5000000000 : ℝ)|^5087 ≤ (8108736734493/25000000000000 : ℝ)^4063
        have hw : |(2034299917/5000000000 : ℝ)|=(2034299917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234369131/10000000000 : ℝ)|^5087 ≤ (44464107687633/100000000000000 : ℝ)^4063
        have hw : |(5234369131/10000000000 : ℝ)|=(5234369131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(775656531/2500000000 : ℝ)|^5087 ≤ (2887618170481/12500000000000 : ℝ)^4063
        have hw : |(775656531/2500000000 : ℝ)|=(775656531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1683_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5197/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22909/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5079/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5079 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5079*1^1024 ≤ 0^1024*1^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5079/1024 : ℝ) ≤ (1062265560468447267/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5079 ≤ (1062265560468447267/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5079*100000000000000000000^1024 ≤ 1062265560468447267^1024*5^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1062265560468447267 100000000000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1062265560468447267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5079 := by
      have hnat : (1 : ℕ)^1024*1^5079 ≤ 1^5079*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101062265560468447267/100000000000000000000 : ℝ) ≤ (10021326569364641/10000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (101062265560468447267/100000000000000000000 : ℝ)^1024 ≤ (10021326569364641/10000000000000000 : ℝ)^5079 := by
      have hnat : (101062265560468447267 : ℕ)^1024*10000000000000000^5079 ≤ 10021326569364641^5079*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101062265560468447267 100000000000000000000 10021326569364641 10000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10021326569364641/10000000000000000 : ℝ)) (X := (101062265560468447267/100000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51062265560468447267/50000000000000000000 : ℝ) ≤ (5021326569364641/5000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (51062265560468447267/50000000000000000000 : ℝ)^1024 ≤ (5021326569364641/5000000000000000 : ℝ)^5079 := by
      have hnat : (51062265560468447267 : ℕ)^1024*5000000000000000^5079 ≤ 5021326569364641^5079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51062265560468447267 50000000000000000000 5021326569364641 5000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5021326569364641/5000000000000000 : ℝ)) (X := (51062265560468447267/50000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(21326569364641/4000000000000000 : ℝ)*(0 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21326569364641/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1062265560468447267/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(21326569364641/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5079/1024 : ℝ) := by
    rw [show (1 : ℝ)+(21326569364641/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10021326569364641/10000000000000000 : ℝ) by norm_num, show 1+(1062265560468447267/100000000000000000000 : ℝ)+(0 : ℝ)=(101062265560468447267/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1062265560468447267/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(21326569364641/4000000000000000 : ℝ)*(2/5 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21326569364641/4000000000000000 : ℝ)*(2/5 : ℝ)=(5021326569364641/5000000000000000 : ℝ) by norm_num, show 1+2*(1062265560468447267/100000000000000000000 : ℝ)=(51062265560468447267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(21326569364641/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21326569364641/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(21326569364641/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21326569364641/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(21326569364641/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21326569364641/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-355004971/2500000000 : ℝ)*X 0 0+(2877641061/5000000000 : ℝ)*X 0 1+(1232363561/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5423779563/10000000000 : ℝ)*X 1 0+(-467855717/2500000000 : ℝ)*X 1 1+(4929455307/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5423781373/10000000000 : ℝ)*X 2 0+(1232363557/2500000000 : ℝ)*X 2 1+(-1871421879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4062761581/10000000000 : ℝ)*X 0 0+(1521913623/5000000000 : ℝ)*X 0 1+(5291183621/10000000000 : ℝ)*X 0 2+(4062761581/10000000000 : ℝ)*X 1 0+(1521913623/5000000000 : ℝ)*X 1 1+(5291183621/10000000000 : ℝ)*X 1 2+(4062761581/10000000000 : ℝ)*X 2 0+(1521913623/5000000000 : ℝ)*X 2 1+(5291183621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1422165351/10000000000 : ℝ)*X 0 0+(2475165703/5000000000 : ℝ)*X 0 1+(1433418803/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5199264577/10000000000 : ℝ)*X 1 0+(-533601217/5000000000 : ℝ)*X 1 1+(5733675359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5199264583/10000000000 : ℝ)*X 2 0+(1146735077/2000000000 : ℝ)*X 2 1+(-66700149/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2034299917/5000000000 : ℝ)*X 0 0+(5234369131/10000000000 : ℝ)*X 0 1+(775656531/2500000000 : ℝ)*X 0 2+(2034299917/5000000000 : ℝ)*X 1 0+(5234369131/10000000000 : ℝ)*X 1 1+(775656531/2500000000 : ℝ)*X 1 2+(2034299917/5000000000 : ℝ)*X 2 0+(5234369131/10000000000 : ℝ)*X 2 1+(775656531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34529689909782373393467/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4078341/10000000000000 : ℝ)*(base1) + (167788553/25000000000000 : ℝ)*(base19) + (987852993/100000000000000 : ℝ)*(base23) + (87402067/100000000000000 : ℝ)*(base24) + (79019283/50000000000000 : ℝ)*(upper5) + (165588554489929/20000000000000 : ℝ)*(major0) + (165588554489929/20000000000000 : ℝ)*(major1) + (165588554489929/20000000000000 : ℝ)*(major2) + (605454651877039/50000000000000 : ℝ)*(sp0) + (1210914173963821/100000000000000 : ℝ)*(sp1) + (1210913769862973/100000000000000 : ℝ)*(sp2) + (111242239244189/25000000000000 : ℝ)*(sp3) + (1116429473/20000000000000 : ℝ)*(sp4) + (12465179/800000000000 : ℝ)*(sp7) + (444970555907541/100000000000000 : ℝ)*(f.failure) + (605457422559017/50000000000000 : ℝ)*(f.sum) + (60251033559511/40000000000000000000000000000 : ℝ)*base66 + (647503741359511/80000000000000000000000000000 : ℝ)*base68 + (141515547839511/80000000000000000000000000000 : ℝ)*base70 + (413321613519511/80000000000000000000000000000 : ℝ)*base72 + (218323295719511/40000000000000000000000000000 : ℝ)*base74 + (75010481360489/80000000000000000000000000000 : ℝ)*base75 + (627610549999511/80000000000000000000000000000 : ℝ)*base78 + (228132632399511/80000000000000000000000000000 : ℝ)*base80 + (182788705159511/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4455953/10000000000000000000000 : ℝ)*base90 + (4455953/10000000000000000000000 : ℝ)*base92 + (4455953/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (195605371540806597528063/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1946437763/100000000000000 : ℝ)*(base19) + (491352673/25000000000000 : ℝ)*(base23) + (21668771/25000000000000 : ℝ)*(base32) + (165679699/50000000000000 : ℝ)*(upper3) + (12788563/5000000000000 : ℝ)*(upper5) + (218209740985113/25000000000000 : ℝ)*(major0) + (218209740985113/25000000000000 : ℝ)*(major1) + (872838963940453/100000000000000 : ℝ)*(major2) + (1609695743/25000000000000 : ℝ)*(sp1) + (6843982983/100000000000000 : ℝ)*(sp2) + (39893061968809/3125000000000 : ℝ)*(sp4) + (1276569597781153/100000000000000 : ℝ)*(sp5) + (1276569173608213/100000000000000 : ℝ)*(sp6) + (117274883048743/25000000000000 : ℝ)*(sp7) + (93819923774011/20000000000000 : ℝ)*(f.failure) + (39893061968809/3125000000000 : ℝ)*(f.sum) + (114379083583979/80000000000000000000000000000 : ℝ)*base66 + (6718115576277627/400000000000000000000000000000 : ℝ)*base68 + (182184971189433/100000000000000000000000000000 : ℝ)*base69 + (3125335298277627/400000000000000000000000000000 : ℝ)*base72 + (921245265503979/80000000000000000000000000000 : ℝ)*base74 + (441930863689433/100000000000000000000000000000 : ℝ)*base75 + (764273199010567/100000000000000000000000000000 : ℝ)*base78 + (1094624996510567/100000000000000000000000000000 : ℝ)*base80 + (166629334360567/50000000000000000000000000000 : ℝ)*base82 + (2793537/2000000000000000000000 : ℝ)*base89 + (2793537/2000000000000000000000 : ℝ)*base91 + (17206463/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1683_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5197/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22909/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1683_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1683_s1_0 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1509423953/10000000000 : ℝ)*x 0 + (5513850487/10000000000 : ℝ)*x 1 + (5112463801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1509423953/10000000000 : ℝ)^5087 ≤ (4686154593107/50000000000000 : ℝ)^4063 := by
    have hnat : (1509423953 : ℕ)^5087*50000000000000^4063 ≤ 4686154593107^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509423953 10000000000 4686154593107 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5513850487/10000000000 : ℝ)^5087 ≤ (5932035814671/12500000000000 : ℝ)^4063 := by
    have hnat : (5513850487 : ℕ)^5087*12500000000000^4063 ≤ 5932035814671^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513850487 10000000000 5932035814671 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5112463801/10000000000 : ℝ)^5087 ≤ (10792851068669/25000000000000 : ℝ)^4063 := by
    have hnat : (5112463801 : ℕ)^5087*25000000000000^4063 ≤ 10792851068669^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112463801 10000000000 10792851068669 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1509423953/10000000000 : ℝ), (5513850487/10000000000 : ℝ), (5112463801/10000000000 : ℝ)] ![(4686154593107/50000000000000 : ℝ), (5932035814671/12500000000000 : ℝ), (10792851068669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1509423953/10000000000 : ℝ)|^5087 ≤ (4686154593107/50000000000000 : ℝ)^4063
        have hw : |(-1509423953/10000000000 : ℝ)|=(1509423953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5513850487/10000000000 : ℝ)|^5087 ≤ (5932035814671/12500000000000 : ℝ)^4063
        have hw : |(5513850487/10000000000 : ℝ)|=(5513850487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5112463801/10000000000 : ℝ)|^5087 ≤ (10792851068669/25000000000000 : ℝ)^4063
        have hw : |(5112463801/10000000000 : ℝ)|=(5112463801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s1_1 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359455631/10000000000 : ℝ)*x 0 + (-171912349/1000000000 : ℝ)*x 1 + (5112463673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359455631/10000000000 : ℝ)^5087 ≤ (11449613664561/25000000000000 : ℝ)^4063 := by
    have hnat : (5359455631 : ℕ)^5087*25000000000000^4063 ≤ 11449613664561^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359455631 10000000000 11449613664561 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171912349/1000000000 : ℝ)^5087 ≤ (5515071201983/50000000000000 : ℝ)^4063 := by
    have hnat : (171912349 : ℕ)^5087*50000000000000^4063 ≤ 5515071201983^4063*1000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171912349 1000000000 5515071201983 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5112463673/10000000000 : ℝ)^5087 ≤ (21585701460693/50000000000000 : ℝ)^4063 := by
    have hnat : (5112463673 : ℕ)^5087*50000000000000^4063 ≤ 21585701460693^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112463673 10000000000 21585701460693 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359455631/10000000000 : ℝ), (-171912349/1000000000 : ℝ), (5112463673/10000000000 : ℝ)] ![(11449613664561/25000000000000 : ℝ), (5515071201983/50000000000000 : ℝ), (21585701460693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359455631/10000000000 : ℝ)|^5087 ≤ (11449613664561/25000000000000 : ℝ)^4063
        have hw : |(5359455631/10000000000 : ℝ)|=(5359455631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-171912349/1000000000 : ℝ)|^5087 ≤ (5515071201983/50000000000000 : ℝ)^4063
        have hw : |(-171912349/1000000000 : ℝ)|=(171912349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5112463673/10000000000 : ℝ)|^5087 ≤ (21585701460693/50000000000000 : ℝ)^4063
        have hw : |(5112463673/10000000000 : ℝ)|=(5112463673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s1_2 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339863763/2500000000 : ℝ)*x 0 + (5112464197/10000000000 : ℝ)*x 1 + (-429780893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339863763/2500000000 : ℝ)^5087 ≤ (5724806057937/12500000000000 : ℝ)^4063 := by
    have hnat : (1339863763 : ℕ)^5087*12500000000000^4063 ≤ 5724806057937^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339863763 2500000000 5724806057937 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5112464197/10000000000 : ℝ)^5087 ≤ (5396426057677/12500000000000 : ℝ)^4063 := by
    have hnat : (5112464197 : ℕ)^5087*12500000000000^4063 ≤ 5396426057677^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112464197 10000000000 5396426057677 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429780893/2500000000 : ℝ)^5087 ≤ (11030143062689/100000000000000 : ℝ)^4063 := by
    have hnat : (429780893 : ℕ)^5087*100000000000000^4063 ≤ 11030143062689^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429780893 2500000000 11030143062689 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339863763/2500000000 : ℝ), (5112464197/10000000000 : ℝ), (-429780893/2500000000 : ℝ)] ![(5724806057937/12500000000000 : ℝ), (5396426057677/12500000000000 : ℝ), (11030143062689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339863763/2500000000 : ℝ)|^5087 ≤ (5724806057937/12500000000000 : ℝ)^4063
        have hw : |(1339863763/2500000000 : ℝ)|=(1339863763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5112464197/10000000000 : ℝ)|^5087 ≤ (5396426057677/12500000000000 : ℝ)^4063
        have hw : |(5112464197/10000000000 : ℝ)|=(5112464197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429780893/2500000000 : ℝ)|^5087 ≤ (11030143062689/100000000000000 : ℝ)^4063
        have hw : |(-429780893/2500000000 : ℝ)|=(429780893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s1_3 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4135979037/10000000000 : ℝ)*x 0 + (903583727/2500000000 : ℝ)*x 1 + (4706643197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135979037/10000000000 : ℝ)^5087 ≤ (33108870563703/100000000000000 : ℝ)^4063 := by
    have hnat : (4135979037 : ℕ)^5087*100000000000000^4063 ≤ 33108870563703^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135979037 10000000000 33108870563703 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903583727/2500000000 : ℝ)^5087 ≤ (27966496168959/100000000000000 : ℝ)^4063 := by
    have hnat : (903583727 : ℕ)^5087*100000000000000^4063 ≤ 27966496168959^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903583727 2500000000 27966496168959 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4706643197/10000000000 : ℝ)^5087 ≤ (38924633259067/100000000000000 : ℝ)^4063 := by
    have hnat : (4706643197 : ℕ)^5087*100000000000000^4063 ≤ 38924633259067^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4706643197 10000000000 38924633259067 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135979037/10000000000 : ℝ), (903583727/2500000000 : ℝ), (4706643197/10000000000 : ℝ)] ![(33108870563703/100000000000000 : ℝ), (27966496168959/100000000000000 : ℝ), (38924633259067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135979037/10000000000 : ℝ)|^5087 ≤ (33108870563703/100000000000000 : ℝ)^4063
        have hw : |(4135979037/10000000000 : ℝ)|=(4135979037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903583727/2500000000 : ℝ)|^5087 ≤ (27966496168959/100000000000000 : ℝ)^4063
        have hw : |(903583727/2500000000 : ℝ)|=(903583727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4706643197/10000000000 : ℝ)|^5087 ≤ (38924633259067/100000000000000 : ℝ)^4063
        have hw : |(4706643197/10000000000 : ℝ)|=(4706643197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s1_4 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1509666889/10000000000 : ℝ)*x 0 + (639672613/1250000000 : ℝ)*x 1 + (2754424871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1509666889/10000000000 : ℝ)^5087 ≤ (468709891699/5000000000000 : ℝ)^4063 := by
    have hnat : (1509666889 : ℕ)^5087*5000000000000^4063 ≤ 468709891699^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509666889 10000000000 468709891699 5000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639672613/1250000000 : ℝ)^5087 ≤ (2701462313911/6250000000000 : ℝ)^4063 := by
    have hnat : (639672613 : ℕ)^5087*6250000000000^4063 ≤ 2701462313911^4063*1250000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639672613 1250000000 2701462313911 6250000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754424871/5000000000 : ℝ)^5087 ≤ (23701202566747/50000000000000 : ℝ)^4063 := by
    have hnat : (2754424871 : ℕ)^5087*50000000000000^4063 ≤ 23701202566747^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754424871 5000000000 23701202566747 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1509666889/10000000000 : ℝ), (639672613/1250000000 : ℝ), (2754424871/5000000000 : ℝ)] ![(468709891699/5000000000000 : ℝ), (2701462313911/6250000000000 : ℝ), (23701202566747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1509666889/10000000000 : ℝ)|^5087 ≤ (468709891699/5000000000000 : ℝ)^4063
        have hw : |(-1509666889/10000000000 : ℝ)|=(1509666889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(639672613/1250000000 : ℝ)|^5087 ≤ (2701462313911/6250000000000 : ℝ)^4063
        have hw : |(639672613/1250000000 : ℝ)|=(639672613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754424871/5000000000 : ℝ)|^5087 ≤ (23701202566747/50000000000000 : ℝ)^4063
        have hw : |(2754424871/5000000000 : ℝ)|=(2754424871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s1_5 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313035987/2500000000 : ℝ)*x 0 + (-330684609/2500000000 : ℝ)*x 1 + (2754425197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313035987/2500000000 : ℝ)^5087 ≤ (22326616778131/50000000000000 : ℝ)^4063 := by
    have hnat : (1313035987 : ℕ)^5087*50000000000000^4063 ≤ 22326616778131^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313035987 2500000000 22326616778131 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330684609/2500000000 : ℝ)^5087 ≤ (1588870853559/20000000000000 : ℝ)^4063 := by
    have hnat : (330684609 : ℕ)^5087*20000000000000^4063 ≤ 1588870853559^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330684609 2500000000 1588870853559 20000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754425197/5000000000 : ℝ)^5087 ≤ (2962650759861/6250000000000 : ℝ)^4063 := by
    have hnat : (2754425197 : ℕ)^5087*6250000000000^4063 ≤ 2962650759861^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754425197 5000000000 2962650759861 6250000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313035987/2500000000 : ℝ), (-330684609/2500000000 : ℝ), (2754425197/5000000000 : ℝ)] ![(22326616778131/50000000000000 : ℝ), (1588870853559/20000000000000 : ℝ), (2962650759861/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313035987/2500000000 : ℝ)|^5087 ≤ (22326616778131/50000000000000 : ℝ)^4063
        have hw : |(1313035987/2500000000 : ℝ)|=(1313035987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-330684609/2500000000 : ℝ)|^5087 ≤ (1588870853559/20000000000000 : ℝ)^4063
        have hw : |(-330684609/2500000000 : ℝ)|=(330684609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754425197/5000000000 : ℝ)|^5087 ≤ (2962650759861/6250000000000 : ℝ)^4063
        have hw : |(2754425197/5000000000 : ℝ)|=(2754425197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s1_6 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13130361/25000000 : ℝ)*x 0 + (43037893/78125000 : ℝ)*x 1 + (-52909517/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13130361/25000000 : ℝ)^5087 ≤ (22326619183821/50000000000000 : ℝ)^4063 := by
    have hnat : (13130361 : ℕ)^5087*50000000000000^4063 ≤ 22326619183821^4063*25000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13130361 25000000 22326619183821 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43037893/78125000 : ℝ)^5087 ≤ (47402411188167/100000000000000 : ℝ)^4063 := by
    have hnat : (43037893 : ℕ)^5087*100000000000000^4063 ≤ 47402411188167^4063*78125000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43037893 78125000 47402411188167 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52909517/400000000 : ℝ)^5087 ≤ (7944350425237/100000000000000 : ℝ)^4063 := by
    have hnat : (52909517 : ℕ)^5087*100000000000000^4063 ≤ 7944350425237^4063*400000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52909517 400000000 7944350425237 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13130361/25000000 : ℝ), (43037893/78125000 : ℝ), (-52909517/400000000 : ℝ)] ![(22326619183821/50000000000000 : ℝ), (47402411188167/100000000000000 : ℝ), (7944350425237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13130361/25000000 : ℝ)|^5087 ≤ (22326619183821/50000000000000 : ℝ)^4063
        have hw : |(13130361/25000000 : ℝ)|=(13130361/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43037893/78125000 : ℝ)|^5087 ≤ (47402411188167/100000000000000 : ℝ)^4063
        have hw : |(43037893/78125000 : ℝ)|=(43037893/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52909517/400000000 : ℝ)|^5087 ≤ (7944350425237/100000000000000 : ℝ)^4063
        have hw : |(-52909517/400000000 : ℝ)|=(52909517/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s1_7 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (827328013/2000000000 : ℝ)*x 0 + (469326087/1000000000 : ℝ)*x 1 + (906985677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827328013/2000000000 : ℝ)^5087 ≤ (33115495924821/100000000000000 : ℝ)^4063 := by
    have hnat : (827328013 : ℕ)^5087*100000000000000^4063 ≤ 33115495924821^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827328013 2000000000 33115495924821 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469326087/1000000000 : ℝ)^5087 ≤ (1551444637807/4000000000000 : ℝ)^4063 := by
    have hnat : (469326087 : ℕ)^5087*4000000000000^4063 ≤ 1551444637807^4063*1000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469326087 1000000000 1551444637807 4000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906985677/2500000000 : ℝ)^5087 ≤ (14049194061801/50000000000000 : ℝ)^4063 := by
    have hnat : (906985677 : ℕ)^5087*50000000000000^4063 ≤ 14049194061801^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906985677 2500000000 14049194061801 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(827328013/2000000000 : ℝ), (469326087/1000000000 : ℝ), (906985677/2500000000 : ℝ)] ![(33115495924821/100000000000000 : ℝ), (1551444637807/4000000000000 : ℝ), (14049194061801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(827328013/2000000000 : ℝ)|^5087 ≤ (33115495924821/100000000000000 : ℝ)^4063
        have hw : |(827328013/2000000000 : ℝ)|=(827328013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(469326087/1000000000 : ℝ)|^5087 ≤ (1551444637807/4000000000000 : ℝ)^4063
        have hw : |(469326087/1000000000 : ℝ)|=(469326087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(906985677/2500000000 : ℝ)|^5087 ≤ (14049194061801/50000000000000 : ℝ)^4063
        have hw : |(906985677/2500000000 : ℝ)|=(906985677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1683_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (929/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (713/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22909/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5197/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22909/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5197/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22909/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5197/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22909/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5197/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22909/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5197/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22909/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5197/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5197/100000 : ℝ) ^ (5079/1024 : ℝ) ≤ (1066899840059/2500000000000000000 : ℝ) := by
    have hpowers : (5197/100000 : ℝ)^5079 ≤ (1066899840059/2500000000000000000 : ℝ)^1024 := by
      have hnat : (5197 : ℕ)^5079*2500000000000000000^1024 ≤ 1066899840059^1024*100000^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5197 100000 1066899840059 2500000000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5197/100000 : ℝ)) (X := (1066899840059/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22909/100000 : ℝ) ^ (5079/1024 : ℝ) ≤ (6693533104159643/10000000000000000000 : ℝ) := by
    have hpowers : (22909/100000 : ℝ)^5079 ≤ (6693533104159643/10000000000000000000 : ℝ)^1024 := by
      have hnat : (22909 : ℕ)^5079*10000000000000000000^1024 ≤ 6693533104159643^1024*100000^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22909 100000 6693533104159643 10000000000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22909/100000 : ℝ)) (X := (6693533104159643/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250001066899840059/1250000000000000000 : ℝ) ≤ (250000043020479/250000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (1250001066899840059/1250000000000000000 : ℝ)^1024 ≤ (250000043020479/250000000000000 : ℝ)^5079 := by
      have hnat : (1250001066899840059 : ℕ)^1024*250000000000000^5079 ≤ 250000043020479^5079*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250001066899840059 1250000000000000000 250000043020479 250000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000043020479/250000000000000 : ℝ)) (X := (1250001066899840059/1250000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10006697800703519879/10000000000000000000 : ℝ) ≤ (12501687515967/12500000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (10006697800703519879/10000000000000000000 : ℝ)^1024 ≤ (12501687515967/12500000000000 : ℝ)^5079 := by
      have hnat : (10006697800703519879 : ℕ)^1024*12500000000000^5079 ≤ 12501687515967^5079*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006697800703519879 10000000000000000000 12501687515967 12500000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12501687515967/12500000000000 : ℝ)) (X := (10006697800703519879/10000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5006693533104159643/5000000000000000000 : ℝ) ≤ (250067457618201/250000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (5006693533104159643/5000000000000000000 : ℝ)^1024 ≤ (250067457618201/250000000000000 : ℝ)^5079 := by
      have hnat : (5006693533104159643 : ℕ)^1024*250000000000000^5079 ≤ 250067457618201^5079*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5006693533104159643 5000000000000000000 250067457618201 250000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250067457618201/250000000000000 : ℝ)) (X := (5006693533104159643/5000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1066899840059/2500000000000000000 : ℝ) ≤ ((245980578239686823/246000000000000000 : ℝ)+2*(3745255429/4920000000000 : ℝ)*(5197/100000 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (245980578239686823/246000000000000000 : ℝ)+2*(3745255429/4920000000000 : ℝ)*(5197/100000 : ℝ)=(250000043020479/250000000000000 : ℝ) by norm_num, show 1+2*(1066899840059/2500000000000000000 : ℝ)=(1250001066899840059/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6693533104159643/10000000000000000000 : ℝ)+(1066899840059/2500000000000000000 : ℝ) ≤ ((245980578239686823/246000000000000000 : ℝ)+(3745255429/4920000000000 : ℝ)*((22909/100000 : ℝ)+(5197/100000 : ℝ)))^(5079/1024 : ℝ) := by
    rw [show (245980578239686823/246000000000000000 : ℝ)+(3745255429/4920000000000 : ℝ)*((22909/100000 : ℝ)+(5197/100000 : ℝ))=(12501687515967/12500000000000 : ℝ) by norm_num, show 1+(6693533104159643/10000000000000000000 : ℝ)+(1066899840059/2500000000000000000 : ℝ)=(10006697800703519879/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6693533104159643/10000000000000000000 : ℝ) ≤ ((245980578239686823/246000000000000000 : ℝ)+2*(3745255429/4920000000000 : ℝ)*(22909/100000 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (245980578239686823/246000000000000000 : ℝ)+2*(3745255429/4920000000000 : ℝ)*(22909/100000 : ℝ)=(250067457618201/250000000000000 : ℝ) by norm_num, show 1+2*(6693533104159643/10000000000000000000 : ℝ)=(5006693533104159643/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (245980578239686823/246000000000000000 : ℝ)*(X 1 0+X 2 0)+(3745255429/4920000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (5197/100000 : ℝ)) (hi := (22909/100000 : ℝ)) (c := (245980578239686823/246000000000000000 : ℝ)) (alpha := (3745255429/4920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (245980578239686823/246000000000000000 : ℝ)*(X 0 1+X 2 1)+(3745255429/4920000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (5197/100000 : ℝ)) (hi := (22909/100000 : ℝ)) (c := (245980578239686823/246000000000000000 : ℝ)) (alpha := (3745255429/4920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (245980578239686823/246000000000000000 : ℝ)*(X 0 2+X 1 2)+(3745255429/4920000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (5197/100000 : ℝ)) (hi := (22909/100000 : ℝ)) (c := (245980578239686823/246000000000000000 : ℝ)) (alpha := (3745255429/4920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1509423953/10000000000 : ℝ)*X 0 0+(5513850487/10000000000 : ℝ)*X 0 1+(5112463801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359455631/10000000000 : ℝ)*X 1 0+(-171912349/1000000000 : ℝ)*X 1 1+(5112463673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1339863763/2500000000 : ℝ)*X 2 0+(5112464197/10000000000 : ℝ)*X 2 1+(-429780893/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4135979037/10000000000 : ℝ)*X 0 0+(903583727/2500000000 : ℝ)*X 0 1+(4706643197/10000000000 : ℝ)*X 0 2+(4135979037/10000000000 : ℝ)*X 1 0+(903583727/2500000000 : ℝ)*X 1 1+(4706643197/10000000000 : ℝ)*X 1 2+(4135979037/10000000000 : ℝ)*X 2 0+(903583727/2500000000 : ℝ)*X 2 1+(4706643197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1509666889/10000000000 : ℝ)*X 0 0+(639672613/1250000000 : ℝ)*X 0 1+(2754424871/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1313035987/2500000000 : ℝ)*X 1 0+(-330684609/2500000000 : ℝ)*X 1 1+(2754425197/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((13130361/25000000 : ℝ)*X 2 0+(43037893/78125000 : ℝ)*X 2 1+(-52909517/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((827328013/2000000000 : ℝ)*X 0 0+(469326087/1000000000 : ℝ)*X 0 1+(906985677/2500000000 : ℝ)*X 0 2+(827328013/2000000000 : ℝ)*X 1 0+(469326087/1000000000 : ℝ)*X 1 1+(906985677/2500000000 : ℝ)*X 1 2+(827328013/2000000000 : ℝ)*X 2 0+(469326087/1000000000 : ℝ)*X 2 1+(906985677/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2292117765087765599903923/256250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1369634039/100000000000000 : ℝ)*(base19) + (1066079129/100000000000000 : ℝ)*(base23) + (228317331/100000000000000 : ℝ)*(upper3) + (737509/4000000000000 : ℝ)*(upper4) + (116494559/100000000000000 : ℝ)*(upper5) + (212930429142701/12500000000000 : ℝ)*(major0) + (212930429142701/12500000000000 : ℝ)*(major1) + (212930429142701/12500000000000 : ℝ)*(major2) + (1245687782207263/50000000000000 : ℝ)*(sp0) + (2491384518217759/100000000000000 : ℝ)*(sp1) + (622846205443167/25000000000000 : ℝ)*(sp2) + (915496335806149/100000000000000 : ℝ)*(sp3) + (1290429659/12500000000000 : ℝ)*(sp4) + (10861159/250000000000 : ℝ)*(sp7) + (228875170067437/25000000000000 : ℝ)*(f.failure) + (1245692943925899/50000000000000 : ℝ)*(f.sum) + (17866230079/24600000000000000000000000 : ℝ)*base65 + (12422671423871077/3075000000000000000000000000000 : ℝ)*base68 + (5991600928946077/3075000000000000000000000000000 : ℝ)*base70 + (4496673218628923/3075000000000000000000000000000 : ℝ)*base71 + (39745585807/12300000000000000000000000 : ℝ)*base74 + (65176161774221077/3075000000000000000000000000000 : ℝ)*base76 + (9498782787896077/3075000000000000000000000000000 : ℝ)*base78 + (5637805527821077/3075000000000000000000000000000 : ℝ)*base80 + (2490580619/24600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (18690121/2500000000000000000000 : ℝ)*base90 + (18690121/2500000000000000000000 : ℝ)*base92 + (18690121/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11084041841950519243498807/1025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (500360319/50000000000000 : ℝ)*(base19) + (52920939/4000000000000 : ℝ)*(base23) + (18443167/100000000000000 : ℝ)*(upper2) + (325982191/100000000000000 : ℝ)*(upper3) + (364090741/100000000000000 : ℝ)*(upper5) + (873292513991191/50000000000000 : ℝ)*(major0) + (873292513991191/50000000000000 : ℝ)*(major1) + (873292513991191/50000000000000 : ℝ)*(major2) + (1463261461/20000000000000 : ℝ)*(sp1) + (212252699/2000000000000 : ℝ)*(sp2) + (319310368100289/12500000000000 : ℝ)*(sp4) + (79827332117949/3125000000000 : ℝ)*(sp5) + (159654438071493/6250000000000 : ℝ)*(sp6) + (4693433753529/500000000000 : ℝ)*(sp7) + (4693433753529/500000000000 : ℝ)*(f.failure) + (319310368100289/12500000000000 : ℝ)*(f.sum) + (406158881203/123000000000000000000000000 : ℝ)*base65 + (24020714527326193/12300000000000000000000000000000 : ℝ)*base67 + (45608274098526193/12300000000000000000000000000000 : ℝ)*base69 + (122991554194026193/12300000000000000000000000000000 : ℝ)*base71 + (88044475607/123000000000000000000000000 : ℝ)*base74 + (31897110436626193/12300000000000000000000000000000 : ℝ)*base75 + (68216145237726193/12300000000000000000000000000000 : ℝ)*base77 + (153229383236873807/12300000000000000000000000000000 : ℝ)*base80 + (317982276139/123000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (223643/50000000000000000000 : ℝ)*base89 + (223643/50000000000000000000 : ℝ)*base91 + (223643/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1683_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (929/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (713/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1683_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1683_s2_0 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-757794021/5000000000 : ℝ)*x 0 + (2744689517/5000000000 : ℝ)*x 1 + (2566423423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (757794021/5000000000 : ℝ)^5087 ≤ (9420254083743/100000000000000 : ℝ)^4063 := by
    have hnat : (757794021 : ℕ)^5087*100000000000000^4063 ≤ 9420254083743^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757794021 5000000000 9420254083743 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744689517/5000000000 : ℝ)^5087 ≤ (2359636607761/5000000000000 : ℝ)^4063 := by
    have hnat : (2744689517 : ℕ)^5087*5000000000000^4063 ≤ 2359636607761^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744689517 5000000000 2359636607761 5000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566423423/5000000000 : ℝ)^5087 ≤ (5423376718127/12500000000000 : ℝ)^4063 := by
    have hnat : (2566423423 : ℕ)^5087*12500000000000^4063 ≤ 5423376718127^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566423423 5000000000 5423376718127 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-757794021/5000000000 : ℝ), (2744689517/5000000000 : ℝ), (2566423423/5000000000 : ℝ)] ![(9420254083743/100000000000000 : ℝ), (2359636607761/5000000000000 : ℝ), (5423376718127/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-757794021/5000000000 : ℝ)|^5087 ≤ (9420254083743/100000000000000 : ℝ)^4063
        have hw : |(-757794021/5000000000 : ℝ)|=(757794021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744689517/5000000000 : ℝ)|^5087 ≤ (2359636607761/5000000000000 : ℝ)^4063
        have hw : |(2744689517/5000000000 : ℝ)|=(2744689517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566423423/5000000000 : ℝ)|^5087 ≤ (5423376718127/12500000000000 : ℝ)^4063
        have hw : |(2566423423/5000000000 : ℝ)|=(2566423423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s2_1 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676461103/5000000000 : ℝ)*x 0 + (-26577489/156250000 : ℝ)*x 1 + (1026569403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676461103/5000000000 : ℝ)^5087 ≤ (9145712796853/20000000000000 : ℝ)^4063 := by
    have hnat : (2676461103 : ℕ)^5087*20000000000000^4063 ≤ 9145712796853^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676461103 5000000000 9145712796853 20000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26577489/156250000 : ℝ)^5087 ≤ (680276279447/6250000000000 : ℝ)^4063 := by
    have hnat : (26577489 : ℕ)^5087*6250000000000^4063 ≤ 680276279447^4063*156250000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26577489 156250000 680276279447 6250000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026569403/2000000000 : ℝ)^5087 ≤ (21693507766787/50000000000000 : ℝ)^4063 := by
    have hnat : (1026569403 : ℕ)^5087*50000000000000^4063 ≤ 21693507766787^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026569403 2000000000 21693507766787 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676461103/5000000000 : ℝ), (-26577489/156250000 : ℝ), (1026569403/2000000000 : ℝ)] ![(9145712796853/20000000000000 : ℝ), (680276279447/6250000000000 : ℝ), (21693507766787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676461103/5000000000 : ℝ)|^5087 ≤ (9145712796853/20000000000000 : ℝ)^4063
        have hw : |(2676461103/5000000000 : ℝ)|=(2676461103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26577489/156250000 : ℝ)|^5087 ≤ (680276279447/6250000000000 : ℝ)^4063
        have hw : |(-26577489/156250000 : ℝ)|=(26577489/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026569403/2000000000 : ℝ)|^5087 ≤ (21693507766787/50000000000000 : ℝ)^4063
        have hw : |(1026569403/2000000000 : ℝ)|=(1026569403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s2_2 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352922583/10000000000 : ℝ)*x 0 + (2566423261/5000000000 : ℝ)*x 1 + (-1700959443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352922583/10000000000 : ℝ)^5087 ≤ (22864284008283/50000000000000 : ℝ)^4063 := by
    have hnat : (5352922583 : ℕ)^5087*50000000000000^4063 ≤ 22864284008283^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352922583 10000000000 22864284008283 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2566423261/5000000000 : ℝ)^5087 ≤ (1355844072377/3125000000000 : ℝ)^4063 := by
    have hnat : (2566423261 : ℕ)^5087*3125000000000^4063 ≤ 1355844072377^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566423261 5000000000 1355844072377 3125000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1700959443/10000000000 : ℝ)^5087 ≤ (2721105412219/25000000000000 : ℝ)^4063 := by
    have hnat : (1700959443 : ℕ)^5087*25000000000000^4063 ≤ 2721105412219^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700959443 10000000000 2721105412219 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352922583/10000000000 : ℝ), (2566423261/5000000000 : ℝ), (-1700959443/10000000000 : ℝ)] ![(22864284008283/50000000000000 : ℝ), (1355844072377/3125000000000 : ℝ), (2721105412219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352922583/10000000000 : ℝ)|^5087 ≤ (22864284008283/50000000000000 : ℝ)^4063
        have hw : |(5352922583/10000000000 : ℝ)|=(5352922583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2566423261/5000000000 : ℝ)|^5087 ≤ (1355844072377/3125000000000 : ℝ)^4063
        have hw : |(2566423261/5000000000 : ℝ)|=(2566423261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1700959443/10000000000 : ℝ)|^5087 ≤ (2721105412219/25000000000000 : ℝ)^4063
        have hw : |(-1700959443/10000000000 : ℝ)|=(1700959443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s2_3 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2070352797/5000000000 : ℝ)*x 0 + (3674918673/10000000000 : ℝ)*x 1 + (185806549/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070352797/5000000000 : ℝ)^5087 ≤ (16578124917237/50000000000000 : ℝ)^4063 := by
    have hnat : (2070352797 : ℕ)^5087*50000000000000^4063 ≤ 16578124917237^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070352797 5000000000 16578124917237 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3674918673/10000000000 : ℝ)^5087 ≤ (7138663344933/25000000000000 : ℝ)^4063 := by
    have hnat : (3674918673 : ℕ)^5087*25000000000000^4063 ≤ 7138663344933^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3674918673 10000000000 7138663344933 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185806549/400000000 : ℝ)^5087 ≤ (19144548382231/50000000000000 : ℝ)^4063 := by
    have hnat : (185806549 : ℕ)^5087*50000000000000^4063 ≤ 19144548382231^4063*400000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185806549 400000000 19144548382231 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2070352797/5000000000 : ℝ), (3674918673/10000000000 : ℝ), (185806549/400000000 : ℝ)] ![(16578124917237/50000000000000 : ℝ), (7138663344933/25000000000000 : ℝ), (19144548382231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2070352797/5000000000 : ℝ)|^5087 ≤ (16578124917237/50000000000000 : ℝ)^4063
        have hw : |(2070352797/5000000000 : ℝ)|=(2070352797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3674918673/10000000000 : ℝ)|^5087 ≤ (7138663344933/25000000000000 : ℝ)^4063
        have hw : |(3674918673/10000000000 : ℝ)|=(3674918673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(185806549/400000000 : ℝ)|^5087 ≤ (19144548382231/50000000000000 : ℝ)^4063
        have hw : |(185806549/400000000 : ℝ)|=(185806549/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s2_4 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-23683721/156250000 : ℝ)*x 0 + (205469219/400000000 : ℝ)*x 1 + (5485436879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23683721/156250000 : ℝ)^5087 ≤ (4710788925941/50000000000000 : ℝ)^4063 := by
    have hnat : (23683721 : ℕ)^5087*50000000000000^4063 ≤ 4710788925941^4063*156250000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23683721 156250000 4710788925941 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205469219/400000000 : ℝ)^5087 ≤ (21714059412737/50000000000000 : ℝ)^4063 := by
    have hnat : (205469219 : ℕ)^5087*50000000000000^4063 ≤ 21714059412737^4063*400000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205469219 400000000 21714059412737 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485436879/10000000000 : ℝ)^5087 ≤ (47150303310957/100000000000000 : ℝ)^4063 := by
    have hnat : (5485436879 : ℕ)^5087*100000000000000^4063 ≤ 47150303310957^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485436879 10000000000 47150303310957 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23683721/156250000 : ℝ), (205469219/400000000 : ℝ), (5485436879/10000000000 : ℝ)] ![(4710788925941/50000000000000 : ℝ), (21714059412737/50000000000000 : ℝ), (47150303310957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23683721/156250000 : ℝ)|^5087 ≤ (4710788925941/50000000000000 : ℝ)^4063
        have hw : |(-23683721/156250000 : ℝ)|=(23683721/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205469219/400000000 : ℝ)|^5087 ≤ (21714059412737/50000000000000 : ℝ)^4063
        have hw : |(205469219/400000000 : ℝ)|=(205469219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485436879/10000000000 : ℝ)|^5087 ≤ (47150303310957/100000000000000 : ℝ)^4063
        have hw : |(5485436879/10000000000 : ℝ)|=(5485436879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s2_5 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257677067/10000000000 : ℝ)*x 0 + (-5393477/40000000 : ℝ)*x 1 + (5485436783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257677067/10000000000 : ℝ)^5087 ≤ (44712139464389/100000000000000 : ℝ)^4063 := by
    have hnat : (5257677067 : ℕ)^5087*100000000000000^4063 ≤ 44712139464389^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257677067 10000000000 44712139464389 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393477/40000000 : ℝ)^5087 ≤ (8137558238103/100000000000000 : ℝ)^4063 := by
    have hnat : (5393477 : ℕ)^5087*100000000000000^4063 ≤ 8137558238103^4063*40000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393477 40000000 8137558238103 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485436783/10000000000 : ℝ)^5087 ≤ (47150302277817/100000000000000 : ℝ)^4063 := by
    have hnat : (5485436783 : ℕ)^5087*100000000000000^4063 ≤ 47150302277817^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485436783 10000000000 47150302277817 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257677067/10000000000 : ℝ), (-5393477/40000000 : ℝ), (5485436783/10000000000 : ℝ)] ![(44712139464389/100000000000000 : ℝ), (8137558238103/100000000000000 : ℝ), (47150302277817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257677067/10000000000 : ℝ)|^5087 ≤ (44712139464389/100000000000000 : ℝ)^4063
        have hw : |(5257677067/10000000000 : ℝ)|=(5257677067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5393477/40000000 : ℝ)|^5087 ≤ (8137558238103/100000000000000 : ℝ)^4063
        have hw : |(-5393477/40000000 : ℝ)|=(5393477/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485436783/10000000000 : ℝ)|^5087 ≤ (47150302277817/100000000000000 : ℝ)^4063
        have hw : |(5485436783/10000000000 : ℝ)|=(5485436783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s2_6 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257677031/10000000000 : ℝ)*x 0 + (2742718397/5000000000 : ℝ)*x 1 + (-269673857/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257677031/10000000000 : ℝ)^5087 ≤ (1117803477027/2500000000000 : ℝ)^4063 := by
    have hnat : (5257677031 : ℕ)^5087*2500000000000^4063 ≤ 1117803477027^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257677031 10000000000 1117803477027 2500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742718397/5000000000 : ℝ)^5087 ≤ (47150302396197/100000000000000 : ℝ)^4063 := by
    have hnat : (2742718397 : ℕ)^5087*100000000000000^4063 ≤ 47150302396197^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742718397 5000000000 47150302396197 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269673857/2000000000 : ℝ)^5087 ≤ (1017194812821/12500000000000 : ℝ)^4063 := by
    have hnat : (269673857 : ℕ)^5087*12500000000000^4063 ≤ 1017194812821^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269673857 2000000000 1017194812821 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257677031/10000000000 : ℝ), (2742718397/5000000000 : ℝ), (-269673857/2000000000 : ℝ)] ![(1117803477027/2500000000000 : ℝ), (47150302396197/100000000000000 : ℝ), (1017194812821/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257677031/10000000000 : ℝ)|^5087 ≤ (1117803477027/2500000000000 : ℝ)^4063
        have hw : |(5257677031/10000000000 : ℝ)|=(5257677031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742718397/5000000000 : ℝ)|^5087 ≤ (47150302396197/100000000000000 : ℝ)^4063
        have hw : |(2742718397/5000000000 : ℝ)|=(2742718397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269673857/2000000000 : ℝ)|^5087 ≤ (1017194812821/12500000000000 : ℝ)^4063
        have hw : |(-269673857/2000000000 : ℝ)|=(269673857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s2_7 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (828233663/2000000000 : ℝ)*x 0 + (579324299/1250000000 : ℝ)*x 1 + (3685646901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828233663/2000000000 : ℝ)^5087 ≤ (4145111113547/12500000000000 : ℝ)^4063 := by
    have hnat : (828233663 : ℕ)^5087*12500000000000^4063 ≤ 4145111113547^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828233663 2000000000 4145111113547 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579324299/1250000000 : ℝ)^5087 ≤ (38180050202111/100000000000000 : ℝ)^4063 := by
    have hnat : (579324299 : ℕ)^5087*100000000000000^4063 ≤ 38180050202111^4063*1250000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579324299 1250000000 38180050202111 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3685646901/10000000000 : ℝ)^5087 ≤ (28659060878567/100000000000000 : ℝ)^4063 := by
    have hnat : (3685646901 : ℕ)^5087*100000000000000^4063 ≤ 28659060878567^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685646901 10000000000 28659060878567 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(828233663/2000000000 : ℝ), (579324299/1250000000 : ℝ), (3685646901/10000000000 : ℝ)] ![(4145111113547/12500000000000 : ℝ), (38180050202111/100000000000000 : ℝ), (28659060878567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(828233663/2000000000 : ℝ)|^5087 ≤ (4145111113547/12500000000000 : ℝ)^4063
        have hw : |(828233663/2000000000 : ℝ)|=(828233663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(579324299/1250000000 : ℝ)|^5087 ≤ (38180050202111/100000000000000 : ℝ)^4063
        have hw : |(579324299/1250000000 : ℝ)|=(579324299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3685646901/10000000000 : ℝ)|^5087 ≤ (28659060878567/100000000000000 : ℝ)^4063
        have hw : |(3685646901/10000000000 : ℝ)|=(3685646901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1683_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (713/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (929/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (9733/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8657/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (713/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (929/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (713/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (929/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (713/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (929/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (713/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (929/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (713/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (929/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (713/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (929/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (929/10000 : ℝ) ^ (5079/1024 : ℝ) ≤ (380511912558427/50000000000000000000 : ℝ) := by
    have hpowers : (929/10000 : ℝ)^5079 ≤ (380511912558427/50000000000000000000 : ℝ)^1024 := by
      have hnat : (929 : ℕ)^5079*50000000000000000000^1024 ≤ 380511912558427^1024*10000^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        929 10000 380511912558427 50000000000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (929/10000 : ℝ)) (X := (380511912558427/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (713/4000 : ℝ) ^ (5079/1024 : ℝ) ≤ (19281275839967661/100000000000000000000 : ℝ) := by
    have hpowers : (713/4000 : ℝ)^5079 ≤ (19281275839967661/100000000000000000000 : ℝ)^1024 := by
      have hnat : (713 : ℕ)^5079*100000000000000000000^1024 ≤ 19281275839967661^1024*4000^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        713 4000 19281275839967661 100000000000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (713/4000 : ℝ)) (X := (19281275839967661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000380511912558427/25000000000000000000 : ℝ) ≤ (10000030686499787/10000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (25000380511912558427/25000000000000000000 : ℝ)^1024 ≤ (10000030686499787/10000000000000000 : ℝ)^5079 := by
      have hnat : (25000380511912558427 : ℕ)^1024*10000000000000000^5079 ≤ 10000030686499787^5079*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000380511912558427 25000000000000000000 10000030686499787 10000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000030686499787/10000000000000000 : ℝ)) (X := (25000380511912558427/25000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004008459933016903/20000000000000000000 : ℝ) ≤ (5000202024739487/5000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (20004008459933016903/20000000000000000000 : ℝ)^1024 ≤ (5000202024739487/5000000000000000 : ℝ)^5079 := by
      have hnat : (20004008459933016903 : ℕ)^1024*5000000000000000^5079 ≤ 5000202024739487^5079*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004008459933016903 20000000000000000000 5000202024739487 5000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000202024739487/5000000000000000 : ℝ)) (X := (20004008459933016903/20000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019281275839967661/50000000000000000000 : ℝ) ≤ (10000777412458161/10000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (50019281275839967661/50000000000000000000 : ℝ)^1024 ≤ (10000777412458161/10000000000000000 : ℝ)^5079 := by
      have hnat : (50019281275839967661 : ℕ)^1024*10000000000000000^5079 ≤ 10000777412458161^5079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019281275839967661 50000000000000000000 10000777412458161 10000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000777412458161/10000000000000000 : ℝ)) (X := (50019281275839967661/50000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(380511912558427/50000000000000000000 : ℝ) ≤ ((17068664965024477517/17070000000000000000 : ℝ)+2*(373362979187/853500000000000 : ℝ)*(929/10000 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (17068664965024477517/17070000000000000000 : ℝ)+2*(373362979187/853500000000000 : ℝ)*(929/10000 : ℝ)=(10000030686499787/10000000000000000 : ℝ) by norm_num, show 1+2*(380511912558427/50000000000000000000 : ℝ)=(25000380511912558427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19281275839967661/100000000000000000000 : ℝ)+(380511912558427/50000000000000000000 : ℝ) ≤ ((17068664965024477517/17070000000000000000 : ℝ)+(373362979187/853500000000000 : ℝ)*((713/4000 : ℝ)+(929/10000 : ℝ)))^(5079/1024 : ℝ) := by
    rw [show (17068664965024477517/17070000000000000000 : ℝ)+(373362979187/853500000000000 : ℝ)*((713/4000 : ℝ)+(929/10000 : ℝ))=(5000202024739487/5000000000000000 : ℝ) by norm_num, show 1+(19281275839967661/100000000000000000000 : ℝ)+(380511912558427/50000000000000000000 : ℝ)=(20004008459933016903/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19281275839967661/100000000000000000000 : ℝ) ≤ ((17068664965024477517/17070000000000000000 : ℝ)+2*(373362979187/853500000000000 : ℝ)*(713/4000 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (17068664965024477517/17070000000000000000 : ℝ)+2*(373362979187/853500000000000 : ℝ)*(713/4000 : ℝ)=(10000777412458161/10000000000000000 : ℝ) by norm_num, show 1+2*(19281275839967661/100000000000000000000 : ℝ)=(50019281275839967661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17068664965024477517/17070000000000000000 : ℝ)*(X 1 0+X 2 0)+(373362979187/853500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (929/10000 : ℝ)) (hi := (713/4000 : ℝ)) (c := (17068664965024477517/17070000000000000000 : ℝ)) (alpha := (373362979187/853500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17068664965024477517/17070000000000000000 : ℝ)*(X 0 1+X 2 1)+(373362979187/853500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (929/10000 : ℝ)) (hi := (713/4000 : ℝ)) (c := (17068664965024477517/17070000000000000000 : ℝ)) (alpha := (373362979187/853500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17068664965024477517/17070000000000000000 : ℝ)*(X 0 2+X 1 2)+(373362979187/853500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (929/10000 : ℝ)) (hi := (713/4000 : ℝ)) (c := (17068664965024477517/17070000000000000000 : ℝ)) (alpha := (373362979187/853500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-757794021/5000000000 : ℝ)*X 0 0+(2744689517/5000000000 : ℝ)*X 0 1+(2566423423/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676461103/5000000000 : ℝ)*X 1 0+(-26577489/156250000 : ℝ)*X 1 1+(1026569403/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352922583/10000000000 : ℝ)*X 2 0+(2566423261/5000000000 : ℝ)*X 2 1+(-1700959443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2070352797/5000000000 : ℝ)*X 0 0+(3674918673/10000000000 : ℝ)*X 0 1+(185806549/400000000 : ℝ)*X 0 2+(2070352797/5000000000 : ℝ)*X 1 0+(3674918673/10000000000 : ℝ)*X 1 1+(185806549/400000000 : ℝ)*X 1 2+(2070352797/5000000000 : ℝ)*X 2 0+(3674918673/10000000000 : ℝ)*X 2 1+(185806549/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-23683721/156250000 : ℝ)*X 0 0+(205469219/400000000 : ℝ)*X 0 1+(5485436879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257677067/10000000000 : ℝ)*X 1 0+(-5393477/40000000 : ℝ)*X 1 1+(5485436783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257677031/10000000000 : ℝ)*X 2 0+(2742718397/5000000000 : ℝ)*X 2 1+(-269673857/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((828233663/2000000000 : ℝ)*X 0 0+(579324299/1250000000 : ℝ)*X 0 1+(3685646901/10000000000 : ℝ)*X 0 2+(828233663/2000000000 : ℝ)*X 1 0+(579324299/1250000000 : ℝ)*X 1 1+(3685646901/10000000000 : ℝ)*X 1 2+(828233663/2000000000 : ℝ)*X 2 0+(579324299/1250000000 : ℝ)*X 2 1+(3685646901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108525340289628698550891461/11380000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1365266127/100000000000000 : ℝ)*(base19) + (353775523/25000000000000 : ℝ)*(base23) + (79064957/100000000000000 : ℝ)*(lower2) + (65311283/25000000000000 : ℝ)*(upper3) + (91569921/100000000000000 : ℝ)*(upper5) + (76710023670233/4000000000000 : ℝ)*(major0) + (76710023670233/4000000000000 : ℝ)*(major1) + (76710023670233/4000000000000 : ℝ)*(major2) + (350601238498793/12500000000000 : ℝ)*(sp0) + (87650666372551/3125000000000 : ℝ)*(sp1) + (2804821274085667/100000000000000 : ℝ)*(sp2) + (1030672043596759/100000000000000 : ℝ)*(sp3) + (1597649677/12500000000000 : ℝ)*(sp4) + (3066421939/50000000000000 : ℝ)*(sp7) + (1030678176440637/100000000000000 : ℝ)*(f.failure) + (35060283614847/1250000000000 : ℝ)*(f.sum) + (6040100679677/1707000000000000000000000000 : ℝ)*base66 + (2438843449349513/22760000000000000000000000000000 : ℝ)*base68 + (349595661392469513/22760000000000000000000000000000 : ℝ)*base70 + (110172121142610487/22760000000000000000000000000000 : ℝ)*base71 + (990931219247/853500000000000000000000000 : ℝ)*base73 + (258564055098389513/22760000000000000000000000000000 : ℝ)*base76 + (40598259403829513/22760000000000000000000000000000 : ℝ)*base78 + (56634739327370487/22760000000000000000000000000000 : ℝ)*base79 + (4217046542933/1707000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (38074279/10000000000000000000000 : ℝ)*base89 + (38074279/10000000000000000000000 : ℝ)*base91 + (38074279/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3612385957059974670818015247/284500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (245655477/12500000000000 : ℝ)*(base19) + (2104405419/100000000000000 : ℝ)*(base23) + (259422391/100000000000000 : ℝ)*(upper3) + (38141789/50000000000000 : ℝ)*(lower4) + (138391057/50000000000000 : ℝ)*(upper5) + (1960770254043691/100000000000000 : ℝ)*(major0) + (1960770254043691/100000000000000 : ℝ)*(major1) + (1960770254043691/100000000000000 : ℝ)*(major2) + (3404914667/20000000000000 : ℝ)*(sp1) + (8890585511/50000000000000 : ℝ)*(sp2) + (573548273908849/20000000000000 : ℝ)*(sp4) + (1433861189863547/50000000000000 : ℝ)*(sp5) + (716930370991951/25000000000000 : ℝ)*(sp6) + (526899357649659/50000000000000 : ℝ)*(sp7) + (526899357649659/50000000000000 : ℝ)*(f.failure) + (573548273908849/20000000000000 : ℝ)*(f.sum) + (31151001453467/42675000000000000000000000000 : ℝ)*base65 + (1073957435677511749/569000000000000000000000000000000 : ℝ)*base67 + (1985688620420488251/569000000000000000000000000000000 : ℝ)*base70 + (4549440230665488251/569000000000000000000000000000000 : ℝ)*base72 + (298076080554917/42675000000000000000000000000 : ℝ)*base73 + (2092337583188488251/569000000000000000000000000000000 : ℝ)*base76 + (705258843163488251/569000000000000000000000000000000 : ℝ)*base78 + (857453228712511749/569000000000000000000000000000000 : ℝ)*base79 + (37674953088617/42675000000000000000000000000 : ℝ)*base81 + (16251647/5000000000000000000000 : ℝ)*base90 + (16251647/5000000000000000000000 : ℝ)*base92 + (16251647/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1683_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (713/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (929/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9733/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8657/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1683_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1683_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9733/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8657/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1683_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1683_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1683_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9733/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8657/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1683_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
