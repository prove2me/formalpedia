-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1254_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:24:46.07612+00:00
-- url     : https://prove2.me/submissions/258e8e12-6f98-41cb-aafa-31f4019bdcd5

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
theorem support_rectangle_w1254_s6_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114435749/10000000000 : ℝ)*x 0 + (1078230567/2000000000 : ℝ)*x 1 + (1053440547/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114435749/10000000000 : ℝ)^8447 ≤ (12859467495043/100000000000000 : ℝ)^6399 := by
    have hnat : (2114435749 : ℕ)^8447*100000000000000^6399 ≤ 12859467495043^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114435749 10000000000 12859467495043 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078230567/2000000000 : ℝ)^8447 ≤ (11059776753367/25000000000000 : ℝ)^6399 := by
    have hnat : (1078230567 : ℕ)^8447*25000000000000^6399 ≤ 11059776753367^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078230567 2000000000 11059776753367 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053440547/2000000000 : ℝ)^8447 ≤ (42901425476611/100000000000000 : ℝ)^6399 := by
    have hnat : (1053440547 : ℕ)^8447*100000000000000^6399 ≤ 42901425476611^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053440547 2000000000 42901425476611 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114435749/10000000000 : ℝ), (1078230567/2000000000 : ℝ), (1053440547/2000000000 : ℝ)] ![(12859467495043/100000000000000 : ℝ), (11059776753367/25000000000000 : ℝ), (42901425476611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114435749/10000000000 : ℝ)|^8447 ≤ (12859467495043/100000000000000 : ℝ)^6399
        have hw : |(-2114435749/10000000000 : ℝ)|=(2114435749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078230567/2000000000 : ℝ)|^8447 ≤ (11059776753367/25000000000000 : ℝ)^6399
        have hw : |(1078230567/2000000000 : ℝ)|=(1078230567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053440547/2000000000 : ℝ)|^8447 ≤ (42901425476611/100000000000000 : ℝ)^6399
        have hw : |(1053440547/2000000000 : ℝ)|=(1053440547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s6_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344289707/10000000000 : ℝ)*x 0 + (-544320333/2500000000 : ℝ)*x 1 + (5267202729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344289707/10000000000 : ℝ)^8447 ≤ (1366630800241/3125000000000 : ℝ)^6399 := by
    have hnat : (5344289707 : ℕ)^8447*3125000000000^6399 ≤ 1366630800241^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344289707 10000000000 1366630800241 3125000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544320333/2500000000 : ℝ)^8447 ≤ (133663889689/1000000000000 : ℝ)^6399 := by
    have hnat : (544320333 : ℕ)^8447*1000000000000^6399 ≤ 133663889689^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544320333 2500000000 133663889689 1000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267202729/10000000000 : ℝ)^8447 ≤ (42901425412101/100000000000000 : ℝ)^6399 := by
    have hnat : (5267202729 : ℕ)^8447*100000000000000^6399 ≤ 42901425412101^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267202729 10000000000 42901425412101 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344289707/10000000000 : ℝ), (-544320333/2500000000 : ℝ), (5267202729/10000000000 : ℝ)] ![(1366630800241/3125000000000 : ℝ), (133663889689/1000000000000 : ℝ), (42901425412101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344289707/10000000000 : ℝ)|^8447 ≤ (1366630800241/3125000000000 : ℝ)^6399
        have hw : |(5344289707/10000000000 : ℝ)|=(5344289707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544320333/2500000000 : ℝ)|^8447 ≤ (133663889689/1000000000000 : ℝ)^6399
        have hw : |(-544320333/2500000000 : ℝ)|=(544320333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267202729/10000000000 : ℝ)|^8447 ≤ (42901425412101/100000000000000 : ℝ)^6399
        have hw : |(5267202729/10000000000 : ℝ)|=(5267202729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s6_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068857943/2000000000 : ℝ)*x 0 + (658400341/1250000000 : ℝ)*x 1 + (-2177281321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068857943/2000000000 : ℝ)^8447 ≤ (43732185694127/100000000000000 : ℝ)^6399 := by
    have hnat : (1068857943 : ℕ)^8447*100000000000000^6399 ≤ 43732185694127^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068857943 2000000000 43732185694127 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658400341/1250000000 : ℝ)^8447 ≤ (42901425401349/100000000000000 : ℝ)^6399 := by
    have hnat : (658400341 : ℕ)^8447*100000000000000^6399 ≤ 42901425401349^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658400341 1250000000 42901425401349 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2177281321/10000000000 : ℝ)^8447 ≤ (6683194439879/50000000000000 : ℝ)^6399 := by
    have hnat : (2177281321 : ℕ)^8447*50000000000000^6399 ≤ 6683194439879^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177281321 10000000000 6683194439879 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068857943/2000000000 : ℝ), (658400341/1250000000 : ℝ), (-2177281321/10000000000 : ℝ)] ![(43732185694127/100000000000000 : ℝ), (42901425401349/100000000000000 : ℝ), (6683194439879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068857943/2000000000 : ℝ)|^8447 ≤ (43732185694127/100000000000000 : ℝ)^6399
        have hw : |(1068857943/2000000000 : ℝ)|=(1068857943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658400341/1250000000 : ℝ)|^8447 ≤ (42901425401349/100000000000000 : ℝ)^6399
        have hw : |(658400341/1250000000 : ℝ)|=(658400341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2177281321/10000000000 : ℝ)|^8447 ≤ (6683194439879/50000000000000 : ℝ)^6399
        have hw : |(-2177281321/10000000000 : ℝ)|=(2177281321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s6_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174560581/5000000000 : ℝ)*x 0 + (4224879017/10000000000 : ℝ)*x 1 + (4476903287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174560581/5000000000 : ℝ)^8447 ≤ (33317461631843/100000000000000 : ℝ)^6399 := by
    have hnat : (2174560581 : ℕ)^8447*100000000000000^6399 ≤ 33317461631843^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174560581 5000000000 33317461631843 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224879017/10000000000 : ℝ)^8447 ≤ (32066837687141/100000000000000 : ℝ)^6399 := by
    have hnat : (4224879017 : ℕ)^8447*100000000000000^6399 ≤ 32066837687141^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224879017 10000000000 32066837687141 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476903287/10000000000 : ℝ)^8447 ≤ (6923140133841/20000000000000 : ℝ)^6399 := by
    have hnat : (4476903287 : ℕ)^8447*20000000000000^6399 ≤ 6923140133841^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476903287 10000000000 6923140133841 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174560581/5000000000 : ℝ), (4224879017/10000000000 : ℝ), (4476903287/10000000000 : ℝ)] ![(33317461631843/100000000000000 : ℝ), (32066837687141/100000000000000 : ℝ), (6923140133841/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174560581/5000000000 : ℝ)|^8447 ≤ (33317461631843/100000000000000 : ℝ)^6399
        have hw : |(2174560581/5000000000 : ℝ)|=(2174560581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224879017/10000000000 : ℝ)|^8447 ≤ (32066837687141/100000000000000 : ℝ)^6399
        have hw : |(4224879017/10000000000 : ℝ)|=(4224879017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476903287/10000000000 : ℝ)|^8447 ≤ (6923140133841/20000000000000 : ℝ)^6399
        have hw : |(4476903287/10000000000 : ℝ)|=(4476903287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s6_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-66076271/312500000 : ℝ)*x 0 + (5267515879/10000000000 : ℝ)*x 1 + (5390838359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66076271/312500000 : ℝ)^8447 ≤ (257190140359/2000000000000 : ℝ)^6399 := by
    have hnat : (66076271 : ℕ)^8447*2000000000000^6399 ≤ 257190140359^6399*312500000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66076271 312500000 257190140359 2000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267515879/10000000000 : ℝ)^8447 ≤ (21452396188619/50000000000000 : ℝ)^6399 := by
    have hnat : (5267515879 : ℕ)^8447*50000000000000^6399 ≤ 21452396188619^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267515879 10000000000 21452396188619 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390838359/10000000000 : ℝ)^8447 ≤ (11058925147679/25000000000000 : ℝ)^6399 := by
    have hnat : (5390838359 : ℕ)^8447*25000000000000^6399 ≤ 11058925147679^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390838359 10000000000 11058925147679 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66076271/312500000 : ℝ), (5267515879/10000000000 : ℝ), (5390838359/10000000000 : ℝ)] ![(257190140359/2000000000000 : ℝ), (21452396188619/50000000000000 : ℝ), (11058925147679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66076271/312500000 : ℝ)|^8447 ≤ (257190140359/2000000000000 : ℝ)^6399
        have hw : |(-66076271/312500000 : ℝ)|=(66076271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267515879/10000000000 : ℝ)|^8447 ≤ (21452396188619/50000000000000 : ℝ)^6399
        have hw : |(5267515879/10000000000 : ℝ)|=(5267515879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390838359/10000000000 : ℝ)|^8447 ≤ (11058925147679/25000000000000 : ℝ)^6399
        have hw : |(5390838359/10000000000 : ℝ)|=(5390838359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s6_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212505531/400000000 : ℝ)*x 0 + (-256705723/1250000000 : ℝ)*x 1 + (1347709433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212505531/400000000 : ℝ)^8447 ≤ (1735624534079/4000000000000 : ℝ)^6399 := by
    have hnat : (212505531 : ℕ)^8447*4000000000000^6399 ≤ 1735624534079^6399*400000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212505531 400000000 1735624534079 4000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256705723/1250000000 : ℝ)^8447 ≤ (12373692838023/100000000000000 : ℝ)^6399 := by
    have hnat : (256705723 : ℕ)^8447*100000000000000^6399 ≤ 12373692838023^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256705723 1250000000 12373692838023 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347709433/2500000000 : ℝ)^8447 ≤ (22117846899539/50000000000000 : ℝ)^6399 := by
    have hnat : (1347709433 : ℕ)^8447*50000000000000^6399 ≤ 22117846899539^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347709433 2500000000 22117846899539 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212505531/400000000 : ℝ), (-256705723/1250000000 : ℝ), (1347709433/2500000000 : ℝ)] ![(1735624534079/4000000000000 : ℝ), (12373692838023/100000000000000 : ℝ), (22117846899539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212505531/400000000 : ℝ)|^8447 ≤ (1735624534079/4000000000000 : ℝ)^6399
        have hw : |(212505531/400000000 : ℝ)|=(212505531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256705723/1250000000 : ℝ)|^8447 ≤ (12373692838023/100000000000000 : ℝ)^6399
        have hw : |(-256705723/1250000000 : ℝ)|=(256705723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347709433/2500000000 : ℝ)|^8447 ≤ (22117846899539/50000000000000 : ℝ)^6399
        have hw : |(1347709433/2500000000 : ℝ)|=(1347709433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s6_6 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656319281/5000000000 : ℝ)*x 0 + (1347709333/2500000000 : ℝ)*x 1 + (-2053645939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656319281/5000000000 : ℝ)^8447 ≤ (43390616446243/100000000000000 : ℝ)^6399 := by
    have hnat : (2656319281 : ℕ)^8447*100000000000000^6399 ≤ 43390616446243^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656319281 5000000000 43390616446243 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347709333/2500000000 : ℝ)^8447 ≤ (8847137893259/20000000000000 : ℝ)^6399 := by
    have hnat : (1347709333 : ℕ)^8447*20000000000000^6399 ≤ 8847137893259^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347709333 2500000000 8847137893259 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2053645939/10000000000 : ℝ)^8447 ≤ (773355879427/6250000000000 : ℝ)^6399 := by
    have hnat : (2053645939 : ℕ)^8447*6250000000000^6399 ≤ 773355879427^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053645939 10000000000 773355879427 6250000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656319281/5000000000 : ℝ), (1347709333/2500000000 : ℝ), (-2053645939/10000000000 : ℝ)] ![(43390616446243/100000000000000 : ℝ), (8847137893259/20000000000000 : ℝ), (773355879427/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656319281/5000000000 : ℝ)|^8447 ≤ (43390616446243/100000000000000 : ℝ)^6399
        have hw : |(2656319281/5000000000 : ℝ)|=(2656319281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347709333/2500000000 : ℝ)|^8447 ≤ (8847137893259/20000000000000 : ℝ)^6399
        have hw : |(1347709333/2500000000 : ℝ)|=(1347709333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2053645939/10000000000 : ℝ)|^8447 ≤ (773355879427/6250000000000 : ℝ)^6399
        have hw : |(-2053645939/10000000000 : ℝ)|=(2053645939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s6_7 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349130453/10000000000 : ℝ)*x 0 + (4476265897/10000000000 : ℝ)*x 1 + (4225518929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349130453/10000000000 : ℝ)^8447 ≤ (33317555587599/100000000000000 : ℝ)^6399 := by
    have hnat : (4349130453 : ℕ)^8447*100000000000000^6399 ≤ 33317555587599^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349130453 10000000000 33317555587599 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476265897/10000000000 : ℝ)^8447 ≤ (34609195162203/100000000000000 : ℝ)^6399 := by
    have hnat : (4476265897 : ℕ)^8447*100000000000000^6399 ≤ 34609195162203^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476265897 10000000000 34609195162203 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225518929/10000000000 : ℝ)^8447 ≤ (32073249236953/100000000000000 : ℝ)^6399 := by
    have hnat : (4225518929 : ℕ)^8447*100000000000000^6399 ≤ 32073249236953^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225518929 10000000000 32073249236953 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349130453/10000000000 : ℝ), (4476265897/10000000000 : ℝ), (4225518929/10000000000 : ℝ)] ![(33317555587599/100000000000000 : ℝ), (34609195162203/100000000000000 : ℝ), (32073249236953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349130453/10000000000 : ℝ)|^8447 ≤ (33317555587599/100000000000000 : ℝ)^6399
        have hw : |(4349130453/10000000000 : ℝ)|=(4349130453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476265897/10000000000 : ℝ)|^8447 ≤ (34609195162203/100000000000000 : ℝ)^6399
        have hw : |(4476265897/10000000000 : ℝ)|=(4476265897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225518929/10000000000 : ℝ)|^8447 ≤ (32073249236953/100000000000000 : ℝ)^6399
        have hw : |(4225518929/10000000000 : ℝ)|=(4225518929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11489/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2823/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2827/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11469/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2827/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11469/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2827/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11469/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2827/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11469/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2827/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11469/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2827/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11469/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11469/100000 : ℝ) ^ (4223/1024 : ℝ) ≤ (2645399899972503/20000000000000000000 : ℝ) := by
    have hpowers : (11469/100000 : ℝ)^4223 ≤ (2645399899972503/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11469 : ℕ)^4223*20000000000000000000^1024 ≤ 2645399899972503^1024*100000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11469 100000 2645399899972503 20000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11469/100000 : ℝ)) (X := (2645399899972503/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2827/20000 : ℝ) ^ (4223/1024 : ℝ) ≤ (7829608121976533/25000000000000000000 : ℝ) := by
    have hpowers : (2827/20000 : ℝ)^4223 ≤ (7829608121976533/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2827 : ℕ)^4223*25000000000000000000^1024 ≤ 7829608121976533^1024*20000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2827 20000 7829608121976533 25000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2827/20000 : ℝ)) (X := (7829608121976533/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002645399899972503/10000000000000000000 : ℝ) ≤ (10000641396665207/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (10002645399899972503/10000000000000000000 : ℝ)^1024 ≤ (10000641396665207/10000000000000000 : ℝ)^4223 := by
      have hnat : (10002645399899972503 : ℕ)^1024*10000000000000000^4223 ≤ 10000641396665207^4223*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002645399899972503 10000000000000000000 10000641396665207 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000641396665207/10000000000000000 : ℝ)) (X := (10002645399899972503/10000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044545431987768647/100000000000000000000 : ℝ) ≤ (1000107996278203/1000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (100044545431987768647/100000000000000000000 : ℝ)^1024 ≤ (1000107996278203/1000000000000000 : ℝ)^4223 := by
      have hnat : (100044545431987768647 : ℕ)^1024*1000000000000000^4223 ≤ 1000107996278203^4223*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044545431987768647 100000000000000000000 1000107996278203 1000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000107996278203/1000000000000000 : ℝ)) (X := (100044545431987768647/100000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507829608121976533/12500000000000000000 : ℝ) ≤ (10001518528898853/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (12507829608121976533/12500000000000000000 : ℝ)^1024 ≤ (10001518528898853/10000000000000000 : ℝ)^4223 := by
      have hnat : (12507829608121976533 : ℕ)^1024*10000000000000000^4223 ≤ 10001518528898853^4223*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507829608121976533 12500000000000000000 10001518528898853 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001518528898853/10000000000000000 : ℝ)) (X := (12507829608121976533/12500000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2645399899972503/20000000000000000000 : ℝ) ≤ ((1665728133370109743/1666250000000000000 : ℝ)+2*(438566116823/266600000000000 : ℝ)*(11469/100000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (1665728133370109743/1666250000000000000 : ℝ)+2*(438566116823/266600000000000 : ℝ)*(11469/100000 : ℝ)=(10000641396665207/10000000000000000 : ℝ) by norm_num, show 1+2*(2645399899972503/20000000000000000000 : ℝ)=(10002645399899972503/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7829608121976533/25000000000000000000 : ℝ)+(2645399899972503/20000000000000000000 : ℝ) ≤ ((1665728133370109743/1666250000000000000 : ℝ)+(438566116823/266600000000000 : ℝ)*((2827/20000 : ℝ)+(11469/100000 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (1665728133370109743/1666250000000000000 : ℝ)+(438566116823/266600000000000 : ℝ)*((2827/20000 : ℝ)+(11469/100000 : ℝ))=(1000107996278203/1000000000000000 : ℝ) by norm_num, show 1+(7829608121976533/25000000000000000000 : ℝ)+(2645399899972503/20000000000000000000 : ℝ)=(100044545431987768647/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7829608121976533/25000000000000000000 : ℝ) ≤ ((1665728133370109743/1666250000000000000 : ℝ)+2*(438566116823/266600000000000 : ℝ)*(2827/20000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (1665728133370109743/1666250000000000000 : ℝ)+2*(438566116823/266600000000000 : ℝ)*(2827/20000 : ℝ)=(10001518528898853/10000000000000000 : ℝ) by norm_num, show 1+2*(7829608121976533/25000000000000000000 : ℝ)=(12507829608121976533/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1665728133370109743/1666250000000000000 : ℝ)*(X 1 0+X 2 0)+(438566116823/266600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11469/100000 : ℝ)) (hi := (2827/20000 : ℝ)) (c := (1665728133370109743/1666250000000000000 : ℝ)) (alpha := (438566116823/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1665728133370109743/1666250000000000000 : ℝ)*(X 0 1+X 2 1)+(438566116823/266600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11469/100000 : ℝ)) (hi := (2827/20000 : ℝ)) (c := (1665728133370109743/1666250000000000000 : ℝ)) (alpha := (438566116823/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1665728133370109743/1666250000000000000 : ℝ)*(X 0 2+X 1 2)+(438566116823/266600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11469/100000 : ℝ)) (hi := (2827/20000 : ℝ)) (c := (1665728133370109743/1666250000000000000 : ℝ)) (alpha := (438566116823/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2114435749/10000000000 : ℝ)*X 0 0+(1078230567/2000000000 : ℝ)*X 0 1+(1053440547/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344289707/10000000000 : ℝ)*X 1 0+(-544320333/2500000000 : ℝ)*X 1 1+(5267202729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068857943/2000000000 : ℝ)*X 2 0+(658400341/1250000000 : ℝ)*X 2 1+(-2177281321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174560581/5000000000 : ℝ)*X 0 0+(4224879017/10000000000 : ℝ)*X 0 1+(4476903287/10000000000 : ℝ)*X 0 2+(2174560581/5000000000 : ℝ)*X 1 0+(4224879017/10000000000 : ℝ)*X 1 1+(4476903287/10000000000 : ℝ)*X 1 2+(2174560581/5000000000 : ℝ)*X 2 0+(4224879017/10000000000 : ℝ)*X 2 1+(4476903287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-66076271/312500000 : ℝ)*X 0 0+(5267515879/10000000000 : ℝ)*X 0 1+(5390838359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212505531/400000000 : ℝ)*X 1 0+(-256705723/1250000000 : ℝ)*X 1 1+(1347709433/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656319281/5000000000 : ℝ)*X 2 0+(1347709333/2500000000 : ℝ)*X 2 1+(-2053645939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349130453/10000000000 : ℝ)*X 0 0+(4476265897/10000000000 : ℝ)*X 0 1+(4225518929/10000000000 : ℝ)*X 0 2+(4349130453/10000000000 : ℝ)*X 1 0+(4476265897/10000000000 : ℝ)*X 1 1+(4225518929/10000000000 : ℝ)*X 1 2+(4349130453/10000000000 : ℝ)*X 2 0+(4476265897/10000000000 : ℝ)*X 2 1+(4225518929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (284008028875414281440457/48437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1149385723/100000000000000 : ℝ)*(base19) + (107732679/10000000000000 : ℝ)*(base23) + (44964641/100000000000000 : ℝ)*(lower2) + (72107639/50000000000000 : ℝ)*(upper3) + (101626947/100000000000000 : ℝ)*(upper5) + (601786554391563/10000000000000 : ℝ)*(major0) + (601786554391563/10000000000000 : ℝ)*(major1) + (601786554391563/10000000000000 : ℝ)*(major2) + (8067795153230023/100000000000000 : ℝ)*(sp0) + (8067825946497661/100000000000000 : ℝ)*(sp1) + (8067826018556593/100000000000000 : ℝ)*(sp2) + (991971764577951/25000000000000 : ℝ)*(sp3) + (31942653361/100000000000000 : ℝ)*(sp4) + (16738189677/100000000000000 : ℝ)*(sp7) + (1983951898250741/50000000000000 : ℝ)*(f.failure) + (8067827095883383/100000000000000 : ℝ)*(f.sum) + (75392024867/31000000000000000000000000 : ℝ)*base66 + (4317838976184487/387500000000000000000000000000 : ℝ)*base68 + (911495706734487/387500000000000000000000000000 : ℝ)*base70 + (45403009246987/387500000000000000000000000000 : ℝ)*base72 + (28179458623/7750000000000000000000000 : ℝ)*base74 + (2939274164328013/387500000000000000000000000000 : ℝ)*base75 + (2654620955596987/387500000000000000000000000000 : ℝ)*base78 + (4669766933434487/387500000000000000000000000000 : ℝ)*base80 + (226066389/248000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (18294779/1000000000000000000000 : ℝ)*base89 + (18294779/1000000000000000000000 : ℝ)*base91 + (18294779/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51486843955177181919737427/20828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78084937/3125000000000 : ℝ)*(base19) + (34164971/1000000000000 : ℝ)*(base23) + (53115461/20000000000000 : ℝ)*(upper2) + (120912877/50000000000000 : ℝ)*(upper5) + (1512115860966719/25000000000000 : ℝ)*(major0) + (1512115860966719/25000000000000 : ℝ)*(major1) + (1512115860966719/25000000000000 : ℝ)*(major2) + (9107972173/100000000000000 : ℝ)*(sp0) + (7642272101/12500000000000 : ℝ)*(sp1) + (57752328883/100000000000000 : ℝ)*(sp2) + (8108839052736141/100000000000000 : ℝ)*(sp4) + (4054392261906761/50000000000000 : ℝ)*(sp5) + (2027196747970583/25000000000000 : ℝ)*(sp6) + (997019661156469/25000000000000 : ℝ)*(sp7) + (997019661156469/25000000000000 : ℝ)*(f.failure) + (4054424080354157/50000000000000 : ℝ)*(f.sum) + (29951588471639/6665000000000000000000000000 : ℝ)*base65 + (542927063790938033/41656250000000000000000000000000 : ℝ)*base68 + (521696473265813033/41656250000000000000000000000000 : ℝ)*base70 + (320227647067313033/41656250000000000000000000000000 : ℝ)*base72 + (12454175786873/3332500000000000000000000000 : ℝ)*base74 + (662227805064125533/41656250000000000000000000000000 : ℝ)*base76 + (138667803590218217/41656250000000000000000000000000 : ℝ)*base77 + (1147062144502875533/41656250000000000000000000000000 : ℝ)*base80 + (7896281288171/6665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (9209211/500000000000000000000 : ℝ)*base89 + (9209211/500000000000000000000 : ℝ)*base91 + (9209211/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1254_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1254_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1254_s7_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-264306113/1250000000 : ℝ)*x 0 + (5390967829/10000000000 : ℝ)*x 1 + (5267379299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264306113/1250000000 : ℝ)^8447 ≤ (803723319143/6250000000000 : ℝ)^6399 := by
    have hnat : (264306113 : ℕ)^8447*6250000000000^6399 ≤ 803723319143^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264306113 1250000000 803723319143 6250000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390967829/10000000000 : ℝ)^8447 ≤ (44237103009761/100000000000000 : ℝ)^6399 := by
    have hnat : (5390967829 : ℕ)^8447*100000000000000^6399 ≤ 44237103009761^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390967829 10000000000 44237103009761 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267379299/10000000000 : ℝ)^8447 ≤ (42903323871521/100000000000000 : ℝ)^6399 := by
    have hnat : (5267379299 : ℕ)^8447*100000000000000^6399 ≤ 42903323871521^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267379299 10000000000 42903323871521 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264306113/1250000000 : ℝ), (5390967829/10000000000 : ℝ), (5267379299/10000000000 : ℝ)] ![(803723319143/6250000000000 : ℝ), (44237103009761/100000000000000 : ℝ), (42903323871521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264306113/1250000000 : ℝ)|^8447 ≤ (803723319143/6250000000000 : ℝ)^6399
        have hw : |(-264306113/1250000000 : ℝ)|=(264306113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390967829/10000000000 : ℝ)|^8447 ≤ (44237103009761/100000000000000 : ℝ)^6399
        have hw : |(5390967829/10000000000 : ℝ)|=(5390967829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267379299/10000000000 : ℝ)|^8447 ≤ (42903323871521/100000000000000 : ℝ)^6399
        have hw : |(5267379299/10000000000 : ℝ)|=(5267379299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s7_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336060879/2500000000 : ℝ)*x 0 + (-2177108639/10000000000 : ℝ)*x 1 + (2633689647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336060879/2500000000 : ℝ)^8447 ≤ (8746337331241/20000000000000 : ℝ)^6399 := by
    have hnat : (1336060879 : ℕ)^8447*20000000000000^6399 ≤ 8746337331241^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336060879 2500000000 8746337331241 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177108639/10000000000 : ℝ)^8447 ≤ (13364989513211/100000000000000 : ℝ)^6399 := by
    have hnat : (2177108639 : ℕ)^8447*100000000000000^6399 ≤ 13364989513211^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177108639 10000000000 13364989513211 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633689647/5000000000 : ℝ)^8447 ≤ (42903323817761/100000000000000 : ℝ)^6399 := by
    have hnat : (2633689647 : ℕ)^8447*100000000000000^6399 ≤ 42903323817761^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633689647 5000000000 42903323817761 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336060879/2500000000 : ℝ), (-2177108639/10000000000 : ℝ), (2633689647/5000000000 : ℝ)] ![(8746337331241/20000000000000 : ℝ), (13364989513211/100000000000000 : ℝ), (42903323817761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336060879/2500000000 : ℝ)|^8447 ≤ (8746337331241/20000000000000 : ℝ)^6399
        have hw : |(1336060879/2500000000 : ℝ)|=(1336060879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177108639/10000000000 : ℝ)|^8447 ≤ (13364989513211/100000000000000 : ℝ)^6399
        have hw : |(-2177108639/10000000000 : ℝ)|=(2177108639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633689647/5000000000 : ℝ)|^8447 ≤ (42903323817761/100000000000000 : ℝ)^6399
        have hw : |(2633689647/5000000000 : ℝ)|=(2633689647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s7_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672121781/5000000000 : ℝ)*x 0 + (5267379263/10000000000 : ℝ)*x 1 + (-108855431/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672121781/5000000000 : ℝ)^8447 ≤ (43731687153093/100000000000000 : ℝ)^6399 := by
    have hnat : (2672121781 : ℕ)^8447*100000000000000^6399 ≤ 43731687153093^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672121781 5000000000 43731687153093 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267379263/10000000000 : ℝ)^8447 ≤ (42903323484451/100000000000000 : ℝ)^6399 := by
    have hnat : (5267379263 : ℕ)^8447*100000000000000^6399 ≤ 42903323484451^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267379263 10000000000 42903323484451 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108855431/500000000 : ℝ)^8447 ≤ (6682494679621/50000000000000 : ℝ)^6399 := by
    have hnat : (108855431 : ℕ)^8447*50000000000000^6399 ≤ 6682494679621^6399*500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108855431 500000000 6682494679621 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672121781/5000000000 : ℝ), (5267379263/10000000000 : ℝ), (-108855431/500000000 : ℝ)] ![(43731687153093/100000000000000 : ℝ), (42903323484451/100000000000000 : ℝ), (6682494679621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672121781/5000000000 : ℝ)|^8447 ≤ (43731687153093/100000000000000 : ℝ)^6399
        have hw : |(2672121781/5000000000 : ℝ)|=(2672121781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267379263/10000000000 : ℝ)|^8447 ≤ (42903323484451/100000000000000 : ℝ)^6399
        have hw : |(5267379263/10000000000 : ℝ)|=(5267379263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108855431/500000000 : ℝ)|^8447 ≤ (6682494679621/50000000000000 : ℝ)^6399
        have hw : |(-108855431/500000000 : ℝ)|=(108855431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s7_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349130309/10000000000 : ℝ)*x 0 + (2112622729/5000000000 : ℝ)*x 1 + (2238267253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349130309/10000000000 : ℝ)^8447 ≤ (33317554131391/100000000000000 : ℝ)^6399 := by
    have hnat : (4349130309 : ℕ)^8447*100000000000000^6399 ≤ 33317554131391^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349130309 10000000000 33317554131391 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112622729/5000000000 : ℝ)^8447 ≤ (8017627294239/25000000000000 : ℝ)^6399 := by
    have hnat : (2112622729 : ℕ)^8447*25000000000000^6399 ≤ 8017627294239^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112622729 5000000000 8017627294239 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238267253/5000000000 : ℝ)^8447 ≤ (17305968338953/50000000000000 : ℝ)^6399 := by
    have hnat : (2238267253 : ℕ)^8447*50000000000000^6399 ≤ 17305968338953^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238267253 5000000000 17305968338953 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349130309/10000000000 : ℝ), (2112622729/5000000000 : ℝ), (2238267253/5000000000 : ℝ)] ![(33317554131391/100000000000000 : ℝ), (8017627294239/25000000000000 : ℝ), (17305968338953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349130309/10000000000 : ℝ)|^8447 ≤ (33317554131391/100000000000000 : ℝ)^6399
        have hw : |(4349130309/10000000000 : ℝ)|=(4349130309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112622729/5000000000 : ℝ)|^8447 ≤ (8017627294239/25000000000000 : ℝ)^6399
        have hw : |(2112622729/5000000000 : ℝ)|=(2112622729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2238267253/5000000000 : ℝ)|^8447 ≤ (17305968338953/50000000000000 : ℝ)^6399
        have hw : |(2238267253/5000000000 : ℝ)|=(2238267253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s7_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528613353/2500000000 : ℝ)*x 0 + (1316922861/2500000000 : ℝ)*x 1 + (1078130929/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528613353/2500000000 : ℝ)^8447 ≤ (3214902324389/25000000000000 : ℝ)^6399 := by
    have hnat : (528613353 : ℕ)^8447*25000000000000^6399 ≤ 3214902324389^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528613353 2500000000 3214902324389 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316922861/2500000000 : ℝ)^8447 ≤ (21453340033439/50000000000000 : ℝ)^6399 := by
    have hnat : (1316922861 : ℕ)^8447*50000000000000^6399 ≤ 21453340033439^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316922861 2500000000 21453340033439 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078130929/2000000000 : ℝ)^8447 ≤ (1105842765479/2500000000000 : ℝ)^6399 := by
    have hnat : (1078130929 : ℕ)^8447*2500000000000^6399 ≤ 1105842765479^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078130929 2000000000 1105842765479 2500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528613353/2500000000 : ℝ), (1316922861/2500000000 : ℝ), (1078130929/2000000000 : ℝ)] ![(3214902324389/25000000000000 : ℝ), (21453340033439/50000000000000 : ℝ), (1105842765479/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528613353/2500000000 : ℝ)|^8447 ≤ (3214902324389/25000000000000 : ℝ)^6399
        have hw : |(-528613353/2500000000 : ℝ)|=(528613353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316922861/2500000000 : ℝ)|^8447 ≤ (21453340033439/50000000000000 : ℝ)^6399
        have hw : |(1316922861/2500000000 : ℝ)|=(1316922861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078130929/2000000000 : ℝ)|^8447 ≤ (1105842765479/2500000000000 : ℝ)^6399
        have hw : |(1078130929/2000000000 : ℝ)|=(1078130929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s7_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656341889/5000000000 : ℝ)*x 0 + (-2053833049/10000000000 : ℝ)*x 1 + (2695327467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656341889/5000000000 : ℝ)^8447 ≤ (43391103939559/100000000000000 : ℝ)^6399 := by
    have hnat : (2656341889 : ℕ)^8447*100000000000000^6399 ≤ 43391103939559^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656341889 5000000000 43391103939559 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2053833049/10000000000 : ℝ)^8447 ≤ (12375182292139/100000000000000 : ℝ)^6399 := by
    have hnat : (2053833049 : ℕ)^8447*100000000000000^6399 ≤ 12375182292139^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053833049 10000000000 12375182292139 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695327467/5000000000 : ℝ)^8447 ≤ (22116856874781/50000000000000 : ℝ)^6399 := by
    have hnat : (2695327467 : ℕ)^8447*50000000000000^6399 ≤ 22116856874781^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695327467 5000000000 22116856874781 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656341889/5000000000 : ℝ), (-2053833049/10000000000 : ℝ), (2695327467/5000000000 : ℝ)] ![(43391103939559/100000000000000 : ℝ), (12375182292139/100000000000000 : ℝ), (22116856874781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656341889/5000000000 : ℝ)|^8447 ≤ (43391103939559/100000000000000 : ℝ)^6399
        have hw : |(2656341889/5000000000 : ℝ)|=(2656341889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2053833049/10000000000 : ℝ)|^8447 ≤ (12375182292139/100000000000000 : ℝ)^6399
        have hw : |(-2053833049/10000000000 : ℝ)|=(2053833049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695327467/5000000000 : ℝ)|^8447 ≤ (22116856874781/50000000000000 : ℝ)^6399
        have hw : |(2695327467/5000000000 : ℝ)|=(2695327467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s7_6 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062536747/2000000000 : ℝ)*x 0 + (5390655047/10000000000 : ℝ)*x 1 + (-1026916477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062536747/2000000000 : ℝ)^8447 ≤ (43391103475957/100000000000000 : ℝ)^6399 := by
    have hnat : (1062536747 : ℕ)^8447*100000000000000^6399 ≤ 43391103475957^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062536747 2000000000 43391103475957 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390655047/10000000000 : ℝ)^8447 ≤ (1105842874339/2500000000000 : ℝ)^6399 := by
    have hnat : (5390655047 : ℕ)^8447*2500000000000^6399 ≤ 1105842874339^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390655047 10000000000 1105842874339 2500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026916477/5000000000 : ℝ)^8447 ≤ (495007261461/4000000000000 : ℝ)^6399 := by
    have hnat : (1026916477 : ℕ)^8447*4000000000000^6399 ≤ 495007261461^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026916477 5000000000 495007261461 4000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062536747/2000000000 : ℝ), (5390655047/10000000000 : ℝ), (-1026916477/5000000000 : ℝ)] ![(43391103475957/100000000000000 : ℝ), (1105842874339/2500000000000 : ℝ), (495007261461/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062536747/2000000000 : ℝ)|^8447 ≤ (43391103475957/100000000000000 : ℝ)^6399
        have hw : |(1062536747/2000000000 : ℝ)|=(1062536747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390655047/10000000000 : ℝ)|^8447 ≤ (1105842874339/2500000000000 : ℝ)^6399
        have hw : |(5390655047/10000000000 : ℝ)|=(5390655047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026916477/5000000000 : ℝ)|^8447 ≤ (495007261461/4000000000000 : ℝ)^6399
        have hw : |(-1026916477/5000000000 : ℝ)|=(1026916477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s7_7 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087284929/2500000000 : ℝ)*x 0 + (447590069/1000000000 : ℝ)*x 1 + (4225881577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087284929/2500000000 : ℝ)^8447 ≤ (8329412315067/25000000000000 : ℝ)^6399 := by
    have hnat : (1087284929 : ℕ)^8447*25000000000000^6399 ≤ 8329412315067^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087284929 2500000000 8329412315067 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447590069/1000000000 : ℝ)^8447 ≤ (6921093563719/20000000000000 : ℝ)^6399 := by
    have hnat : (447590069 : ℕ)^8447*20000000000000^6399 ≤ 6921093563719^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447590069 1000000000 6921093563719 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225881577/10000000000 : ℝ)^8447 ≤ (32076882899083/100000000000000 : ℝ)^6399 := by
    have hnat : (4225881577 : ℕ)^8447*100000000000000^6399 ≤ 32076882899083^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225881577 10000000000 32076882899083 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087284929/2500000000 : ℝ), (447590069/1000000000 : ℝ), (4225881577/10000000000 : ℝ)] ![(8329412315067/25000000000000 : ℝ), (6921093563719/20000000000000 : ℝ), (32076882899083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087284929/2500000000 : ℝ)|^8447 ≤ (8329412315067/25000000000000 : ℝ)^6399
        have hw : |(1087284929/2500000000 : ℝ)|=(1087284929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447590069/1000000000 : ℝ)|^8447 ≤ (6921093563719/20000000000000 : ℝ)^6399
        have hw : |(447590069/1000000000 : ℝ)|=(447590069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225881577/10000000000 : ℝ)|^8447 ≤ (32076882899083/100000000000000 : ℝ)^6399
        have hw : |(4225881577/10000000000 : ℝ)|=(4225881577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11493/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14111/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11489/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11489/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11489/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11489/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11489/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11489/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11489/100000 : ℝ) ^ (4223/1024 : ℝ) ≤ (1332238222406089/10000000000000000000 : ℝ) := by
    have hpowers : (11489/100000 : ℝ)^4223 ≤ (1332238222406089/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11489 : ℕ)^4223*10000000000000000000^1024 ≤ 1332238222406089^1024*100000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11489 100000 1332238222406089 10000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11489/100000 : ℝ)) (X := (1332238222406089/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2823/20000 : ℝ) ^ (4223/1024 : ℝ) ≤ (1245443474023809/4000000000000000000 : ℝ) := by
    have hpowers : (2823/20000 : ℝ)^4223 ≤ (1245443474023809/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2823 : ℕ)^4223*4000000000000000000^1024 ≤ 1245443474023809^1024*20000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 20000 1245443474023809 4000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/20000 : ℝ)) (X := (1245443474023809/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001332238222406089/5000000000000000000 : ℝ) ≤ (200012920428943/200000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (5001332238222406089/5000000000000000000 : ℝ)^1024 ≤ (200012920428943/200000000000000 : ℝ)^4223 := by
      have hnat : (5001332238222406089 : ℕ)^1024*200000000000000^4223 ≤ 200012920428943^4223*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001332238222406089 5000000000000000000 200012920428943 200000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200012920428943/200000000000000 : ℝ)) (X := (5001332238222406089/5000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008891693814931223/20000000000000000000 : ℝ) ≤ (2500269463700391/2500000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (20008891693814931223/20000000000000000000 : ℝ)^1024 ≤ (2500269463700391/2500000000000000 : ℝ)^4223 := by
      have hnat : (20008891693814931223 : ℕ)^1024*2500000000000000^4223 ≤ 2500269463700391^4223*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008891693814931223 20000000000000000000 2500269463700391 2500000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500269463700391/2500000000000000 : ℝ)) (X := (20008891693814931223/20000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001245443474023809/2000000000000000000 : ℝ) ≤ (5000754844077989/5000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (2001245443474023809/2000000000000000000 : ℝ)^1024 ≤ (5000754844077989/5000000000000000 : ℝ)^4223 := by
      have hnat : (2001245443474023809 : ℕ)^1024*5000000000000000^4223 ≤ 5000754844077989^4223*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001245443474023809 2000000000000000000 5000754844077989 5000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000754844077989/5000000000000000 : ℝ)) (X := (2001245443474023809/2000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1332238222406089/10000000000000000000 : ℝ) ≤ ((205091982699238211/205156250000000000 : ℝ)+2*(215916677207/131300000000000 : ℝ)*(11489/100000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (205091982699238211/205156250000000000 : ℝ)+2*(215916677207/131300000000000 : ℝ)*(11489/100000 : ℝ)=(200012920428943/200000000000000 : ℝ) by norm_num, show 1+2*(1332238222406089/10000000000000000000 : ℝ)=(5001332238222406089/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1245443474023809/4000000000000000000 : ℝ)+(1332238222406089/10000000000000000000 : ℝ) ≤ ((205091982699238211/205156250000000000 : ℝ)+(215916677207/131300000000000 : ℝ)*((2823/20000 : ℝ)+(11489/100000 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (205091982699238211/205156250000000000 : ℝ)+(215916677207/131300000000000 : ℝ)*((2823/20000 : ℝ)+(11489/100000 : ℝ))=(2500269463700391/2500000000000000 : ℝ) by norm_num, show 1+(1245443474023809/4000000000000000000 : ℝ)+(1332238222406089/10000000000000000000 : ℝ)=(20008891693814931223/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1245443474023809/4000000000000000000 : ℝ) ≤ ((205091982699238211/205156250000000000 : ℝ)+2*(215916677207/131300000000000 : ℝ)*(2823/20000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (205091982699238211/205156250000000000 : ℝ)+2*(215916677207/131300000000000 : ℝ)*(2823/20000 : ℝ)=(5000754844077989/5000000000000000 : ℝ) by norm_num, show 1+2*(1245443474023809/4000000000000000000 : ℝ)=(2001245443474023809/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (205091982699238211/205156250000000000 : ℝ)*(X 1 0+X 2 0)+(215916677207/131300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11489/100000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (205091982699238211/205156250000000000 : ℝ)) (alpha := (215916677207/131300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (205091982699238211/205156250000000000 : ℝ)*(X 0 1+X 2 1)+(215916677207/131300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11489/100000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (205091982699238211/205156250000000000 : ℝ)) (alpha := (215916677207/131300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (205091982699238211/205156250000000000 : ℝ)*(X 0 2+X 1 2)+(215916677207/131300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11489/100000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (205091982699238211/205156250000000000 : ℝ)) (alpha := (215916677207/131300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-264306113/1250000000 : ℝ)*X 0 0+(5390967829/10000000000 : ℝ)*X 0 1+(5267379299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336060879/2500000000 : ℝ)*X 1 0+(-2177108639/10000000000 : ℝ)*X 1 1+(2633689647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672121781/5000000000 : ℝ)*X 2 0+(5267379263/10000000000 : ℝ)*X 2 1+(-108855431/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349130309/10000000000 : ℝ)*X 0 0+(2112622729/5000000000 : ℝ)*X 0 1+(2238267253/5000000000 : ℝ)*X 0 2+(4349130309/10000000000 : ℝ)*X 1 0+(2112622729/5000000000 : ℝ)*X 1 1+(2238267253/5000000000 : ℝ)*X 1 2+(4349130309/10000000000 : ℝ)*X 2 0+(2112622729/5000000000 : ℝ)*X 2 1+(2238267253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528613353/2500000000 : ℝ)*X 0 0+(1316922861/2500000000 : ℝ)*X 0 1+(1078130929/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656341889/5000000000 : ℝ)*X 1 0+(-2053833049/10000000000 : ℝ)*X 1 1+(2695327467/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062536747/2000000000 : ℝ)*X 2 0+(5390655047/10000000000 : ℝ)*X 2 1+(-1026916477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087284929/2500000000 : ℝ)*X 0 0+(447590069/1000000000 : ℝ)*X 0 1+(4225881577/10000000000 : ℝ)*X 0 2+(1087284929/2500000000 : ℝ)*X 1 0+(447590069/1000000000 : ℝ)*X 1 1+(4225881577/10000000000 : ℝ)*X 1 2+(1087284929/2500000000 : ℝ)*X 2 0+(447590069/1000000000 : ℝ)*X 2 1+(4225881577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22650398958811402342233/6565000000000000000000000000 : ℝ) := by norm_num
    linear_combination (179737059/25000000000000 : ℝ)*(base19) + (178672073/25000000000000 : ℝ)*(base23) + (19748541/50000000000000 : ℝ)*(lower2) + (19231923/25000000000000 : ℝ)*(upper3) + (4217411/6250000000000 : ℝ)*(upper5) + (6035453418981563/100000000000000 : ℝ)*(major0) + (6035453418981563/100000000000000 : ℝ)*(major1) + (6035453418981563/100000000000000 : ℝ)*(major2) + (1011423157257267/12500000000000 : ℝ)*(sp0) + (4045702785750729/50000000000000 : ℝ)*(sp1) + (4045702787880701/50000000000000 : ℝ)*(sp2) + (994872557722613/25000000000000 : ℝ)*(sp3) + (10516195779/50000000000000 : ℝ)*(sp4) + (510080857/5000000000000 : ℝ)*(sp7) + (497437554063449/12500000000000 : ℝ)*(f.failure) + (4045703145224847/50000000000000 : ℝ)*(f.sum) + (13043577293121/6565000000000000000000000000 : ℝ)*base65 + (48795824379351789/41031250000000000000000000000000 : ℝ)*base68 + (30581182195585711/41031250000000000000000000000000 : ℝ)*base69 + (602412862595273211/41031250000000000000000000000000 : ℝ)*base71 + (16839218733469/6565000000000000000000000000 : ℝ)*base74 + (390547035411101789/41031250000000000000000000000000 : ℝ)*base76 + (3949612796898211/41031250000000000000000000000000 : ℝ)*base77 + (590755868504039289/41031250000000000000000000000000 : ℝ)*base80 + (6482165084839/6565000000000000000000000000 : ℝ)*base82 + (812169/250000000000000000000 : ℝ)*base90 + (812169/250000000000000000000 : ℝ)*base92 + (812169/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78778195403579988396888453/10257812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (19815987/2500000000000 : ℝ)*(base19) + (1181740251/100000000000000 : ℝ)*(base23) + (21383329/10000000000000 : ℝ)*(upper3) + (165776247/100000000000000 : ℝ)*(lower4) + (189565780629487/3125000000000 : ℝ)*(major0) + (189565780629487/3125000000000 : ℝ)*(major1) + (189565780629487/3125000000000 : ℝ)*(major2) + (31356626403/100000000000000 : ℝ)*(sp1) + (55409404371/100000000000000 : ℝ)*(sp2) + (6716662917/100000000000000 : ℝ)*(sp3) + (813249904192637/10000000000000 : ℝ)*(sp4) + (8132466892660487/100000000000000 : ℝ)*(sp5) + (8132442450781747/100000000000000 : ℝ)*(sp6) + (199985197285187/5000000000000 : ℝ)*(sp7) + (3999710662366657/100000000000000 : ℝ)*(f.failure) + (813249904192637/10000000000000 : ℝ)*(f.sum) + (5105435736443/6565000000000000000000000000 : ℝ)*base65 + (41012461481915987/10257812500000000000000000000000 : ℝ)*base67 + (11306949773295403/2564453125000000000000000000000 : ℝ)*base69 + (241768151442066349/20515625000000000000000000000000 : ℝ)*base71 + (7306324888751/3282500000000000000000000000 : ℝ)*base74 + (70693726258146513/10257812500000000000000000000000 : ℝ)*base76 + (35415223293450181/5128906250000000000000000000000 : ℝ)*base77 + (10374951754456069/5128906250000000000000000000000 : ℝ)*base80 + (2422725166957/1641250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1750383/2000000000000000000000 : ℝ)*base89 + (1750383/2000000000000000000000 : ℝ)*base91 + (1750383/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1254_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1254_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1254_s8_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528612891/2500000000 : ℝ)*x 0 + (5390931093/10000000000 : ℝ)*x 1 + (2633707161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528612891/2500000000 : ℝ)^8447 ≤ (12859594461381/100000000000000 : ℝ)^6399 := by
    have hnat : (528612891 : ℕ)^8447*100000000000000^6399 ≤ 12859594461381^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528612891 2500000000 12859594461381 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390931093/10000000000 : ℝ)^8447 ≤ (5529588135539/12500000000000 : ℝ)^6399 := by
    have hnat : (5390931093 : ℕ)^8447*12500000000000^6399 ≤ 5529588135539^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390931093 10000000000 5529588135539 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633707161/5000000000 : ℝ)^8447 ≤ (42903700437029/100000000000000 : ℝ)^6399 := by
    have hnat : (2633707161 : ℕ)^8447*100000000000000^6399 ≤ 42903700437029^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633707161 5000000000 42903700437029 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528612891/2500000000 : ℝ), (5390931093/10000000000 : ℝ), (2633707161/5000000000 : ℝ)] ![(12859594461381/100000000000000 : ℝ), (5529588135539/12500000000000 : ℝ), (42903700437029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528612891/2500000000 : ℝ)|^8447 ≤ (12859594461381/100000000000000 : ℝ)^6399
        have hw : |(-528612891/2500000000 : ℝ)|=(528612891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390931093/10000000000 : ℝ)|^8447 ≤ (5529588135539/12500000000000 : ℝ)^6399
        have hw : |(5390931093/10000000000 : ℝ)|=(5390931093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633707161/5000000000 : ℝ)|^8447 ≤ (42903700437029/100000000000000 : ℝ)^6399
        have hw : |(2633707161/5000000000 : ℝ)|=(2633707161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s8_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672117117/5000000000 : ℝ)*x 0 + (-2177074419/10000000000 : ℝ)*x 1 + (526741441/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672117117/5000000000 : ℝ)^8447 ≤ (43731586392947/100000000000000 : ℝ)^6399 := by
    have hnat : (2672117117 : ℕ)^8447*100000000000000^6399 ≤ 43731586392947^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672117117 5000000000 43731586392947 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177074419/10000000000 : ℝ)^8447 ≤ (1670589026017/12500000000000 : ℝ)^6399 := by
    have hnat : (2177074419 : ℕ)^8447*12500000000000^6399 ≤ 1670589026017^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177074419 10000000000 1670589026017 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526741441/1000000000 : ℝ)^8447 ≤ (42903701383201/100000000000000 : ℝ)^6399 := by
    have hnat : (526741441 : ℕ)^8447*100000000000000^6399 ≤ 42903701383201^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526741441 1000000000 42903701383201 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672117117/5000000000 : ℝ), (-2177074419/10000000000 : ℝ), (526741441/1000000000 : ℝ)] ![(43731586392947/100000000000000 : ℝ), (1670589026017/12500000000000 : ℝ), (42903701383201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672117117/5000000000 : ℝ)|^8447 ≤ (43731586392947/100000000000000 : ℝ)^6399
        have hw : |(2672117117/5000000000 : ℝ)|=(2672117117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177074419/10000000000 : ℝ)|^8447 ≤ (1670589026017/12500000000000 : ℝ)^6399
        have hw : |(-2177074419/10000000000 : ℝ)|=(2177074419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526741441/1000000000 : ℝ)|^8447 ≤ (42903701383201/100000000000000 : ℝ)^6399
        have hw : |(526741441/1000000000 : ℝ)|=(526741441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s8_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1057228317/5000000000 : ℝ)*x 0 + (5144263/9765625 : ℝ)*x 1 + (2695309319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057228317/5000000000 : ℝ)^8447 ≤ (12859635164533/100000000000000 : ℝ)^6399 := by
    have hnat : (1057228317 : ℕ)^8447*100000000000000^6399 ≤ 12859635164533^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057228317 5000000000 12859635164533 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144263/9765625 : ℝ)^8447 ≤ (21453522110389/50000000000000 : ℝ)^6399 := by
    have hnat : (5144263 : ℕ)^8447*50000000000000^6399 ≤ 21453522110389^6399*9765625^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144263 9765625 21453522110389 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695309319/5000000000 : ℝ)^8447 ≤ (8846664119501/20000000000000 : ℝ)^6399 := by
    have hnat : (2695309319 : ℕ)^8447*20000000000000^6399 ≤ 8846664119501^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695309319 5000000000 8846664119501 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1057228317/5000000000 : ℝ), (5144263/9765625 : ℝ), (2695309319/5000000000 : ℝ)] ![(12859635164533/100000000000000 : ℝ), (21453522110389/50000000000000 : ℝ), (8846664119501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1057228317/5000000000 : ℝ)|^8447 ≤ (12859635164533/100000000000000 : ℝ)^6399
        have hw : |(-1057228317/5000000000 : ℝ)|=(1057228317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144263/9765625 : ℝ)|^8447 ≤ (21453522110389/50000000000000 : ℝ)^6399
        have hw : |(5144263/9765625 : ℝ)|=(5144263/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695309319/5000000000 : ℝ)|^8447 ≤ (8846664119501/20000000000000 : ℝ)^6399
        have hw : |(2695309319/5000000000 : ℝ)|=(2695309319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s8_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312693477/10000000000 : ℝ)*x 0 + (-2053869629/10000000000 : ℝ)*x 1 + (5390618419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312693477/10000000000 : ℝ)^8447 ≤ (43391208508859/100000000000000 : ℝ)^6399 := by
    have hnat : (5312693477 : ℕ)^8447*100000000000000^6399 ≤ 43391208508859^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312693477 10000000000 43391208508859 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2053869629/10000000000 : ℝ)^8447 ≤ (3093868311109/25000000000000 : ℝ)^6399 := by
    have hnat : (2053869629 : ℕ)^8447*25000000000000^6399 ≤ 3093868311109^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053869629 10000000000 3093868311109 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390618419/10000000000 : ℝ)^8447 ≤ (44233318225337/100000000000000 : ℝ)^6399 := by
    have hnat : (5390618419 : ℕ)^8447*100000000000000^6399 ≤ 44233318225337^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390618419 10000000000 44233318225337 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312693477/10000000000 : ℝ), (-2053869629/10000000000 : ℝ), (5390618419/10000000000 : ℝ)] ![(43391208508859/100000000000000 : ℝ), (3093868311109/25000000000000 : ℝ), (44233318225337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312693477/10000000000 : ℝ)|^8447 ≤ (43391208508859/100000000000000 : ℝ)^6399
        have hw : |(5312693477/10000000000 : ℝ)|=(5312693477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2053869629/10000000000 : ℝ)|^8447 ≤ (3093868311109/25000000000000 : ℝ)^6399
        have hw : |(-2053869629/10000000000 : ℝ)|=(2053869629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390618419/10000000000 : ℝ)|^8447 ≤ (44233318225337/100000000000000 : ℝ)^6399
        have hw : |(5390618419/10000000000 : ℝ)|=(5390618419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s8_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312693377/10000000000 : ℝ)*x 0 + (2695308987/5000000000 : ℝ)*x 1 + (-513467593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312693377/10000000000 : ℝ)^8447 ≤ (21695603715357/50000000000000 : ℝ)^6399 := by
    have hnat : (5312693377 : ℕ)^8447*50000000000000^6399 ≤ 21695603715357^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312693377 10000000000 21695603715357 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695308987/5000000000 : ℝ)^8447 ≤ (22116656702589/50000000000000 : ℝ)^6399 := by
    have hnat : (2695308987 : ℕ)^8447*50000000000000^6399 ≤ 22116656702589^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695308987 5000000000 22116656702589 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513467593/2500000000 : ℝ)^8447 ≤ (12375479154173/100000000000000 : ℝ)^6399 := by
    have hnat : (513467593 : ℕ)^8447*100000000000000^6399 ≤ 12375479154173^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513467593 2500000000 12375479154173 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312693377/10000000000 : ℝ), (2695308987/5000000000 : ℝ), (-513467593/2500000000 : ℝ)] ![(21695603715357/50000000000000 : ℝ), (22116656702589/50000000000000 : ℝ), (12375479154173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312693377/10000000000 : ℝ)|^8447 ≤ (21695603715357/50000000000000 : ℝ)^6399
        have hw : |(5312693377/10000000000 : ℝ)|=(5312693377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695308987/5000000000 : ℝ)|^8447 ≤ (22116656702589/50000000000000 : ℝ)^6399
        have hw : |(2695308987/5000000000 : ℝ)|=(2695308987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-513467593/2500000000 : ℝ)|^8447 ≤ (12375479154173/100000000000000 : ℝ)^6399
        have hw : |(-513467593/2500000000 : ℝ)|=(513467593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s8_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174570643/5000000000 : ℝ)*x 0 + (4475828167/10000000000 : ℝ)*x 1 + (2112976931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174570643/5000000000 : ℝ)^8447 ≤ (33317665136997/100000000000000 : ℝ)^6399 := by
    have hnat : (2174570643 : ℕ)^8447*100000000000000^6399 ≤ 33317665136997^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174570643 5000000000 33317665136997 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475828167/10000000000 : ℝ)^8447 ≤ (6920945530461/20000000000000 : ℝ)^6399 := by
    have hnat : (4475828167 : ℕ)^8447*20000000000000^6399 ≤ 6920945530461^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475828167 10000000000 6920945530461 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112976931/5000000000 : ℝ)^8447 ≤ (16038803596297/50000000000000 : ℝ)^6399 := by
    have hnat : (2112976931 : ℕ)^8447*50000000000000^6399 ≤ 16038803596297^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112976931 5000000000 16038803596297 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174570643/5000000000 : ℝ), (4475828167/10000000000 : ℝ), (2112976931/5000000000 : ℝ)] ![(33317665136997/100000000000000 : ℝ), (6920945530461/20000000000000 : ℝ), (16038803596297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174570643/5000000000 : ℝ)|^8447 ≤ (33317665136997/100000000000000 : ℝ)^6399
        have hw : |(2174570643/5000000000 : ℝ)|=(2174570643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475828167/10000000000 : ℝ)|^8447 ≤ (6920945530461/20000000000000 : ℝ)^6399
        have hw : |(4475828167/10000000000 : ℝ)|=(4475828167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112976931/5000000000 : ℝ)|^8447 ≤ (16038803596297/50000000000000 : ℝ)^6399
        have hw : |(2112976931/5000000000 : ℝ)|=(2112976931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s8_6 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-771891/200000000 : ℝ)*x 0 + (369503571/625000000 : ℝ)*x 1 + (2956062449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (771891/200000000 : ℝ)^8447 ≤ (65176885409/100000000000000 : ℝ)^6399 := by
    have hnat : (771891 : ℕ)^8447*100000000000000^6399 ≤ 65176885409^6399*200000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771891 200000000 65176885409 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369503571/625000000 : ℝ)^8447 ≤ (49967033548283/100000000000000 : ℝ)^6399 := by
    have hnat : (369503571 : ℕ)^8447*100000000000000^6399 ≤ 49967033548283^6399*625000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369503571 625000000 49967033548283 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956062449/5000000000 : ℝ)^8447 ≤ (3122986846827/6250000000000 : ℝ)^6399 := by
    have hnat : (2956062449 : ℕ)^8447*6250000000000^6399 ≤ 3122986846827^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956062449 5000000000 3122986846827 6250000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-771891/200000000 : ℝ), (369503571/625000000 : ℝ), (2956062449/5000000000 : ℝ)] ![(65176885409/100000000000000 : ℝ), (49967033548283/100000000000000 : ℝ), (3122986846827/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-771891/200000000 : ℝ)|^8447 ≤ (65176885409/100000000000000 : ℝ)^6399
        have hw : |(-771891/200000000 : ℝ)|=(771891/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(369503571/625000000 : ℝ)|^8447 ≤ (49967033548283/100000000000000 : ℝ)^6399
        have hw : |(369503571/625000000 : ℝ)|=(369503571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956062449/5000000000 : ℝ)|^8447 ≤ (3122986846827/6250000000000 : ℝ)^6399
        have hw : |(2956062449/5000000000 : ℝ)|=(2956062449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11493/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1411/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11493/100000 : ℝ) ^ (4223/1024 : ℝ) ≤ (13341521123123581/100000000000000000000 : ℝ) := by
    have hpowers : (11493/100000 : ℝ)^4223 ≤ (13341521123123581/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11493 : ℕ)^4223*100000000000000000000^1024 ≤ 13341521123123581^1024*100000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11493 100000 13341521123123581 100000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11493/100000 : ℝ)) (X := (13341521123123581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14111/100000 : ℝ) ^ (4223/1024 : ℝ) ≤ (31099714445621971/100000000000000000000 : ℝ) := by
    have hpowers : (14111/100000 : ℝ)^4223 ≤ (31099714445621971/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14111 : ℕ)^4223*100000000000000000000^1024 ≤ 31099714445621971^1024*100000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14111 100000 31099714445621971 100000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14111/100000 : ℝ)) (X := (31099714445621971/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013341521123123581/50000000000000000000 : ℝ) ≤ (10000646949426077/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50013341521123123581/50000000000000000000 : ℝ)^1024 ≤ (10000646949426077/10000000000000000 : ℝ)^4223 := by
      have hnat : (50013341521123123581 : ℕ)^1024*10000000000000000^4223 ≤ 10000646949426077^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013341521123123581 50000000000000000000 10000646949426077 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000646949426077/10000000000000000 : ℝ)) (X := (50013341521123123581/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252777577223046597/6250000000000000000 : ℝ) ≤ (400043097482453/400000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (6252777577223046597/6250000000000000000 : ℝ)^1024 ≤ (400043097482453/400000000000000 : ℝ)^4223 := by
      have hnat : (6252777577223046597 : ℕ)^1024*400000000000000^4223 ≤ 400043097482453^4223*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252777577223046597 6250000000000000000 400043097482453 400000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400043097482453/400000000000000 : ℝ)) (X := (6252777577223046597/6250000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031099714445621971/50000000000000000000 : ℝ) ≤ (10001507924696573/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50031099714445621971/50000000000000000000 : ℝ)^1024 ≤ (10001507924696573/10000000000000000 : ℝ)^4223 := by
      have hnat : (50031099714445621971 : ℕ)^1024*10000000000000000^4223 ≤ 10001507924696573^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031099714445621971 50000000000000000000 10001507924696573 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001507924696573/10000000000000000 : ℝ)) (X := (50031099714445621971/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13341521123123581/100000000000000000000 : ℝ) ≤ ((1189627205673348139/1190000000000000000 : ℝ)+2*(2445952473/1487500000000 : ℝ)*(11493/100000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (1189627205673348139/1190000000000000000 : ℝ)+2*(2445952473/1487500000000 : ℝ)*(11493/100000 : ℝ)=(10000646949426077/10000000000000000 : ℝ) by norm_num, show 1+2*(13341521123123581/100000000000000000000 : ℝ)=(50013341521123123581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31099714445621971/100000000000000000000 : ℝ)+(13341521123123581/100000000000000000000 : ℝ) ≤ ((1189627205673348139/1190000000000000000 : ℝ)+(2445952473/1487500000000 : ℝ)*((14111/100000 : ℝ)+(11493/100000 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (1189627205673348139/1190000000000000000 : ℝ)+(2445952473/1487500000000 : ℝ)*((14111/100000 : ℝ)+(11493/100000 : ℝ))=(400043097482453/400000000000000 : ℝ) by norm_num, show 1+(31099714445621971/100000000000000000000 : ℝ)+(13341521123123581/100000000000000000000 : ℝ)=(6252777577223046597/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31099714445621971/100000000000000000000 : ℝ) ≤ ((1189627205673348139/1190000000000000000 : ℝ)+2*(2445952473/1487500000000 : ℝ)*(14111/100000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (1189627205673348139/1190000000000000000 : ℝ)+2*(2445952473/1487500000000 : ℝ)*(14111/100000 : ℝ)=(10001507924696573/10000000000000000 : ℝ) by norm_num, show 1+2*(31099714445621971/100000000000000000000 : ℝ)=(50031099714445621971/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1189627205673348139/1190000000000000000 : ℝ)*(X 1 0+X 2 0)+(2445952473/1487500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (1189627205673348139/1190000000000000000 : ℝ)) (alpha := (2445952473/1487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1189627205673348139/1190000000000000000 : ℝ)*(X 0 1+X 2 1)+(2445952473/1487500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (1189627205673348139/1190000000000000000 : ℝ)) (alpha := (2445952473/1487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1189627205673348139/1190000000000000000 : ℝ)*(X 0 2+X 1 2)+(2445952473/1487500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (1189627205673348139/1190000000000000000 : ℝ)) (alpha := (2445952473/1487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-528612891/2500000000 : ℝ)*X 0 0+(5390931093/10000000000 : ℝ)*X 0 1+(2633707161/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672117117/5000000000 : ℝ)*X 1 0+(-2177074419/10000000000 : ℝ)*X 1 1+(526741441/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1057228317/5000000000 : ℝ)*X 0 0+(5144263/9765625 : ℝ)*X 0 1+(2695309319/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s8_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312693477/10000000000 : ℝ)*X 1 0+(-2053869629/10000000000 : ℝ)*X 1 1+(5390618419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s8_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5312693377/10000000000 : ℝ)*X 2 0+(2695308987/5000000000 : ℝ)*X 2 1+(-513467593/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s8_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2174570643/5000000000 : ℝ)*X 0 0+(4475828167/10000000000 : ℝ)*X 0 1+(2112976931/5000000000 : ℝ)*X 0 2+(2174570643/5000000000 : ℝ)*X 1 0+(4475828167/10000000000 : ℝ)*X 1 1+(2112976931/5000000000 : ℝ)*X 1 2+(2174570643/5000000000 : ℝ)*X 2 0+(4475828167/10000000000 : ℝ)*X 2 1+(2112976931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((-771891/200000000 : ℝ)*X 0 0+(369503571/625000000 : ℝ)*X 0 1+(2956062449/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s8_6 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39163281281218561847267703/8500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1046269/1250000000000 : ℝ)*(upper1) + (565081741/100000000000000 : ℝ)*(lower2) + (680490331/100000000000000 : ℝ)*(lower4) + (403391001/50000000000000 : ℝ)*(lower5) + (6069620893235487/100000000000000 : ℝ)*(major0) + (6069620893235487/100000000000000 : ℝ)*(major1) + (6069620893235487/100000000000000 : ℝ)*(major2) + (53055232737/100000000000000 : ℝ)*(sp0) + (10791263777/100000000000000 : ℝ)*(sp1) + (8137151511263681/100000000000000 : ℝ)*(sp2) + (4068600973926141/50000000000000 : ℝ)*(sp3) + (8137212739116059/100000000000000 : ℝ)*(sp4) + (1000507223443353/25000000000000 : ℝ)*(sp5) + (204315491/2500000000000 : ℝ)*(sp6) + (1000507223443353/25000000000000 : ℝ)*(f.failure) + (8137212739116059/100000000000000 : ℝ)*(f.sum) + (86661953153/42500000000000000000000000 : ℝ)*base66 + (253555712051144099/17000000000000000000000000000000 : ℝ)*base67 + (284495239468144099/17000000000000000000000000000000 : ℝ)*base69 + (52234547167855901/17000000000000000000000000000000 : ℝ)*base72 + (597913054811/85000000000000000000000000 : ℝ)*base74 + (67825713796144099/17000000000000000000000000000000 : ℝ)*base75 + (11011840654855901/17000000000000000000000000000000 : ℝ)*base78 + (180678269030144099/17000000000000000000000000000000 : ℝ)*base79 + (17001007971/21250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3966807/500000000000000000000 : ℝ)*base89 + (3966807/500000000000000000000 : ℝ)*base91 + (3966807/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1254_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1254_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1254_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1254_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1254_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1254_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1254_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
