-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1300_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:36:05.936268+00:00
-- url     : https://prove2.me/submissions/4accbce1-58fa-4519-a930-5e86ca23662f

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
theorem support_rectangle_w1300_s0_0 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-36684761/200000000 : ℝ)*x 0 + (3007627383/5000000000 : ℝ)*x 1 + (2400395017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36684761/200000000 : ℝ)^1065 ≤ (10724661242449/100000000000000 : ℝ)^809 := by
    have hnat : (36684761 : ℕ)^1065*100000000000000^809 ≤ 10724661242449^809*200000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36684761 200000000 10724661242449 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3007627383/5000000000 : ℝ)^1065 ≤ (51215469570429/100000000000000 : ℝ)^809 := by
    have hnat : (3007627383 : ℕ)^1065*100000000000000^809 ≤ 51215469570429^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007627383 5000000000 51215469570429 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2400395017/5000000000 : ℝ)^1065 ≤ (7611973834361/20000000000000 : ℝ)^809 := by
    have hnat : (2400395017 : ℕ)^1065*20000000000000^809 ≤ 7611973834361^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400395017 5000000000 7611973834361 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36684761/200000000 : ℝ), (3007627383/5000000000 : ℝ), (2400395017/5000000000 : ℝ)] ![(10724661242449/100000000000000 : ℝ), (51215469570429/100000000000000 : ℝ), (7611973834361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36684761/200000000 : ℝ)|^1065 ≤ (10724661242449/100000000000000 : ℝ)^809
        have hw : |(-36684761/200000000 : ℝ)|=(36684761/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3007627383/5000000000 : ℝ)|^1065 ≤ (51215469570429/100000000000000 : ℝ)^809
        have hw : |(3007627383/5000000000 : ℝ)|=(3007627383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2400395017/5000000000 : ℝ)|^1065 ≤ (7611973834361/20000000000000 : ℝ)^809
        have hw : |(2400395017/5000000000 : ℝ)|=(2400395017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s0_1 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2753260373/5000000000 : ℝ)*x 0 + (-2526669767/10000000000 : ℝ)*x 1 + (4800790009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753260373/5000000000 : ℝ)^1065 ≤ (2849446391549/6250000000000 : ℝ)^809 := by
    have hnat : (2753260373 : ℕ)^1065*6250000000000^809 ≤ 2849446391549^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753260373 5000000000 2849446391549 6250000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2526669767/10000000000 : ℝ)^1065 ≤ (16348988806553/100000000000000 : ℝ)^809 := by
    have hnat : (2526669767 : ℕ)^1065*100000000000000^809 ≤ 16348988806553^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526669767 10000000000 16348988806553 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4800790009/10000000000 : ℝ)^1065 ≤ (9514967227723/25000000000000 : ℝ)^809 := by
    have hnat : (4800790009 : ℕ)^1065*25000000000000^809 ≤ 9514967227723^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800790009 10000000000 9514967227723 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753260373/5000000000 : ℝ), (-2526669767/10000000000 : ℝ), (4800790009/10000000000 : ℝ)] ![(2849446391549/6250000000000 : ℝ), (16348988806553/100000000000000 : ℝ), (9514967227723/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753260373/5000000000 : ℝ)|^1065 ≤ (2849446391549/6250000000000 : ℝ)^809
        have hw : |(2753260373/5000000000 : ℝ)|=(2753260373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2526669767/10000000000 : ℝ)|^1065 ≤ (16348988806553/100000000000000 : ℝ)^809
        have hw : |(-2526669767/10000000000 : ℝ)|=(2526669767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4800790009/10000000000 : ℝ)|^1065 ≤ (9514967227723/25000000000000 : ℝ)^809
        have hw : |(4800790009/10000000000 : ℝ)|=(4800790009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s0_2 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5506520717/10000000000 : ℝ)*x 0 + (150024689/312500000 : ℝ)*x 1 + (-631667439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5506520717/10000000000 : ℝ)^1065 ≤ (45591141948701/100000000000000 : ℝ)^809 := by
    have hnat : (5506520717 : ℕ)^1065*100000000000000^809 ≤ 45591141948701^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506520717 10000000000 45591141948701 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150024689/312500000 : ℝ)^1065 ≤ (9514967329479/25000000000000 : ℝ)^809 := by
    have hnat : (150024689 : ℕ)^1065*25000000000000^809 ≤ 9514967329479^809*312500000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150024689 312500000 9514967329479 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (631667439/2500000000 : ℝ)^1065 ≤ (8174494356427/50000000000000 : ℝ)^809 := by
    have hnat : (631667439 : ℕ)^1065*50000000000000^809 ≤ 8174494356427^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631667439 2500000000 8174494356427 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5506520717/10000000000 : ℝ), (150024689/312500000 : ℝ), (-631667439/2500000000 : ℝ)] ![(45591141948701/100000000000000 : ℝ), (9514967329479/25000000000000 : ℝ), (8174494356427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5506520717/10000000000 : ℝ)|^1065 ≤ (45591141948701/100000000000000 : ℝ)^809
        have hw : |(5506520717/10000000000 : ℝ)|=(5506520717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150024689/312500000 : ℝ)|^1065 ≤ (9514967329479/25000000000000 : ℝ)^809
        have hw : |(150024689/312500000 : ℝ)|=(150024689/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-631667439/2500000000 : ℝ)|^1065 ≤ (8174494356427/50000000000000 : ℝ)^809
        have hw : |(-631667439/2500000000 : ℝ)|=(631667439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s0_3 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4185104263/10000000000 : ℝ)*x 0 + (777230489/2500000000 : ℝ)*x 1 + (701570867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185104263/10000000000 : ℝ)^1065 ≤ (31768667494841/100000000000000 : ℝ)^809 := by
    have hnat : (4185104263 : ℕ)^1065*100000000000000^809 ≤ 31768667494841^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185104263 10000000000 31768667494841 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777230489/2500000000 : ℝ)^1065 ≤ (21480839310167/100000000000000 : ℝ)^809 := by
    have hnat : (777230489 : ℕ)^1065*100000000000000^809 ≤ 21480839310167^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777230489 2500000000 21480839310167 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (701570867/1250000000 : ℝ)^1065 ≤ (9350098636893/20000000000000 : ℝ)^809 := by
    have hnat : (701570867 : ℕ)^1065*20000000000000^809 ≤ 9350098636893^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701570867 1250000000 9350098636893 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185104263/10000000000 : ℝ), (777230489/2500000000 : ℝ), (701570867/1250000000 : ℝ)] ![(31768667494841/100000000000000 : ℝ), (21480839310167/100000000000000 : ℝ), (9350098636893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185104263/10000000000 : ℝ)|^1065 ≤ (31768667494841/100000000000000 : ℝ)^809
        have hw : |(4185104263/10000000000 : ℝ)|=(4185104263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(777230489/2500000000 : ℝ)|^1065 ≤ (21480839310167/100000000000000 : ℝ)^809
        have hw : |(777230489/2500000000 : ℝ)|=(777230489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(701570867/1250000000 : ℝ)|^1065 ≤ (9350098636893/20000000000000 : ℝ)^809
        have hw : |(701570867/1250000000 : ℝ)|=(701570867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s0_4 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-57466169/312500000 : ℝ)*x 0 + (4832122893/10000000000 : ℝ)*x 1 + (373925467/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57466169/312500000 : ℝ)^1065 ≤ (10760693411321/100000000000000 : ℝ)^809 := by
    have hnat : (57466169 : ℕ)^1065*100000000000000^809 ≤ 10760693411321^809*312500000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57466169 312500000 10760693411321 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4832122893/10000000000 : ℝ)^1065 ≤ (4798401540789/12500000000000 : ℝ)^809 := by
    have hnat : (4832122893 : ℕ)^1065*12500000000000^809 ≤ 4798401540789^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4832122893 10000000000 4798401540789 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373925467/625000000 : ℝ)^1065 ≤ (50852094246001/100000000000000 : ℝ)^809 := by
    have hnat : (373925467 : ℕ)^1065*100000000000000^809 ≤ 50852094246001^809*625000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373925467 625000000 50852094246001 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-57466169/312500000 : ℝ), (4832122893/10000000000 : ℝ), (373925467/625000000 : ℝ)] ![(10760693411321/100000000000000 : ℝ), (4798401540789/12500000000000 : ℝ), (50852094246001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-57466169/312500000 : ℝ)|^1065 ≤ (10760693411321/100000000000000 : ℝ)^809
        have hw : |(-57466169/312500000 : ℝ)|=(57466169/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4832122893/10000000000 : ℝ)|^1065 ≤ (4798401540789/12500000000000 : ℝ)^809
        have hw : |(4832122893/10000000000 : ℝ)|=(4832122893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(373925467/625000000 : ℝ)|^1065 ≤ (50852094246001/100000000000000 : ℝ)^809
        have hw : |(373925467/625000000 : ℝ)|=(373925467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s0_5 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5175831523/10000000000 : ℝ)*x 0 + (-1344649559/10000000000 : ℝ)*x 1 + (2991405069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175831523/10000000000 : ℝ)^1065 ≤ (21010771237137/50000000000000 : ℝ)^809 := by
    have hnat : (5175831523 : ℕ)^1065*50000000000000^809 ≤ 21010771237137^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175831523 10000000000 21010771237137 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344649559/10000000000 : ℝ)^1065 ≤ (7126333433083/100000000000000 : ℝ)^809 := by
    have hnat : (1344649559 : ℕ)^1065*100000000000000^809 ≤ 7126333433083^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344649559 10000000000 7126333433083 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2991405069/5000000000 : ℝ)^1065 ≤ (50852124076813/100000000000000 : ℝ)^809 := by
    have hnat : (2991405069 : ℕ)^1065*100000000000000^809 ≤ 50852124076813^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991405069 5000000000 50852124076813 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175831523/10000000000 : ℝ), (-1344649559/10000000000 : ℝ), (2991405069/5000000000 : ℝ)] ![(21010771237137/50000000000000 : ℝ), (7126333433083/100000000000000 : ℝ), (50852124076813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175831523/10000000000 : ℝ)|^1065 ≤ (21010771237137/50000000000000 : ℝ)^809
        have hw : |(5175831523/10000000000 : ℝ)|=(5175831523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1344649559/10000000000 : ℝ)|^1065 ≤ (7126333433083/100000000000000 : ℝ)^809
        have hw : |(-1344649559/10000000000 : ℝ)|=(1344649559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2991405069/5000000000 : ℝ)|^1065 ≤ (50852124076813/100000000000000 : ℝ)^809
        have hw : |(2991405069/5000000000 : ℝ)|=(2991405069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s0_6 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1035166569/2000000000 : ℝ)*x 0 + (5982807811/10000000000 : ℝ)*x 1 + (-1344651267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035166569/2000000000 : ℝ)^1065 ≤ (42021556603697/100000000000000 : ℝ)^809 := by
    have hnat : (1035166569 : ℕ)^1065*100000000000000^809 ≤ 42021556603697^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035166569 2000000000 42021556603697 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5982807811/10000000000 : ℝ)^1065 ≤ (50852098039191/100000000000000 : ℝ)^809 := by
    have hnat : (5982807811 : ℕ)^1065*100000000000000^809 ≤ 50852098039191^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5982807811 10000000000 50852098039191 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344651267/10000000000 : ℝ)^1065 ≤ (712634534951/10000000000000 : ℝ)^809 := by
    have hnat : (1344651267 : ℕ)^1065*10000000000000^809 ≤ 712634534951^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344651267 10000000000 712634534951 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035166569/2000000000 : ℝ), (5982807811/10000000000 : ℝ), (-1344651267/10000000000 : ℝ)] ![(42021556603697/100000000000000 : ℝ), (50852098039191/100000000000000 : ℝ), (712634534951/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035166569/2000000000 : ℝ)|^1065 ≤ (42021556603697/100000000000000 : ℝ)^809
        have hw : |(1035166569/2000000000 : ℝ)|=(1035166569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5982807811/10000000000 : ℝ)|^1065 ≤ (50852098039191/100000000000000 : ℝ)^809
        have hw : |(5982807811/10000000000 : ℝ)|=(5982807811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1344651267/10000000000 : ℝ)|^1065 ≤ (712634534951/10000000000000 : ℝ)^809
        have hw : |(-1344651267/10000000000 : ℝ)|=(1344651267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s0_7 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2097378563/5000000000 : ℝ)*x 0 + (5547981657/10000000000 : ℝ)*x 1 + (3175804909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097378563/5000000000 : ℝ)^1065 ≤ (7966290818733/25000000000000 : ℝ)^809 := by
    have hnat : (2097378563 : ℕ)^1065*25000000000000^809 ≤ 7966290818733^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097378563 5000000000 7966290818733 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5547981657/10000000000 : ℝ)^1065 ≤ (46043580506257/100000000000000 : ℝ)^809 := by
    have hnat : (5547981657 : ℕ)^1065*100000000000000^809 ≤ 46043580506257^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5547981657 10000000000 46043580506257 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3175804909/10000000000 : ℝ)^1065 ≤ (22091256207189/100000000000000 : ℝ)^809 := by
    have hnat : (3175804909 : ℕ)^1065*100000000000000^809 ≤ 22091256207189^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3175804909 10000000000 22091256207189 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097378563/5000000000 : ℝ), (5547981657/10000000000 : ℝ), (3175804909/10000000000 : ℝ)] ![(7966290818733/25000000000000 : ℝ), (46043580506257/100000000000000 : ℝ), (22091256207189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097378563/5000000000 : ℝ)|^1065 ≤ (7966290818733/25000000000000 : ℝ)^809
        have hw : |(2097378563/5000000000 : ℝ)|=(2097378563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5547981657/10000000000 : ℝ)|^1065 ≤ (46043580506257/100000000000000 : ℝ)^809
        have hw : |(5547981657/10000000000 : ℝ)|=(5547981657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3175804909/10000000000 : ℝ)|^1065 ≤ (22091256207189/100000000000000 : ℝ)^809
        have hw : |(3175804909/10000000000 : ℝ)|=(3175804909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1300_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (547/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3397/12500 : ℝ)*pair X 0 0 := by
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
  have base51 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (4259/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4259 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4259*1^1024 ≤ 0^1024*1^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4259/1024 : ℝ) ≤ (221256480116368769/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4259 ≤ (221256480116368769/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4259*10000000000000000000^1024 ≤ 221256480116368769^1024*5^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 221256480116368769 10000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (221256480116368769/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4259 := by
      have hnat : (1 : ℕ)^1024*1^4259 ≤ 1^4259*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10221256480116368769/10000000000000000000 : ℝ) ≤ (5026377921948191/5000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (10221256480116368769/10000000000000000000 : ℝ)^1024 ≤ (5026377921948191/5000000000000000 : ℝ)^4259 := by
      have hnat : (10221256480116368769 : ℕ)^1024*5000000000000000^4259 ≤ 5026377921948191^4259*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10221256480116368769 10000000000000000000 5026377921948191 5000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026377921948191/5000000000000000 : ℝ)) (X := (10221256480116368769/10000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5221256480116368769/5000000000000000000 : ℝ) ≤ (2526377921948191/2500000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (5221256480116368769/5000000000000000000 : ℝ)^1024 ≤ (2526377921948191/2500000000000000 : ℝ)^4259 := by
      have hnat : (5221256480116368769 : ℕ)^1024*2500000000000000^4259 ≤ 2526377921948191^4259*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5221256480116368769 5000000000000000000 2526377921948191 2500000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2526377921948191/2500000000000000 : ℝ)) (X := (5221256480116368769/5000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26377921948191/2000000000000000 : ℝ)*(0 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26377921948191/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(221256480116368769/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26377921948191/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4259/1024 : ℝ) := by
    rw [show (1 : ℝ)+(26377921948191/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5026377921948191/5000000000000000 : ℝ) by norm_num, show 1+(221256480116368769/10000000000000000000 : ℝ)+(0 : ℝ)=(10221256480116368769/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(221256480116368769/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26377921948191/2000000000000000 : ℝ)*(2/5 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26377921948191/2000000000000000 : ℝ)*(2/5 : ℝ)=(2526377921948191/2500000000000000 : ℝ) by norm_num, show 1+2*(221256480116368769/10000000000000000000 : ℝ)=(5221256480116368769/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26377921948191/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26377921948191/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26377921948191/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26377921948191/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26377921948191/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26377921948191/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-36684761/200000000 : ℝ)*X 0 0+(3007627383/5000000000 : ℝ)*X 0 1+(2400395017/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2753260373/5000000000 : ℝ)*X 1 0+(-2526669767/10000000000 : ℝ)*X 1 1+(4800790009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5506520717/10000000000 : ℝ)*X 2 0+(150024689/312500000 : ℝ)*X 2 1+(-631667439/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4185104263/10000000000 : ℝ)*X 0 0+(777230489/2500000000 : ℝ)*X 0 1+(701570867/1250000000 : ℝ)*X 0 2+(4185104263/10000000000 : ℝ)*X 1 0+(777230489/2500000000 : ℝ)*X 1 1+(701570867/1250000000 : ℝ)*X 1 2+(4185104263/10000000000 : ℝ)*X 2 0+(777230489/2500000000 : ℝ)*X 2 1+(701570867/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-57466169/312500000 : ℝ)*X 0 0+(4832122893/10000000000 : ℝ)*X 0 1+(373925467/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5175831523/10000000000 : ℝ)*X 1 0+(-1344649559/10000000000 : ℝ)*X 1 1+(2991405069/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1035166569/2000000000 : ℝ)*X 2 0+(5982807811/10000000000 : ℝ)*X 2 1+(-1344651267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2097378563/5000000000 : ℝ)*X 0 0+(5547981657/10000000000 : ℝ)*X 0 1+(3175804909/10000000000 : ℝ)*X 0 2+(2097378563/5000000000 : ℝ)*X 1 0+(5547981657/10000000000 : ℝ)*X 1 1+(3175804909/10000000000 : ℝ)*X 1 2+(2097378563/5000000000 : ℝ)*X 2 0+(5547981657/10000000000 : ℝ)*X 2 1+(3175804909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42812924383814049749853/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39160947/50000000000000 : ℝ)*(base1) + (1654846811/100000000000000 : ℝ)*(base19) + (1650510301/100000000000000 : ℝ)*(base23) + (38675381/20000000000000 : ℝ)*(upper3) + (97327409/50000000000000 : ℝ)*(upper5) + (152855150639611/25000000000000 : ℝ)*(major0) + (152855150639611/25000000000000 : ℝ)*(major1) + (152855150639611/25000000000000 : ℝ)*(major2) + (823413045825479/100000000000000 : ℝ)*(sp0) + (823416620137351/100000000000000 : ℝ)*(sp1) + (41170831223693/5000000000000 : ℝ)*(sp2) + (399420073857051/100000000000000 : ℝ)*(sp3) + (10366173/195312500000 : ℝ)*(sp4) + (1274809089/50000000000000 : ℝ)*(sp7) + (399422701797123/100000000000000 : ℝ)*(f.failure) + (823418274984161/100000000000000 : ℝ)*(f.sum) + (80126192681299/25000000000000000000000000000 : ℝ)*base66 + (151355244806299/50000000000000000000000000000 : ℝ)*base68 + (297193230406299/50000000000000000000000000000 : ℝ)*base70 + (582847579956299/50000000000000000000000000000 : ℝ)*base72 + (56621217268701/25000000000000000000000000000 : ℝ)*base73 + (817912530456299/50000000000000000000000000000 : ℝ)*base76 + (316046268656299/50000000000000000000000000000 : ℝ)*base78 + (447492044706299/50000000000000000000000000000 : ℝ)*base80 + (31594230056299/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (38726471/10000000000000000000000 : ℝ)*base89 + (38726471/10000000000000000000000 : ℝ)*base91 + (38726471/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108577737244456555766121/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151080619/100000000000000 : ℝ)*(base1) + (481955689/100000000000000 : ℝ)*(base23) + (456617/2500000000000 : ℝ)*(base51) + (165732193/100000000000000 : ℝ)*(base59) + (645301884758077/100000000000000 : ℝ)*(major0) + (645301884758077/100000000000000 : ℝ)*(major1) + (645301884758077/100000000000000 : ℝ)*(major2) + (1195406147/100000000000000 : ℝ)*(sp1) + (805213123/100000000000000 : ℝ)*(sp2) + (628505319/50000000000000 : ℝ)*(sp3) + (217261889834273/25000000000000 : ℝ)*(sp4) + (434523106425163/50000000000000 : ℝ)*(sp5) + (869046121087661/100000000000000 : ℝ)*(sp6) + (421554916975837/100000000000000 : ℝ)*(sp7) + (84311265013419/20000000000000 : ℝ)*(f.failure) + (108630926032059/12500000000000 : ℝ)*(f.sum) + (204946890788707/100000000000000000000000000000 : ℝ)*base65 + (868781164188707/200000000000000000000000000000 : ℝ)*base67 + (498148477788707/200000000000000000000000000000 : ℝ)*base69 + (358875279588707/200000000000000000000000000000 : ℝ)*base71 + (10594022611293/100000000000000000000000000000 : ℝ)*base74 + (721819299611293/200000000000000000000000000000 : ℝ)*base76 + (238073235611293/200000000000000000000000000000 : ℝ)*base78 + (992553399611293/200000000000000000000000000000 : ℝ)*base80 + (83163889811293/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7122737/2000000000000000000000 : ℝ)*base90 + (7122737/2000000000000000000000 : ℝ)*base92 + (7122737/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1300_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (547/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3397/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1300_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1300_s1_0 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025129331/10000000000 : ℝ)*x 0 + (2830747289/5000000000 : ℝ)*x 1 + (1006467003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025129331/10000000000 : ℝ)^1065 ≤ (12217620810277/100000000000000 : ℝ)^809 := by
    have hnat : (2025129331 : ℕ)^1065*100000000000000^809 ≤ 12217620810277^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025129331 10000000000 12217620810277 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2830747289/5000000000 : ℝ)^1065 ≤ (4728774445967/10000000000000 : ℝ)^809 := by
    have hnat : (2830747289 : ℕ)^1065*10000000000000^809 ≤ 4728774445967^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830747289 5000000000 4728774445967 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006467003/2000000000 : ℝ)^1065 ≤ (40494634709881/100000000000000 : ℝ)^809 := by
    have hnat : (1006467003 : ℕ)^1065*100000000000000^809 ≤ 40494634709881^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006467003 2000000000 40494634709881 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025129331/10000000000 : ℝ), (2830747289/5000000000 : ℝ), (1006467003/2000000000 : ℝ)] ![(12217620810277/100000000000000 : ℝ), (4728774445967/10000000000000 : ℝ), (40494634709881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025129331/10000000000 : ℝ)|^1065 ≤ (12217620810277/100000000000000 : ℝ)^809
        have hw : |(-2025129331/10000000000 : ℝ)|=(2025129331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2830747289/5000000000 : ℝ)|^1065 ≤ (4728774445967/10000000000000 : ℝ)^809
        have hw : |(2830747289/5000000000 : ℝ)|=(2830747289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006467003/2000000000 : ℝ)|^1065 ≤ (40494634709881/100000000000000 : ℝ)^809
        have hw : |(1006467003/2000000000 : ℝ)|=(1006467003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s1_1 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (216405343/400000000 : ℝ)*x 0 + (-295263019/1250000000 : ℝ)*x 1 + (251616761/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216405343/400000000 : ℝ)^1065 ≤ (44543497096493/100000000000000 : ℝ)^809 := by
    have hnat : (216405343 : ℕ)^1065*100000000000000^809 ≤ 44543497096493^809*400000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216405343 400000000 44543497096493 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295263019/1250000000 : ℝ)^1065 ≤ (3740466502927/25000000000000 : ℝ)^809 := by
    have hnat : (295263019 : ℕ)^1065*25000000000000^809 ≤ 3740466502927^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295263019 1250000000 3740466502927 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251616761/500000000 : ℝ)^1065 ≤ (5061829610187/12500000000000 : ℝ)^809 := by
    have hnat : (251616761 : ℕ)^1065*12500000000000^809 ≤ 5061829610187^809*500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251616761 500000000 5061829610187 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216405343/400000000 : ℝ), (-295263019/1250000000 : ℝ), (251616761/500000000 : ℝ)] ![(44543497096493/100000000000000 : ℝ), (3740466502927/25000000000000 : ℝ), (5061829610187/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216405343/400000000 : ℝ)|^1065 ≤ (44543497096493/100000000000000 : ℝ)^809
        have hw : |(216405343/400000000 : ℝ)|=(216405343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-295263019/1250000000 : ℝ)|^1065 ≤ (3740466502927/25000000000000 : ℝ)^809
        have hw : |(-295263019/1250000000 : ℝ)|=(295263019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251616761/500000000 : ℝ)|^1065 ≤ (5061829610187/12500000000000 : ℝ)^809
        have hw : |(251616761/500000000 : ℝ)|=(251616761/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s1_2 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5410133743/10000000000 : ℝ)*x 0 + (2516167451/5000000000 : ℝ)*x 1 + (-2362104337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5410133743/10000000000 : ℝ)^1065 ≤ (11135874729349/25000000000000 : ℝ)^809 := by
    have hnat : (5410133743 : ℕ)^1065*25000000000000^809 ≤ 11135874729349^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410133743 10000000000 11135874729349 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516167451/5000000000 : ℝ)^1065 ≤ (10123658378211/25000000000000 : ℝ)^809 := by
    have hnat : (2516167451 : ℕ)^1065*25000000000000^809 ≤ 10123658378211^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516167451 5000000000 10123658378211 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2362104337/10000000000 : ℝ)^1065 ≤ (1496186755433/10000000000000 : ℝ)^809 := by
    have hnat : (2362104337 : ℕ)^1065*10000000000000^809 ≤ 1496186755433^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362104337 10000000000 1496186755433 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5410133743/10000000000 : ℝ), (2516167451/5000000000 : ℝ), (-2362104337/10000000000 : ℝ)] ![(11135874729349/25000000000000 : ℝ), (10123658378211/25000000000000 : ℝ), (1496186755433/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5410133743/10000000000 : ℝ)|^1065 ≤ (11135874729349/25000000000000 : ℝ)^809
        have hw : |(5410133743/10000000000 : ℝ)|=(5410133743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2516167451/5000000000 : ℝ)|^1065 ≤ (10123658378211/25000000000000 : ℝ)^809
        have hw : |(2516167451/5000000000 : ℝ)|=(2516167451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2362104337/10000000000 : ℝ)|^1065 ≤ (1496186755433/10000000000000 : ℝ)^809
        have hw : |(-2362104337/10000000000 : ℝ)|=(2362104337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s1_3 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4299739537/10000000000 : ℝ)*x 0 + (1848697303/5000000000 : ℝ)*x 1 + (2497210099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299739537/10000000000 : ℝ)^1065 ≤ (6583829254397/20000000000000 : ℝ)^809 := by
    have hnat : (4299739537 : ℕ)^1065*20000000000000^809 ≤ 6583829254397^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299739537 10000000000 6583829254397 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1848697303/5000000000 : ℝ)^1065 ≤ (13493690176989/50000000000000 : ℝ)^809 := by
    have hnat : (1848697303 : ℕ)^1065*50000000000000^809 ≤ 13493690176989^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848697303 5000000000 13493690176989 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2497210099/5000000000 : ℝ)^1065 ≤ (20046736681523/50000000000000 : ℝ)^809 := by
    have hnat : (2497210099 : ℕ)^1065*50000000000000^809 ≤ 20046736681523^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497210099 5000000000 20046736681523 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299739537/10000000000 : ℝ), (1848697303/5000000000 : ℝ), (2497210099/5000000000 : ℝ)] ![(6583829254397/20000000000000 : ℝ), (13493690176989/50000000000000 : ℝ), (20046736681523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299739537/10000000000 : ℝ)|^1065 ≤ (6583829254397/20000000000000 : ℝ)^809
        have hw : |(4299739537/10000000000 : ℝ)|=(4299739537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1848697303/5000000000 : ℝ)|^1065 ≤ (13493690176989/50000000000000 : ℝ)^809
        have hw : |(1848697303/5000000000 : ℝ)|=(1848697303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2497210099/5000000000 : ℝ)|^1065 ≤ (20046736681523/50000000000000 : ℝ)^809
        have hw : |(2497210099/5000000000 : ℝ)|=(2497210099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s1_4 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-405149833/2000000000 : ℝ)*x 0 + (5040487883/10000000000 : ℝ)*x 1 + (5653188369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405149833/2000000000 : ℝ)^1065 ≤ (3055635956971/25000000000000 : ℝ)^809 := by
    have hnat : (405149833 : ℕ)^1065*25000000000000^809 ≤ 3055635956971^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405149833 2000000000 3055635956971 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5040487883/10000000000 : ℝ)^1065 ≤ (40581022169981/100000000000000 : ℝ)^809 := by
    have hnat : (5040487883 : ℕ)^1065*100000000000000^809 ≤ 40581022169981^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5040487883 10000000000 40581022169981 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5653188369/10000000000 : ℝ)^1065 ≤ (1887857359523/4000000000000 : ℝ)^809 := by
    have hnat : (5653188369 : ℕ)^1065*4000000000000^809 ≤ 1887857359523^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5653188369 10000000000 1887857359523 4000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-405149833/2000000000 : ℝ), (5040487883/10000000000 : ℝ), (5653188369/10000000000 : ℝ)] ![(3055635956971/25000000000000 : ℝ), (40581022169981/100000000000000 : ℝ), (1887857359523/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-405149833/2000000000 : ℝ)|^1065 ≤ (3055635956971/25000000000000 : ℝ)^809
        have hw : |(-405149833/2000000000 : ℝ)|=(405149833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5040487883/10000000000 : ℝ)|^1065 ≤ (40581022169981/100000000000000 : ℝ)^809
        have hw : |(5040487883/10000000000 : ℝ)|=(5040487883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5653188369/10000000000 : ℝ)|^1065 ≤ (1887857359523/4000000000000 : ℝ)^809
        have hw : |(5653188369/10000000000 : ℝ)|=(5653188369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s1_5 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5247465053/10000000000 : ℝ)*x 0 + (-174125031/1000000000 : ℝ)*x 1 + (5653189119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247465053/10000000000 : ℝ)^1065 ≤ (42788826729001/100000000000000 : ℝ)^809 := by
    have hnat : (5247465053 : ℕ)^1065*100000000000000^809 ≤ 42788826729001^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247465053 10000000000 42788826729001 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174125031/1000000000 : ℝ)^1065 ≤ (1251841377973/12500000000000 : ℝ)^809 := by
    have hnat : (174125031 : ℕ)^1065*12500000000000^809 ≤ 1251841377973^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174125031 1000000000 1251841377973 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5653189119/10000000000 : ℝ)^1065 ≤ (23598221115469/50000000000000 : ℝ)^809 := by
    have hnat : (5653189119 : ℕ)^1065*50000000000000^809 ≤ 23598221115469^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5653189119 10000000000 23598221115469 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247465053/10000000000 : ℝ), (-174125031/1000000000 : ℝ), (5653189119/10000000000 : ℝ)] ![(42788826729001/100000000000000 : ℝ), (1251841377973/12500000000000 : ℝ), (23598221115469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247465053/10000000000 : ℝ)|^1065 ≤ (42788826729001/100000000000000 : ℝ)^809
        have hw : |(5247465053/10000000000 : ℝ)|=(5247465053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174125031/1000000000 : ℝ)|^1065 ≤ (1251841377973/12500000000000 : ℝ)^809
        have hw : |(-174125031/1000000000 : ℝ)|=(174125031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5653189119/10000000000 : ℝ)|^1065 ≤ (23598221115469/50000000000000 : ℝ)^809
        have hw : |(5653189119/10000000000 : ℝ)|=(5653189119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s1_6 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5247464969/10000000000 : ℝ)*x 0 + (1130637741/2000000000 : ℝ)*x 1 + (-174125103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247464969/10000000000 : ℝ)^1065 ≤ (42788825827303/100000000000000 : ℝ)^809 := by
    have hnat : (5247464969 : ℕ)^1065*100000000000000^809 ≤ 42788825827303^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247464969 10000000000 42788825827303 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130637741/2000000000 : ℝ)^1065 ≤ (23598218840439/50000000000000 : ℝ)^809 := by
    have hnat : (1130637741 : ℕ)^1065*50000000000000^809 ≤ 23598218840439^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130637741 2000000000 23598218840439 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174125103/1000000000 : ℝ)^1065 ≤ (1001473647523/10000000000000 : ℝ)^809 := by
    have hnat : (174125103 : ℕ)^1065*10000000000000^809 ≤ 1001473647523^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174125103 1000000000 1001473647523 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247464969/10000000000 : ℝ), (1130637741/2000000000 : ℝ), (-174125103/1000000000 : ℝ)] ![(42788825827303/100000000000000 : ℝ), (23598218840439/50000000000000 : ℝ), (1001473647523/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247464969/10000000000 : ℝ)|^1065 ≤ (42788825827303/100000000000000 : ℝ)^809
        have hw : |(5247464969/10000000000 : ℝ)|=(5247464969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130637741/2000000000 : ℝ)|^1065 ≤ (23598218840439/50000000000000 : ℝ)^809
        have hw : |(1130637741/2000000000 : ℝ)|=(1130637741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-174125103/1000000000 : ℝ)|^1065 ≤ (1001473647523/10000000000000 : ℝ)^809
        have hw : |(-174125103/1000000000 : ℝ)|=(174125103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s1_7 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4301016483/10000000000 : ℝ)*x 0 + (995522701/2000000000 : ℝ)*x 1 + (1857258587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301016483/10000000000 : ℝ)^1065 ≤ (32932016920743/100000000000000 : ℝ)^809 := by
    have hnat : (4301016483 : ℕ)^1065*100000000000000^809 ≤ 32932016920743^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301016483 10000000000 32932016920743 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995522701/2000000000 : ℝ)^1065 ≤ (997898903577/2500000000000 : ℝ)^809 := by
    have hnat : (995522701 : ℕ)^1065*2500000000000^809 ≤ 997898903577^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995522701 2000000000 997898903577 2500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1857258587/5000000000 : ℝ)^1065 ≤ (13576013459527/50000000000000 : ℝ)^809 := by
    have hnat : (1857258587 : ℕ)^1065*50000000000000^809 ≤ 13576013459527^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857258587 5000000000 13576013459527 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301016483/10000000000 : ℝ), (995522701/2000000000 : ℝ), (1857258587/5000000000 : ℝ)] ![(32932016920743/100000000000000 : ℝ), (997898903577/2500000000000 : ℝ), (13576013459527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301016483/10000000000 : ℝ)|^1065 ≤ (32932016920743/100000000000000 : ℝ)^809
        have hw : |(4301016483/10000000000 : ℝ)|=(4301016483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(995522701/2000000000 : ℝ)|^1065 ≤ (997898903577/2500000000000 : ℝ)^809
        have hw : |(995522701/2000000000 : ℝ)|=(995522701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1857258587/5000000000 : ℝ)|^1065 ≤ (13576013459527/50000000000000 : ℝ)^809
        have hw : |(1857258587/5000000000 : ℝ)|=(1857258587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1300_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3397/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (547/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (811/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9893/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3397/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (547/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3397/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (547/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3397/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (547/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3397/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (547/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3397/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (547/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3397/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (547/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (547/50000 : ℝ) ^ (4259/1024 : ℝ) ≤ (698104886789/100000000000000000000 : ℝ) := by
    have hpowers : (547/50000 : ℝ)^4259 ≤ (698104886789/100000000000000000000 : ℝ)^1024 := by
      have hnat : (547 : ℕ)^4259*100000000000000000000^1024 ≤ 698104886789^1024*50000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        547 50000 698104886789 100000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (547/50000 : ℝ)) (X := (698104886789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3397/12500 : ℝ) ^ (4259/1024 : ℝ) ≤ (443277783468378859/100000000000000000000 : ℝ) := by
    have hpowers : (3397/12500 : ℝ)^4259 ≤ (443277783468378859/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3397 : ℕ)^4259*100000000000000000000^1024 ≤ 443277783468378859^1024*12500^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3397 12500 443277783468378859 100000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3397/12500 : ℝ)) (X := (443277783468378859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000698104886789/50000000000000000000 : ℝ) ≤ (2000000006713871/2000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (50000000698104886789/50000000000000000000 : ℝ)^1024 ≤ (2000000006713871/2000000000000000 : ℝ)^4259 := by
      have hnat : (50000000698104886789 : ℕ)^1024*2000000000000000^4259 ≤ 2000000006713871^4259*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000698104886789 50000000000000000000 2000000006713871 2000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000006713871/2000000000000000 : ℝ)) (X := (50000000698104886789/50000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6277704905098329103/6250000000000000000 : ℝ) ≤ (5005319969194667/5000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (6277704905098329103/6250000000000000000 : ℝ)^1024 ≤ (5005319969194667/5000000000000000 : ℝ)^4259 := by
      have hnat : (6277704905098329103 : ℕ)^1024*5000000000000000^4259 ≤ 5005319969194667^4259*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6277704905098329103 6250000000000000000 5005319969194667 5000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005319969194667/5000000000000000 : ℝ)) (X := (6277704905098329103/6250000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50443277783468378859/50000000000000000000 : ℝ) ≤ (10021279843209313/10000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (50443277783468378859/50000000000000000000 : ℝ)^1024 ≤ (10021279843209313/10000000000000000 : ℝ)^4259 := by
      have hnat : (50443277783468378859 : ℕ)^1024*10000000000000000^4259 ≤ 10021279843209313^4259*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50443277783468378859 50000000000000000000 10021279843209313 10000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10021279843209313/10000000000000000 : ℝ)) (X := (50443277783468378859/50000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(698104886789/100000000000000000000 : ℝ) ≤ ((43466120127301633843/43470000000000000000 : ℝ)+2*(3546634939993/869400000000000 : ℝ)*(547/50000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (43466120127301633843/43470000000000000000 : ℝ)+2*(3546634939993/869400000000000 : ℝ)*(547/50000 : ℝ)=(2000000006713871/2000000000000000 : ℝ) by norm_num, show 1+2*(698104886789/100000000000000000000 : ℝ)=(50000000698104886789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(443277783468378859/100000000000000000000 : ℝ)+(698104886789/100000000000000000000 : ℝ) ≤ ((43466120127301633843/43470000000000000000 : ℝ)+(3546634939993/869400000000000 : ℝ)*((3397/12500 : ℝ)+(547/50000 : ℝ)))^(4259/1024 : ℝ) := by
    rw [show (43466120127301633843/43470000000000000000 : ℝ)+(3546634939993/869400000000000 : ℝ)*((3397/12500 : ℝ)+(547/50000 : ℝ))=(5005319969194667/5000000000000000 : ℝ) by norm_num, show 1+(443277783468378859/100000000000000000000 : ℝ)+(698104886789/100000000000000000000 : ℝ)=(6277704905098329103/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(443277783468378859/100000000000000000000 : ℝ) ≤ ((43466120127301633843/43470000000000000000 : ℝ)+2*(3546634939993/869400000000000 : ℝ)*(3397/12500 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (43466120127301633843/43470000000000000000 : ℝ)+2*(3546634939993/869400000000000 : ℝ)*(3397/12500 : ℝ)=(10021279843209313/10000000000000000 : ℝ) by norm_num, show 1+2*(443277783468378859/100000000000000000000 : ℝ)=(50443277783468378859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43466120127301633843/43470000000000000000 : ℝ)*(X 1 0+X 2 0)+(3546634939993/869400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (547/50000 : ℝ)) (hi := (3397/12500 : ℝ)) (c := (43466120127301633843/43470000000000000000 : ℝ)) (alpha := (3546634939993/869400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43466120127301633843/43470000000000000000 : ℝ)*(X 0 1+X 2 1)+(3546634939993/869400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (547/50000 : ℝ)) (hi := (3397/12500 : ℝ)) (c := (43466120127301633843/43470000000000000000 : ℝ)) (alpha := (3546634939993/869400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43466120127301633843/43470000000000000000 : ℝ)*(X 0 2+X 1 2)+(3546634939993/869400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (547/50000 : ℝ)) (hi := (3397/12500 : ℝ)) (c := (43466120127301633843/43470000000000000000 : ℝ)) (alpha := (3546634939993/869400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2025129331/10000000000 : ℝ)*X 0 0+(2830747289/5000000000 : ℝ)*X 0 1+(1006467003/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((216405343/400000000 : ℝ)*X 1 0+(-295263019/1250000000 : ℝ)*X 1 1+(251616761/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5410133743/10000000000 : ℝ)*X 2 0+(2516167451/5000000000 : ℝ)*X 2 1+(-2362104337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4299739537/10000000000 : ℝ)*X 0 0+(1848697303/5000000000 : ℝ)*X 0 1+(2497210099/5000000000 : ℝ)*X 0 2+(4299739537/10000000000 : ℝ)*X 1 0+(1848697303/5000000000 : ℝ)*X 1 1+(2497210099/5000000000 : ℝ)*X 1 2+(4299739537/10000000000 : ℝ)*X 2 0+(1848697303/5000000000 : ℝ)*X 2 1+(2497210099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-405149833/2000000000 : ℝ)*X 0 0+(5040487883/10000000000 : ℝ)*X 0 1+(5653188369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5247465053/10000000000 : ℝ)*X 1 0+(-174125031/1000000000 : ℝ)*X 1 1+(5653189119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5247464969/10000000000 : ℝ)*X 2 0+(1130637741/2000000000 : ℝ)*X 2 1+(-174125103/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4301016483/10000000000 : ℝ)*X 0 0+(995522701/2000000000 : ℝ)*X 0 1+(1857258587/5000000000 : ℝ)*X 0 2+(4301016483/10000000000 : ℝ)*X 1 0+(995522701/2000000000 : ℝ)*X 1 1+(1857258587/5000000000 : ℝ)*X 1 2+(4301016483/10000000000 : ℝ)*X 2 0+(995522701/2000000000 : ℝ)*X 2 1+(1857258587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91154922482818662265097327/16100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51794363/100000000000000 : ℝ)*(base1) + (501309123/50000000000000 : ℝ)*(base19) + (525987317/50000000000000 : ℝ)*(base23) + (31077233/20000000000000 : ℝ)*(upper3) + (23820121/25000000000000 : ℝ)*(upper5) + (236043398678433/20000000000000 : ℝ)*(major0) + (236043398678433/20000000000000 : ℝ)*(major1) + (236043398678433/20000000000000 : ℝ)*(major2) + (158942793808311/10000000000000 : ℝ)*(sp0) + (1589432508182257/100000000000000 : ℝ)*(sp1) + (1589432458825869/100000000000000 : ℝ)*(sp2) + (770997321371169/100000000000000 : ℝ)*(sp3) + (1406127939/25000000000000 : ℝ)*(sp4) + (2914091741/100000000000000 : ℝ)*(sp7) + (771000287257273/100000000000000 : ℝ)*(f.failure) + (1589433510800503/100000000000000 : ℝ)*(f.sum) + (2237777561587/579600000000000000000000000 : ℝ)*base65 + (126321788724950297/32200000000000000000000000000000 : ℝ)*base67 + (28959058856350297/32200000000000000000000000000000 : ℝ)*base69 + (134280093300150297/32200000000000000000000000000000 : ℝ)*base71 + (10688539271933/2898000000000000000000000000 : ℝ)*base73 + (243922107439150297/32200000000000000000000000000000 : ℝ)*base75 + (94892444977750297/32200000000000000000000000000000 : ℝ)*base77 + (202901448062950297/32200000000000000000000000000000 : ℝ)*base79 + (3127100890709/2898000000000000000000000000 : ℝ)*base81 + (59441979/10000000000000000000000 : ℝ)*base90 + (59441979/10000000000000000000000 : ℝ)*base92 + (59441979/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1141454435332190275915765469/181125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (141442217/12500000000000 : ℝ)*(base19) + (112814057/10000000000000 : ℝ)*(base23) + (3077873/10000000000000 : ℝ)*(upper2) + (101113249/50000000000000 : ℝ)*(upper3) + (131354059/100000000000000 : ℝ)*(upper5) + (302977910479417/25000000000000 : ℝ)*(major0) + (302977910479417/25000000000000 : ℝ)*(major1) + (302977910479417/25000000000000 : ℝ)*(major2) + (1659168041/25000000000000 : ℝ)*(sp1) + (684720861/12500000000000 : ℝ)*(sp2) + (1632117625294839/100000000000000 : ℝ)*(sp4) + (816054928542469/50000000000000 : ℝ)*(sp5) + (1632111019387381/100000000000000 : ℝ)*(sp6) + (791705448472963/100000000000000 : ℝ)*(sp7) + (791705448472963/100000000000000 : ℝ)*(f.failure) + (1632117625294839/100000000000000 : ℝ)*(f.sum) + (2203388484433/1358437500000000000000000000 : ℝ)*base66 + (640691086643351059/120750000000000000000000000000000 : ℝ)*base67 + (748536818227398941/120750000000000000000000000000000 : ℝ)*base70 + (224160823230101059/120750000000000000000000000000000 : ℝ)*base71 + (48201230940017/21735000000000000000000000000 : ℝ)*base73 + (818716299869351059/120750000000000000000000000000000 : ℝ)*base75 + (59568918180851059/120750000000000000000000000000000 : ℝ)*base77 + (990535243194648941/120750000000000000000000000000000 : ℝ)*base80 + (68957909495849/10867500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (16606151/10000000000000000000000 : ℝ)*base89 + (16606151/10000000000000000000000 : ℝ)*base91 + (16606151/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1300_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3397/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (547/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (811/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9893/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1300_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1300_s2_0 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2069068507/10000000000 : ℝ)*x 0 + (5491815557/10000000000 : ℝ)*x 1 + (5173936179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069068507/10000000000 : ℝ)^1065 ≤ (502711277383/4000000000000 : ℝ)^809 := by
    have hnat : (2069068507 : ℕ)^1065*4000000000000^809 ≤ 502711277383^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069068507 10000000000 502711277383 4000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491815557/10000000000 : ℝ)^1065 ≤ (45430931667851/100000000000000 : ℝ)^809 := by
    have hnat : (5491815557 : ℕ)^1065*100000000000000^809 ≤ 45430931667851^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491815557 10000000000 45430931667851 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5173936179/10000000000 : ℝ)^1065 ≤ (21000643187327/50000000000000 : ℝ)^809 := by
    have hnat : (5173936179 : ℕ)^1065*50000000000000^809 ≤ 21000643187327^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173936179 10000000000 21000643187327 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2069068507/10000000000 : ℝ), (5491815557/10000000000 : ℝ), (5173936179/10000000000 : ℝ)] ![(502711277383/4000000000000 : ℝ), (45430931667851/100000000000000 : ℝ), (21000643187327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2069068507/10000000000 : ℝ)|^1065 ≤ (502711277383/4000000000000 : ℝ)^809
        have hw : |(-2069068507/10000000000 : ℝ)|=(2069068507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491815557/10000000000 : ℝ)|^1065 ≤ (45430931667851/100000000000000 : ℝ)^809
        have hw : |(5491815557/10000000000 : ℝ)|=(5491815557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5173936179/10000000000 : ℝ)|^1065 ≤ (21000643187327/50000000000000 : ℝ)^809
        have hw : |(5173936179/10000000000 : ℝ)|=(5173936179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s2_1 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (671123437/1250000000 : ℝ)*x 0 + (-558429773/2500000000 : ℝ)*x 1 + (1034787213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671123437/1250000000 : ℝ)^1065 ≤ (8819612890051/20000000000000 : ℝ)^809 := by
    have hnat : (671123437 : ℕ)^1065*20000000000000^809 ≤ 8819612890051^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671123437 1250000000 8819612890051 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (558429773/2500000000 : ℝ)^1065 ≤ (278013007583/2000000000000 : ℝ)^809 := by
    have hnat : (558429773 : ℕ)^1065*2000000000000^809 ≤ 278013007583^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558429773 2500000000 278013007583 2000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034787213/2000000000 : ℝ)^1065 ≤ (42001285156373/100000000000000 : ℝ)^809 := by
    have hnat : (1034787213 : ℕ)^1065*100000000000000^809 ≤ 42001285156373^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034787213 2000000000 42001285156373 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671123437/1250000000 : ℝ), (-558429773/2500000000 : ℝ), (1034787213/2000000000 : ℝ)] ![(8819612890051/20000000000000 : ℝ), (278013007583/2000000000000 : ℝ), (42001285156373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671123437/1250000000 : ℝ)|^1065 ≤ (8819612890051/20000000000000 : ℝ)^809
        have hw : |(671123437/1250000000 : ℝ)|=(671123437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-558429773/2500000000 : ℝ)|^1065 ≤ (278013007583/2000000000000 : ℝ)^809
        have hw : |(-558429773/2500000000 : ℝ)|=(558429773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034787213/2000000000 : ℝ)|^1065 ≤ (42001285156373/100000000000000 : ℝ)^809
        have hw : |(1034787213/2000000000 : ℝ)|=(1034787213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s2_2 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5368987273/10000000000 : ℝ)*x 0 + (5173936203/10000000000 : ℝ)*x 1 + (-1116859603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368987273/10000000000 : ℝ)^1065 ≤ (2756128877441/6250000000000 : ℝ)^809 := by
    have hnat : (5368987273 : ℕ)^1065*6250000000000^809 ≤ 2756128877441^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368987273 10000000000 2756128877441 6250000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5173936203/10000000000 : ℝ)^1065 ≤ (21000643315567/50000000000000 : ℝ)^809 := by
    have hnat : (5173936203 : ℕ)^1065*50000000000000^809 ≤ 21000643315567^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173936203 10000000000 21000643315567 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116859603/5000000000 : ℝ)^1065 ≤ (3475162828269/25000000000000 : ℝ)^809 := by
    have hnat : (1116859603 : ℕ)^1065*25000000000000^809 ≤ 3475162828269^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116859603 5000000000 3475162828269 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368987273/10000000000 : ℝ), (5173936203/10000000000 : ℝ), (-1116859603/5000000000 : ℝ)] ![(2756128877441/6250000000000 : ℝ), (21000643315567/50000000000000 : ℝ), (3475162828269/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368987273/10000000000 : ℝ)|^1065 ≤ (2756128877441/6250000000000 : ℝ)^809
        have hw : |(5368987273/10000000000 : ℝ)|=(5368987273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5173936203/10000000000 : ℝ)|^1065 ≤ (21000643315567/50000000000000 : ℝ)^809
        have hw : |(5173936203/10000000000 : ℝ)|=(5173936203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1116859603/5000000000 : ℝ)|^1065 ≤ (3475162828269/25000000000000 : ℝ)^809
        have hw : |(-1116859603/5000000000 : ℝ)|=(1116859603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s2_3 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2165157613/5000000000 : ℝ)*x 0 + (4014423233/10000000000 : ℝ)*x 1 + (4669746277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165157613/5000000000 : ℝ)^1065 ≤ (33227657745709/100000000000000 : ℝ)^809 := by
    have hnat : (2165157613 : ℕ)^1065*100000000000000^809 ≤ 33227657745709^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165157613 5000000000 33227657745709 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4014423233/10000000000 : ℝ)^1065 ≤ (30074169958957/100000000000000 : ℝ)^809 := by
    have hnat : (4014423233 : ℕ)^1065*100000000000000^809 ≤ 30074169958957^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014423233 10000000000 30074169958957 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4669746277/10000000000 : ℝ)^1065 ≤ (36698172279661/100000000000000 : ℝ)^809 := by
    have hnat : (4669746277 : ℕ)^1065*100000000000000^809 ≤ 36698172279661^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669746277 10000000000 36698172279661 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165157613/5000000000 : ℝ), (4014423233/10000000000 : ℝ), (4669746277/10000000000 : ℝ)] ![(33227657745709/100000000000000 : ℝ), (30074169958957/100000000000000 : ℝ), (36698172279661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165157613/5000000000 : ℝ)|^1065 ≤ (33227657745709/100000000000000 : ℝ)^809
        have hw : |(2165157613/5000000000 : ℝ)|=(2165157613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4014423233/10000000000 : ℝ)|^1065 ≤ (30074169958957/100000000000000 : ℝ)^809
        have hw : |(4014423233/10000000000 : ℝ)|=(4014423233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4669746277/10000000000 : ℝ)|^1065 ≤ (36698172279661/100000000000000 : ℝ)^809
        have hw : |(4669746277/10000000000 : ℝ)|=(4669746277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s2_4 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2069147803/10000000000 : ℝ)*x 0 + (5176026647/10000000000 : ℝ)*x 1 + (5489705679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069147803/10000000000 : ℝ)^1065 ≤ (12568416006853/100000000000000 : ℝ)^809 := by
    have hnat : (2069147803 : ℕ)^1065*100000000000000^809 ≤ 12568416006853^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069147803 10000000000 12568416006853 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176026647/10000000000 : ℝ)^1065 ≤ (42023627955217/100000000000000 : ℝ)^809 := by
    have hnat : (5176026647 : ℕ)^1065*100000000000000^809 ≤ 42023627955217^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176026647 10000000000 42023627955217 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489705679/10000000000 : ℝ)^1065 ≤ (5675994502753/12500000000000 : ℝ)^809 := by
    have hnat : (5489705679 : ℕ)^1065*12500000000000^809 ≤ 5675994502753^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489705679 10000000000 5675994502753 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2069147803/10000000000 : ℝ), (5176026647/10000000000 : ℝ), (5489705679/10000000000 : ℝ)] ![(12568416006853/100000000000000 : ℝ), (42023627955217/100000000000000 : ℝ), (5675994502753/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2069147803/10000000000 : ℝ)|^1065 ≤ (12568416006853/100000000000000 : ℝ)^809
        have hw : |(-2069147803/10000000000 : ℝ)|=(2069147803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176026647/10000000000 : ℝ)|^1065 ≤ (42023627955217/100000000000000 : ℝ)^809
        have hw : |(5176026647/10000000000 : ℝ)|=(5176026647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489705679/10000000000 : ℝ)|^1065 ≤ (5675994502753/12500000000000 : ℝ)^809
        have hw : |(5489705679/10000000000 : ℝ)|=(5489705679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s2_5 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5287438919/10000000000 : ℝ)*x 0 + (-958974461/5000000000 : ℝ)*x 1 + (5489705799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287438919/10000000000 : ℝ)^1065 ≤ (2160922128603/5000000000000 : ℝ)^809 := by
    have hnat : (5287438919 : ℕ)^1065*5000000000000^809 ≤ 2160922128603^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287438919 10000000000 2160922128603 5000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958974461/5000000000 : ℝ)^1065 ≤ (1137360008313/10000000000000 : ℝ)^809 := by
    have hnat : (958974461 : ℕ)^1065*10000000000000^809 ≤ 1137360008313^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958974461 5000000000 1137360008313 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489705799/10000000000 : ℝ)^1065 ≤ (45407957328691/100000000000000 : ℝ)^809 := by
    have hnat : (5489705799 : ℕ)^1065*100000000000000^809 ≤ 45407957328691^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489705799 10000000000 45407957328691 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287438919/10000000000 : ℝ), (-958974461/5000000000 : ℝ), (5489705799/10000000000 : ℝ)] ![(2160922128603/5000000000000 : ℝ), (1137360008313/10000000000000 : ℝ), (45407957328691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287438919/10000000000 : ℝ)|^1065 ≤ (2160922128603/5000000000000 : ℝ)^809
        have hw : |(5287438919/10000000000 : ℝ)|=(5287438919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-958974461/5000000000 : ℝ)|^1065 ≤ (1137360008313/10000000000000 : ℝ)^809
        have hw : |(-958974461/5000000000 : ℝ)|=(958974461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489705799/10000000000 : ℝ)|^1065 ≤ (45407957328691/100000000000000 : ℝ)^809
        have hw : |(5489705799/10000000000 : ℝ)|=(5489705799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s2_6 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5287439067/10000000000 : ℝ)*x 0 + (5489705687/10000000000 : ℝ)*x 1 + (-15343591/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287439067/10000000000 : ℝ)^1065 ≤ (21609222082293/50000000000000 : ℝ)^809 := by
    have hnat : (5287439067 : ℕ)^1065*50000000000000^809 ≤ 21609222082293^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287439067 10000000000 21609222082293 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489705687/10000000000 : ℝ)^1065 ≤ (9081591221827/20000000000000 : ℝ)^809 := by
    have hnat : (5489705687 : ℕ)^1065*20000000000000^809 ≤ 9081591221827^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489705687 10000000000 9081591221827 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15343591/80000000 : ℝ)^1065 ≤ (568679985811/5000000000000 : ℝ)^809 := by
    have hnat : (15343591 : ℕ)^1065*5000000000000^809 ≤ 568679985811^809*80000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15343591 80000000 568679985811 5000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287439067/10000000000 : ℝ), (5489705687/10000000000 : ℝ), (-15343591/80000000 : ℝ)] ![(21609222082293/50000000000000 : ℝ), (9081591221827/20000000000000 : ℝ), (568679985811/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287439067/10000000000 : ℝ)|^1065 ≤ (21609222082293/50000000000000 : ℝ)^809
        have hw : |(5287439067/10000000000 : ℝ)|=(5287439067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489705687/10000000000 : ℝ)|^1065 ≤ (9081591221827/20000000000000 : ℝ)^809
        have hw : |(5489705687/10000000000 : ℝ)|=(5489705687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15343591/80000000 : ℝ)|^1065 ≤ (568679985811/5000000000000 : ℝ)^809
        have hw : |(-15343591/80000000 : ℝ)|=(15343591/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s2_7 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2165238967/5000000000 : ℝ)*x 0 + (291589679/625000000 : ℝ)*x 1 + (803755579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165238967/5000000000 : ℝ)^1065 ≤ (33229301333063/100000000000000 : ℝ)^809 := by
    have hnat : (2165238967 : ℕ)^1065*100000000000000^809 ≤ 33229301333063^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165238967 5000000000 33229301333063 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291589679/625000000 : ℝ)^1065 ≤ (18326787498157/50000000000000 : ℝ)^809 := by
    have hnat : (291589679 : ℕ)^1065*50000000000000^809 ≤ 18326787498157^809*625000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291589679 625000000 18326787498157 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803755579/2000000000 : ℝ)^1065 ≤ (6023424731071/20000000000000 : ℝ)^809 := by
    have hnat : (803755579 : ℕ)^1065*20000000000000^809 ≤ 6023424731071^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803755579 2000000000 6023424731071 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165238967/5000000000 : ℝ), (291589679/625000000 : ℝ), (803755579/2000000000 : ℝ)] ![(33229301333063/100000000000000 : ℝ), (18326787498157/50000000000000 : ℝ), (6023424731071/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165238967/5000000000 : ℝ)|^1065 ≤ (33229301333063/100000000000000 : ℝ)^809
        have hw : |(2165238967/5000000000 : ℝ)|=(2165238967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(291589679/625000000 : ℝ)|^1065 ≤ (18326787498157/50000000000000 : ℝ)^809
        have hw : |(291589679/625000000 : ℝ)|=(291589679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(803755579/2000000000 : ℝ)|^1065 ≤ (6023424731071/20000000000000 : ℝ)^809
        have hw : |(803755579/2000000000 : ℝ)|=(803755579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1300_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9893/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (811/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9563/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16281/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9893/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (811/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9893/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (811/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9893/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (811/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9893/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (811/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9893/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (811/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9893/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (811/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (811/12500 : ℝ) ^ (4259/1024 : ℝ) ≤ (286612777898219/25000000000000000000 : ℝ) := by
    have hpowers : (811/12500 : ℝ)^4259 ≤ (286612777898219/25000000000000000000 : ℝ)^1024 := by
      have hnat : (811 : ℕ)^4259*25000000000000000000^1024 ≤ 286612777898219^1024*12500^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        811 12500 286612777898219 25000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (811/12500 : ℝ)) (X := (286612777898219/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9893/50000 : ℝ) ^ (4259/1024 : ℝ) ≤ (118420395185037919/100000000000000000000 : ℝ) := by
    have hpowers : (9893/50000 : ℝ)^4259 ≤ (118420395185037919/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9893 : ℕ)^4259*100000000000000000000^1024 ≤ 118420395185037919^1024*50000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9893 50000 118420395185037919 100000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9893/50000 : ℝ)) (X := (118420395185037919/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500286612777898219/12500000000000000000 : ℝ) ≤ (39062715344659/39062500000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (12500286612777898219/12500000000000000000 : ℝ)^1024 ≤ (39062715344659/39062500000000 : ℝ)^4259 := by
      have hnat : (12500286612777898219 : ℕ)^1024*39062500000000^4259 ≤ 39062715344659^4259*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500286612777898219 12500000000000000000 39062715344659 39062500000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39062715344659/39062500000000 : ℝ)) (X := (12500286612777898219/12500000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20023913369259326159/20000000000000000000 : ℝ) ≤ (2500718366351817/2500000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (20023913369259326159/20000000000000000000 : ℝ)^1024 ≤ (2500718366351817/2500000000000000 : ℝ)^4259 := by
      have hnat : (20023913369259326159 : ℕ)^1024*2500000000000000^4259 ≤ 2500718366351817^4259*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20023913369259326159 20000000000000000000 2500718366351817 2500000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500718366351817/2500000000000000 : ℝ)) (X := (20023913369259326159/20000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50118420395185037919/50000000000000000000 : ℝ) ≤ (1250711475322729/1250000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (50118420395185037919/50000000000000000000 : ℝ)^1024 ≤ (1250711475322729/1250000000000000 : ℝ)^4259 := by
      have hnat : (50118420395185037919 : ℕ)^1024*1250000000000000^4259 ≤ 1250711475322729^4259*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50118420395185037919 50000000000000000000 1250711475322729 1250000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250711475322729/1250000000000000 : ℝ)) (X := (50118420395185037919/50000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(286612777898219/25000000000000000000 : ℝ) ≤ ((2077252536750958677/2077812500000000000 : ℝ)+2*(704584293641/332450000000000 : ℝ)*(811/12500 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (2077252536750958677/2077812500000000000 : ℝ)+2*(704584293641/332450000000000 : ℝ)*(811/12500 : ℝ)=(39062715344659/39062500000000 : ℝ) by norm_num, show 1+2*(286612777898219/25000000000000000000 : ℝ)=(12500286612777898219/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(118420395185037919/100000000000000000000 : ℝ)+(286612777898219/25000000000000000000 : ℝ) ≤ ((2077252536750958677/2077812500000000000 : ℝ)+(704584293641/332450000000000 : ℝ)*((9893/50000 : ℝ)+(811/12500 : ℝ)))^(4259/1024 : ℝ) := by
    rw [show (2077252536750958677/2077812500000000000 : ℝ)+(704584293641/332450000000000 : ℝ)*((9893/50000 : ℝ)+(811/12500 : ℝ))=(2500718366351817/2500000000000000 : ℝ) by norm_num, show 1+(118420395185037919/100000000000000000000 : ℝ)+(286612777898219/25000000000000000000 : ℝ)=(20023913369259326159/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(118420395185037919/100000000000000000000 : ℝ) ≤ ((2077252536750958677/2077812500000000000 : ℝ)+2*(704584293641/332450000000000 : ℝ)*(9893/50000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (2077252536750958677/2077812500000000000 : ℝ)+2*(704584293641/332450000000000 : ℝ)*(9893/50000 : ℝ)=(1250711475322729/1250000000000000 : ℝ) by norm_num, show 1+2*(118420395185037919/100000000000000000000 : ℝ)=(50118420395185037919/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2077252536750958677/2077812500000000000 : ℝ)*(X 1 0+X 2 0)+(704584293641/332450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (811/12500 : ℝ)) (hi := (9893/50000 : ℝ)) (c := (2077252536750958677/2077812500000000000 : ℝ)) (alpha := (704584293641/332450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2077252536750958677/2077812500000000000 : ℝ)*(X 0 1+X 2 1)+(704584293641/332450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (811/12500 : ℝ)) (hi := (9893/50000 : ℝ)) (c := (2077252536750958677/2077812500000000000 : ℝ)) (alpha := (704584293641/332450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2077252536750958677/2077812500000000000 : ℝ)*(X 0 2+X 1 2)+(704584293641/332450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (811/12500 : ℝ)) (hi := (9893/50000 : ℝ)) (c := (2077252536750958677/2077812500000000000 : ℝ)) (alpha := (704584293641/332450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2069068507/10000000000 : ℝ)*X 0 0+(5491815557/10000000000 : ℝ)*X 0 1+(5173936179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((671123437/1250000000 : ℝ)*X 1 0+(-558429773/2500000000 : ℝ)*X 1 1+(1034787213/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368987273/10000000000 : ℝ)*X 2 0+(5173936203/10000000000 : ℝ)*X 2 1+(-1116859603/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2165157613/5000000000 : ℝ)*X 0 0+(4014423233/10000000000 : ℝ)*X 0 1+(4669746277/10000000000 : ℝ)*X 0 2+(2165157613/5000000000 : ℝ)*X 1 0+(4014423233/10000000000 : ℝ)*X 1 1+(4669746277/10000000000 : ℝ)*X 1 2+(2165157613/5000000000 : ℝ)*X 2 0+(4014423233/10000000000 : ℝ)*X 2 1+(4669746277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2069147803/10000000000 : ℝ)*X 0 0+(5176026647/10000000000 : ℝ)*X 0 1+(5489705679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287438919/10000000000 : ℝ)*X 1 0+(-958974461/5000000000 : ℝ)*X 1 1+(5489705799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287439067/10000000000 : ℝ)*X 2 0+(5489705687/10000000000 : ℝ)*X 2 1+(-15343591/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2165238967/5000000000 : ℝ)*X 0 0+(291589679/625000000 : ℝ)*X 0 1+(803755579/2000000000 : ℝ)*X 0 2+(2165238967/5000000000 : ℝ)*X 1 0+(291589679/625000000 : ℝ)*X 1 1+(803755579/2000000000 : ℝ)*X 1 2+(2165238967/5000000000 : ℝ)*X 2 0+(291589679/625000000 : ℝ)*X 2 1+(803755579/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (381836502158605729452637359/103890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (422430721/25000000000000 : ℝ)*(base19) + (9849237/800000000000 : ℝ)*(base23) + (176051919/100000000000000 : ℝ)*(lower2) + (28416501/5000000000000 : ℝ)*(upper3) + (94193861/50000000000000 : ℝ)*(upper5) + (583982496646359/25000000000000 : ℝ)*(major0) + (583982496646359/25000000000000 : ℝ)*(major1) + (583982496646359/25000000000000 : ℝ)*(major2) + (314586031204339/10000000000000 : ℝ)*(sp0) + (3145865313218861/100000000000000 : ℝ)*(sp1) + (39323322147339/1250000000000 : ℝ)*(sp2) + (190747119128261/12500000000000 : ℝ)*(sp3) + (1338179671/20000000000000 : ℝ)*(sp4) + (3178938139/20000000000000 : ℝ)*(sp7) + (1525992847716783/100000000000000 : ℝ)*(f.failure) + (629173400588349/20000000000000 : ℝ)*(f.sum) + (132522554146317/33245000000000000000000000000 : ℝ)*base65 + (249138598899329711/103890625000000000000000000000000 : ℝ)*base67 + (164123091053625793/51945312500000000000000000000000 : ℝ)*base69 + (43372521759730667/12986328125000000000000000000000 : ℝ)*base71 + (9872922337453/8311250000000000000000000000 : ℝ)*base73 + (26297859646585541/25972656250000000000000000000000 : ℝ)*base76 + (76716074971763771/6493164062500000000000000000000 : ℝ)*base77 + (117891755142561707/51945312500000000000000000000000 : ℝ)*base80 + (43443326055107/33245000000000000000000000000 : ℝ)*base81 + (51299709/10000000000000000000000 : ℝ)*base90 + (51299709/10000000000000000000000 : ℝ)*base92 + (51299709/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (619495195752528237212733657/103890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1155033849/100000000000000 : ℝ)*(base19) + (181283343/12500000000000 : ℝ)*(base23) + (45814881/25000000000000 : ℝ)*(upper3) + (37869369/50000000000000 : ℝ)*(lower4) + (67532341/100000000000000 : ℝ)*(upper5) + (295899090278133/12500000000000 : ℝ)*(major0) + (295899090278133/12500000000000 : ℝ)*(major1) + (295899090278133/12500000000000 : ℝ)*(major2) + (11905838809/100000000000000 : ℝ)*(sp1) + (15974888213/100000000000000 : ℝ)*(sp2) + (79699234811463/2500000000000 : ℝ)*(sp4) + (1593978165792931/50000000000000 : ℝ)*(sp5) + (1593975983651781/50000000000000 : ℝ)*(sp6) + (193301981653301/12500000000000 : ℝ)*(sp7) + (193301981653301/12500000000000 : ℝ)*(f.failure) + (79699234811463/2500000000000 : ℝ)*(f.sum) + (7714818373799/4155625000000000000000000000 : ℝ)*base66 + (259558659271885041/25972656250000000000000000000000 : ℝ)*base67 + (96348687592541291/25972656250000000000000000000000 : ℝ)*base69 + (194609467905191957/51945312500000000000000000000000 : ℝ)*base71 + (4096647269/4058227539062500000000000 : ℝ)*base73 + (75217347140881711/103890625000000000000000000000000 : ℝ)*base76 + (1124736057274618289/103890625000000000000000000000000 : ℝ)*base77 + (1440992628672587039/103890625000000000000000000000000 : ℝ)*base79 + (41815279176323/8311250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8819823/1250000000000000000000 : ℝ)*base90 + (8819823/1250000000000000000000 : ℝ)*base92 + (8819823/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1300_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9893/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (811/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9563/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1300_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1300_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9563/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1300_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1300_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1300_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9563/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1300_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
