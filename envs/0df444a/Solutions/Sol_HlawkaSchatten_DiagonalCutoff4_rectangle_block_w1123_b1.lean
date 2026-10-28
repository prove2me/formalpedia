-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1123_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:10:22.405712+00:00
-- url     : https://prove2.me/submissions/d878955c-3264-4c07-817e-6f9216f7527b

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
theorem support_rectangle_w1123_s3_0 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-542997041/2500000000 : ℝ)*x 0 + (543117531/1000000000 : ℝ)*x 1 + (5230256669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542997041/2500000000 : ℝ)^2079 ≤ (2637624226933/20000000000000 : ℝ)^1567 := by
    have hnat : (542997041 : ℕ)^2079*20000000000000^1567 ≤ 2637624226933^1567*2500000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542997041 2500000000 2637624226933 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543117531/1000000000 : ℝ)^2079 ≤ (22245557810527/50000000000000 : ℝ)^1567 := by
    have hnat : (543117531 : ℕ)^2079*50000000000000^1567 ≤ 22245557810527^1567*1000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543117531 1000000000 22245557810527 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230256669/10000000000 : ℝ)^2079 ≤ (42320763231857/100000000000000 : ℝ)^1567 := by
    have hnat : (5230256669 : ℕ)^2079*100000000000000^1567 ≤ 42320763231857^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230256669 10000000000 42320763231857 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542997041/2500000000 : ℝ), (543117531/1000000000 : ℝ), (5230256669/10000000000 : ℝ)] ![(2637624226933/20000000000000 : ℝ), (22245557810527/50000000000000 : ℝ), (42320763231857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542997041/2500000000 : ℝ)|^2079 ≤ (2637624226933/20000000000000 : ℝ)^1567
        have hw : |(-542997041/2500000000 : ℝ)|=(542997041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543117531/1000000000 : ℝ)|^2079 ≤ (22245557810527/50000000000000 : ℝ)^1567
        have hw : |(543117531/1000000000 : ℝ)|=(543117531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230256669/10000000000 : ℝ)|^2079 ≤ (42320763231857/100000000000000 : ℝ)^1567
        have hw : |(5230256669/10000000000 : ℝ)|=(5230256669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s3_1 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338564229/2500000000 : ℝ)*x 0 + (-454946913/2000000000 : ℝ)*x 1 + (5230256603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338564229/2500000000 : ℝ)^2079 ≤ (2182853869069/5000000000000 : ℝ)^1567 := by
    have hnat : (1338564229 : ℕ)^2079*5000000000000^1567 ≤ 2182853869069^1567*2500000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338564229 2500000000 2182853869069 5000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454946913/2000000000 : ℝ)^2079 ≤ (14022160084469/100000000000000 : ℝ)^1567 := by
    have hnat : (454946913 : ℕ)^2079*100000000000000^1567 ≤ 14022160084469^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454946913 2000000000 14022160084469 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230256603/10000000000 : ℝ)^2079 ≤ (1692830500933/4000000000000 : ℝ)^1567 := by
    have hnat : (5230256603 : ℕ)^2079*4000000000000^1567 ≤ 1692830500933^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230256603 10000000000 1692830500933 4000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338564229/2500000000 : ℝ), (-454946913/2000000000 : ℝ), (5230256603/10000000000 : ℝ)] ![(2182853869069/5000000000000 : ℝ), (14022160084469/100000000000000 : ℝ), (1692830500933/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338564229/2500000000 : ℝ)|^2079 ≤ (2182853869069/5000000000000 : ℝ)^1567
        have hw : |(1338564229/2500000000 : ℝ)|=(1338564229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-454946913/2000000000 : ℝ)|^2079 ≤ (14022160084469/100000000000000 : ℝ)^1567
        have hw : |(-454946913/2000000000 : ℝ)|=(454946913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230256603/10000000000 : ℝ)|^2079 ≤ (1692830500933/4000000000000 : ℝ)^1567
        have hw : |(5230256603/10000000000 : ℝ)|=(5230256603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s3_2 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2677128509/5000000000 : ℝ)*x 0 + (2615128353/5000000000 : ℝ)*x 1 + (-1137367147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677128509/5000000000 : ℝ)^2079 ≤ (43657078484801/100000000000000 : ℝ)^1567 := by
    have hnat : (2677128509 : ℕ)^2079*100000000000000^1567 ≤ 43657078484801^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677128509 5000000000 43657078484801 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615128353/5000000000 : ℝ)^2079 ≤ (8464152725813/20000000000000 : ℝ)^1567 := by
    have hnat : (2615128353 : ℕ)^2079*20000000000000^1567 ≤ 8464152725813^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615128353 5000000000 8464152725813 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137367147/5000000000 : ℝ)^2079 ≤ (2804431573623/20000000000000 : ℝ)^1567 := by
    have hnat : (1137367147 : ℕ)^2079*20000000000000^1567 ≤ 2804431573623^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137367147 5000000000 2804431573623 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677128509/5000000000 : ℝ), (2615128353/5000000000 : ℝ), (-1137367147/5000000000 : ℝ)] ![(43657078484801/100000000000000 : ℝ), (8464152725813/20000000000000 : ℝ), (2804431573623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677128509/5000000000 : ℝ)|^2079 ≤ (43657078484801/100000000000000 : ℝ)^1567
        have hw : |(2677128509/5000000000 : ℝ)|=(2677128509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615128353/5000000000 : ℝ)|^2079 ≤ (8464152725813/20000000000000 : ℝ)^1567
        have hw : |(2615128353/5000000000 : ℝ)|=(2615128353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1137367147/5000000000 : ℝ)|^2079 ≤ (2804431573623/20000000000000 : ℝ)^1567
        have hw : |(-1137367147/5000000000 : ℝ)|=(1137367147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s3_3 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4364973557/10000000000 : ℝ)*x 0 + (4170390039/10000000000 : ℝ)*x 1 + (4568622801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364973557/10000000000 : ℝ)^2079 ≤ (16646371322679/50000000000000 : ℝ)^1567 := by
    have hnat : (4364973557 : ℕ)^2079*50000000000000^1567 ≤ 16646371322679^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364973557 10000000000 16646371322679 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170390039/10000000000 : ℝ)^2079 ≤ (31338166543479/100000000000000 : ℝ)^1567 := by
    have hnat : (4170390039 : ℕ)^2079*100000000000000^1567 ≤ 31338166543479^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170390039 10000000000 31338166543479 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4568622801/10000000000 : ℝ)^2079 ≤ (8842272696921/25000000000000 : ℝ)^1567 := by
    have hnat : (4568622801 : ℕ)^2079*25000000000000^1567 ≤ 8842272696921^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4568622801 10000000000 8842272696921 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364973557/10000000000 : ℝ), (4170390039/10000000000 : ℝ), (4568622801/10000000000 : ℝ)] ![(16646371322679/50000000000000 : ℝ), (31338166543479/100000000000000 : ℝ), (8842272696921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364973557/10000000000 : ℝ)|^2079 ≤ (16646371322679/50000000000000 : ℝ)^1567
        have hw : |(4364973557/10000000000 : ℝ)|=(4364973557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170390039/10000000000 : ℝ)|^2079 ≤ (31338166543479/100000000000000 : ℝ)^1567
        have hw : |(4170390039/10000000000 : ℝ)|=(4170390039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4568622801/10000000000 : ℝ)|^2079 ≤ (8842272696921/25000000000000 : ℝ)^1567
        have hw : |(4568622801/10000000000 : ℝ)|=(4568622801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s3_4 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086003581/5000000000 : ℝ)*x 0 + (1046209381/2000000000 : ℝ)*x 1 + (5430380627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086003581/5000000000 : ℝ)^2079 ≤ (659413708989/5000000000000 : ℝ)^1567 := by
    have hnat : (1086003581 : ℕ)^2079*5000000000000^1567 ≤ 659413708989^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086003581 5000000000 659413708989 5000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046209381/2000000000 : ℝ)^2079 ≤ (42329246896883/100000000000000 : ℝ)^1567 := by
    have hnat : (1046209381 : ℕ)^2079*100000000000000^1567 ≤ 42329246896883^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046209381 2000000000 42329246896883 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430380627/10000000000 : ℝ)^2079 ≤ (5560309863457/12500000000000 : ℝ)^1567 := by
    have hnat : (5430380627 : ℕ)^2079*12500000000000^1567 ≤ 5560309863457^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430380627 10000000000 5560309863457 12500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086003581/5000000000 : ℝ), (1046209381/2000000000 : ℝ), (5430380627/10000000000 : ℝ)] ![(659413708989/5000000000000 : ℝ), (42329246896883/100000000000000 : ℝ), (5560309863457/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086003581/5000000000 : ℝ)|^2079 ≤ (659413708989/5000000000000 : ℝ)^1567
        have hw : |(-1086003581/5000000000 : ℝ)|=(1086003581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046209381/2000000000 : ℝ)|^2079 ≤ (42329246896883/100000000000000 : ℝ)^1567
        have hw : |(1046209381/2000000000 : ℝ)|=(1046209381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430380627/10000000000 : ℝ)|^2079 ≤ (5560309863457/12500000000000 : ℝ)^1567
        have hw : |(5430380627/10000000000 : ℝ)|=(5430380627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s3_5 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060685253/2000000000 : ℝ)*x 0 + (-2074610447/10000000000 : ℝ)*x 1 + (2715190367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060685253/2000000000 : ℝ)^2079 ≤ (5388506711707/12500000000000 : ℝ)^1567 := by
    have hnat : (1060685253 : ℕ)^2079*12500000000000^1567 ≤ 5388506711707^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060685253 2000000000 5388506711707 12500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074610447/10000000000 : ℝ)^2079 ≤ (1551183276951/12500000000000 : ℝ)^1567 := by
    have hnat : (2074610447 : ℕ)^2079*12500000000000^1567 ≤ 1551183276951^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074610447 10000000000 1551183276951 12500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715190367/5000000000 : ℝ)^2079 ≤ (22241240035259/50000000000000 : ℝ)^1567 := by
    have hnat : (2715190367 : ℕ)^2079*50000000000000^1567 ≤ 22241240035259^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715190367 5000000000 22241240035259 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060685253/2000000000 : ℝ), (-2074610447/10000000000 : ℝ), (2715190367/5000000000 : ℝ)] ![(5388506711707/12500000000000 : ℝ), (1551183276951/12500000000000 : ℝ), (22241240035259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060685253/2000000000 : ℝ)|^2079 ≤ (5388506711707/12500000000000 : ℝ)^1567
        have hw : |(1060685253/2000000000 : ℝ)|=(1060685253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2074610447/10000000000 : ℝ)|^2079 ≤ (1551183276951/12500000000000 : ℝ)^1567
        have hw : |(-2074610447/10000000000 : ℝ)|=(2074610447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715190367/5000000000 : ℝ)|^2079 ≤ (22241240035259/50000000000000 : ℝ)^1567
        have hw : |(2715190367/5000000000 : ℝ)|=(2715190367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s3_6 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5303426249/10000000000 : ℝ)*x 0 + (339398791/625000000 : ℝ)*x 1 + (-129663161/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303426249/10000000000 : ℝ)^2079 ≤ (43108053521109/100000000000000 : ℝ)^1567 := by
    have hnat : (5303426249 : ℕ)^2079*100000000000000^1567 ≤ 43108053521109^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303426249 10000000000 43108053521109 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339398791/625000000 : ℝ)^2079 ≤ (5560309902853/12500000000000 : ℝ)^1567 := by
    have hnat : (339398791 : ℕ)^2079*12500000000000^1567 ≤ 5560309902853^1567*625000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339398791 625000000 5560309902853 12500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129663161/625000000 : ℝ)^2079 ≤ (12409467239353/100000000000000 : ℝ)^1567 := by
    have hnat : (129663161 : ℕ)^2079*100000000000000^1567 ≤ 12409467239353^1567*625000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129663161 625000000 12409467239353 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303426249/10000000000 : ℝ), (339398791/625000000 : ℝ), (-129663161/625000000 : ℝ)] ![(43108053521109/100000000000000 : ℝ), (5560309902853/12500000000000 : ℝ), (12409467239353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303426249/10000000000 : ℝ)|^2079 ≤ (43108053521109/100000000000000 : ℝ)^1567
        have hw : |(5303426249/10000000000 : ℝ)|=(5303426249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339398791/625000000 : ℝ)|^2079 ≤ (5560309902853/12500000000000 : ℝ)^1567
        have hw : |(339398791/625000000 : ℝ)|=(339398791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129663161/625000000 : ℝ)|^2079 ≤ (12409467239353/100000000000000 : ℝ)^1567
        have hw : |(-129663161/625000000 : ℝ)|=(129663161/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s3_7 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2182505589/5000000000 : ℝ)*x 0 + (4567056989/10000000000 : ℝ)*x 1 + (4171964841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182505589/5000000000 : ℝ)^2079 ≤ (3329312334669/10000000000000 : ℝ)^1567 := by
    have hnat : (2182505589 : ℕ)^2079*10000000000000^1567 ≤ 3329312334669^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182505589 5000000000 3329312334669 10000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4567056989/10000000000 : ℝ)^2079 ≤ (1767650440633/5000000000000 : ℝ)^1567 := by
    have hnat : (4567056989 : ℕ)^2079*5000000000000^1567 ≤ 1767650440633^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567056989 10000000000 1767650440633 5000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171964841/10000000000 : ℝ)^2079 ≤ (6270773565351/20000000000000 : ℝ)^1567 := by
    have hnat : (4171964841 : ℕ)^2079*20000000000000^1567 ≤ 6270773565351^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171964841 10000000000 6270773565351 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182505589/5000000000 : ℝ), (4567056989/10000000000 : ℝ), (4171964841/10000000000 : ℝ)] ![(3329312334669/10000000000000 : ℝ), (1767650440633/5000000000000 : ℝ), (6270773565351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182505589/5000000000 : ℝ)|^2079 ≤ (3329312334669/10000000000000 : ℝ)^1567
        have hw : |(2182505589/5000000000 : ℝ)|=(2182505589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4567056989/10000000000 : ℝ)|^2079 ≤ (1767650440633/5000000000000 : ℝ)^1567
        have hw : |(4567056989/10000000000 : ℝ)|=(4567056989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171964841/10000000000 : ℝ)|^2079 ≤ (6270773565351/20000000000000 : ℝ)^1567
        have hw : |(4171964841/10000000000 : ℝ)|=(4171964841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1123_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (207/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5289/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14829/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (207/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8983/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (207/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8983/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (207/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8983/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (207/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8983/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (207/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8983/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (207/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8983/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8983/100000 : ℝ) ^ (8315/2048 : ℝ) ≤ (176067655569783/3125000000000000000 : ℝ) := by
    have hpowers : (8983/100000 : ℝ)^8315 ≤ (176067655569783/3125000000000000000 : ℝ)^2048 := by
      have hnat : (8983 : ℕ)^8315*3125000000000000000^2048 ≤ 176067655569783^2048*100000^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8983 100000 176067655569783 3125000000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8983/100000 : ℝ)) (X := (176067655569783/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (207/1250 : ℝ) ^ (8315/2048 : ℝ) ≤ (67505505162306717/100000000000000000000 : ℝ) := by
    have hpowers : (207/1250 : ℝ)^8315 ≤ (67505505162306717/100000000000000000000 : ℝ)^2048 := by
      have hnat : (207 : ℕ)^8315*100000000000000000000^2048 ≤ 67505505162306717^2048*1250^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        207 1250 67505505162306717 100000000000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (207/1250 : ℝ)) (X := (67505505162306717/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562676067655569783/1562500000000000000 : ℝ) ≤ (5000138764641233/5000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (1562676067655569783/1562500000000000000 : ℝ)^2048 ≤ (5000138764641233/5000000000000000 : ℝ)^8315 := by
      have hnat : (1562676067655569783 : ℕ)^2048*5000000000000000^8315 ≤ 5000138764641233^8315*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562676067655569783 1562500000000000000 5000138764641233 5000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138764641233/5000000000000000 : ℝ)) (X := (1562676067655569783/1562500000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100073139670140539773/100000000000000000000 : ℝ) ≤ (1250225118424587/1250000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (100073139670140539773/100000000000000000000 : ℝ)^2048 ≤ (1250225118424587/1250000000000000 : ℝ)^8315 := by
      have hnat : (100073139670140539773 : ℕ)^2048*1250000000000000^8315 ≤ 1250225118424587^8315*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100073139670140539773 100000000000000000000 1250225118424587 1250000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250225118424587/1250000000000000 : ℝ)) (X := (100073139670140539773/100000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50067505505162306717/50000000000000000000 : ℝ) ≤ (5001662182755463/5000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (50067505505162306717/50000000000000000000 : ℝ)^2048 ≤ (5001662182755463/5000000000000000 : ℝ)^8315 := by
      have hnat : (50067505505162306717 : ℕ)^2048*5000000000000000^8315 ≤ 5001662182755463^8315*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50067505505162306717 50000000000000000000 5001662182755463 5000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001662182755463/5000000000000000 : ℝ)) (X := (50067505505162306717/50000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(176067655569783/3125000000000000000 : ℝ) ≤ ((37872366554766494351/37885000000000000000 : ℝ)+2*(152341811423/75770000000000 : ℝ)*(8983/100000 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (37872366554766494351/37885000000000000000 : ℝ)+2*(152341811423/75770000000000 : ℝ)*(8983/100000 : ℝ)=(5000138764641233/5000000000000000 : ℝ) by norm_num, show 1+2*(176067655569783/3125000000000000000 : ℝ)=(1562676067655569783/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(67505505162306717/100000000000000000000 : ℝ)+(176067655569783/3125000000000000000 : ℝ) ≤ ((37872366554766494351/37885000000000000000 : ℝ)+(152341811423/75770000000000 : ℝ)*((207/1250 : ℝ)+(8983/100000 : ℝ)))^(8315/2048 : ℝ) := by
    rw [show (37872366554766494351/37885000000000000000 : ℝ)+(152341811423/75770000000000 : ℝ)*((207/1250 : ℝ)+(8983/100000 : ℝ))=(1250225118424587/1250000000000000 : ℝ) by norm_num, show 1+(67505505162306717/100000000000000000000 : ℝ)+(176067655569783/3125000000000000000 : ℝ)=(100073139670140539773/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(67505505162306717/100000000000000000000 : ℝ) ≤ ((37872366554766494351/37885000000000000000 : ℝ)+2*(152341811423/75770000000000 : ℝ)*(207/1250 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (37872366554766494351/37885000000000000000 : ℝ)+2*(152341811423/75770000000000 : ℝ)*(207/1250 : ℝ)=(5001662182755463/5000000000000000 : ℝ) by norm_num, show 1+2*(67505505162306717/100000000000000000000 : ℝ)=(50067505505162306717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37872366554766494351/37885000000000000000 : ℝ)*(X 1 0+X 2 0)+(152341811423/75770000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (8983/100000 : ℝ)) (hi := (207/1250 : ℝ)) (c := (37872366554766494351/37885000000000000000 : ℝ)) (alpha := (152341811423/75770000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37872366554766494351/37885000000000000000 : ℝ)*(X 0 1+X 2 1)+(152341811423/75770000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (8983/100000 : ℝ)) (hi := (207/1250 : ℝ)) (c := (37872366554766494351/37885000000000000000 : ℝ)) (alpha := (152341811423/75770000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37872366554766494351/37885000000000000000 : ℝ)*(X 0 2+X 1 2)+(152341811423/75770000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (8983/100000 : ℝ)) (hi := (207/1250 : ℝ)) (c := (37872366554766494351/37885000000000000000 : ℝ)) (alpha := (152341811423/75770000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-542997041/2500000000 : ℝ)*X 0 0+(543117531/1000000000 : ℝ)*X 0 1+(5230256669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338564229/2500000000 : ℝ)*X 1 0+(-454946913/2000000000 : ℝ)*X 1 1+(5230256603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677128509/5000000000 : ℝ)*X 2 0+(2615128353/5000000000 : ℝ)*X 2 1+(-1137367147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364973557/10000000000 : ℝ)*X 0 0+(4170390039/10000000000 : ℝ)*X 0 1+(4568622801/10000000000 : ℝ)*X 0 2+(4364973557/10000000000 : ℝ)*X 1 0+(4170390039/10000000000 : ℝ)*X 1 1+(4568622801/10000000000 : ℝ)*X 1 2+(4364973557/10000000000 : ℝ)*X 2 0+(4170390039/10000000000 : ℝ)*X 2 1+(4568622801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086003581/5000000000 : ℝ)*X 0 0+(1046209381/2000000000 : ℝ)*X 0 1+(5430380627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060685253/2000000000 : ℝ)*X 1 0+(-2074610447/10000000000 : ℝ)*X 1 1+(2715190367/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303426249/10000000000 : ℝ)*X 2 0+(339398791/625000000 : ℝ)*X 2 1+(-129663161/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182505589/5000000000 : ℝ)*X 0 0+(4567056989/10000000000 : ℝ)*X 0 1+(4171964841/10000000000 : ℝ)*X 0 2+(2182505589/5000000000 : ℝ)*X 1 0+(4567056989/10000000000 : ℝ)*X 1 1+(4171964841/10000000000 : ℝ)*X 1 2+(2182505589/5000000000 : ℝ)*X 2 0+(4567056989/10000000000 : ℝ)*X 2 1+(4171964841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3228328940732151031567187661/1894250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152982603/20000000000000 : ℝ)*(base19) + (374692601/50000000000000 : ℝ)*(base23) + (70181817/100000000000000 : ℝ)*(lower2) + (112779873/100000000000000 : ℝ)*(upper5) + (3744138804289937/100000000000000 : ℝ)*(major0) + (3744138804289937/100000000000000 : ℝ)*(major1) + (3744138804289937/100000000000000 : ℝ)*(major2) + (4977152000029201/100000000000000 : ℝ)*(sp0) + (1244291956140959/25000000000000 : ℝ)*(sp1) + (2488585011974797/50000000000000 : ℝ)*(sp2) + (627775201934447/25000000000000 : ℝ)*(sp3) + (3754661119/20000000000000 : ℝ)*(sp4) + (272982243/12500000000000 : ℝ)*(sp5) + (5970698009/100000000000000 : ℝ)*(sp7) + (627776694608949/25000000000000 : ℝ)*(f.failure) + (995434154666959/20000000000000 : ℝ)*(f.sum) + (20469484838963/3788500000000000000000000000 : ℝ)*base66 + (5954433105640854113/3788500000000000000000000000000000 : ℝ)*base68 + (15131376790501354113/3788500000000000000000000000000000 : ℝ)*base70 + (45604177158026854113/3788500000000000000000000000000000 : ℝ)*base72 + (47382663853823/7577000000000000000000000000 : ℝ)*base74 + (63818082168903645887/3788500000000000000000000000000000 : ℝ)*base75 + (41542002570632854113/3788500000000000000000000000000000 : ℝ)*base78 + (33709962534817645887/3788500000000000000000000000000000 : ℝ)*base79 + (2259035349823/1515400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (308963/250000000000000000000 : ℝ)*base90 + (308963/250000000000000000000 : ℝ)*base92 + (308963/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12199605211633572642388540341/1894250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (618067969/50000000000000 : ℝ)*(base19) + (706557273/50000000000000 : ℝ)*(base23) + (152762553/100000000000000 : ℝ)*(upper3) + (96281299/100000000000000 : ℝ)*(lower4) + (3311889/3125000000000 : ℝ)*(upper5) + (3773882266759501/100000000000000 : ℝ)*(major0) + (3773882266759501/100000000000000 : ℝ)*(major1) + (3773882266759501/100000000000000 : ℝ)*(major2) + (1454669953/6250000000000 : ℝ)*(sp1) + (24377291357/100000000000000 : ℝ)*(sp2) + (1254177323047449/25000000000000 : ℝ)*(sp4) + (501668478133461/10000000000000 : ℝ)*(sp5) + (5016683501783893/100000000000000 : ℝ)*(sp6) + (316381878331419/12500000000000 : ℝ)*(sp7) + (316381878331419/12500000000000 : ℝ)*(f.failure) + (1254177323047449/25000000000000 : ℝ)*(f.sum) + (13002214682319/3788500000000000000000000000 : ℝ)*base65 + (25191206871995578851/3788500000000000000000000000000000 : ℝ)*base67 + (8408088922279578851/3788500000000000000000000000000000 : ℝ)*base69 + (26364191005304578851/3788500000000000000000000000000000 : ℝ)*base71 + (1300476194091/378850000000000000000000000 : ℝ)*base73 + (15344392228887578851/3788500000000000000000000000000000 : ℝ)*base75 + (24395118262902078851/3788500000000000000000000000000000 : ℝ)*base77 + (43882595734400578851/3788500000000000000000000000000000 : ℝ)*base79 + (1171309151371/1894250000000000000000000000 : ℝ)*base81 + (1225853/125000000000000000000 : ℝ)*base90 + (1225853/125000000000000000000 : ℝ)*base92 + (1225853/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1123_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (207/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5289/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14829/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1123_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1123_s4_0 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2175146061/10000000000 : ℝ)*x 0 + (1080563927/2000000000 : ℝ)*x 1 + (2628273703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175146061/10000000000 : ℝ)^2079 ≤ (528542667843/4000000000000 : ℝ)^1567 := by
    have hnat : (2175146061 : ℕ)^2079*4000000000000^1567 ≤ 528542667843^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175146061 10000000000 528542667843 4000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080563927/2000000000 : ℝ)^2079 ≤ (44183198428797/100000000000000 : ℝ)^1567 := by
    have hnat : (1080563927 : ℕ)^2079*100000000000000^1567 ≤ 44183198428797^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080563927 2000000000 44183198428797 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628273703/5000000000 : ℝ)^2079 ≤ (10650808716047/25000000000000 : ℝ)^1567 := by
    have hnat : (2628273703 : ℕ)^2079*25000000000000^1567 ≤ 10650808716047^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628273703 5000000000 10650808716047 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2175146061/10000000000 : ℝ), (1080563927/2000000000 : ℝ), (2628273703/5000000000 : ℝ)] ![(528542667843/4000000000000 : ℝ), (44183198428797/100000000000000 : ℝ), (10650808716047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2175146061/10000000000 : ℝ)|^2079 ≤ (528542667843/4000000000000 : ℝ)^1567
        have hw : |(-2175146061/10000000000 : ℝ)|=(2175146061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080563927/2000000000 : ℝ)|^2079 ≤ (44183198428797/100000000000000 : ℝ)^1567
        have hw : |(1080563927/2000000000 : ℝ)|=(1080563927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628273703/5000000000 : ℝ)|^2079 ≤ (10650808716047/25000000000000 : ℝ)^1567
        have hw : |(2628273703/5000000000 : ℝ)|=(2628273703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s4_1 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347190637/10000000000 : ℝ)*x 0 + (-449898927/2000000000 : ℝ)*x 1 + (5256547487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347190637/10000000000 : ℝ)^2079 ≤ (43580651923177/100000000000000 : ℝ)^1567 := by
    have hnat : (5347190637 : ℕ)^2079*100000000000000^1567 ≤ 43580651923177^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347190637 10000000000 43580651923177 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449898927/2000000000 : ℝ)^2079 ≤ (863507020339/6250000000000 : ℝ)^1567 := by
    have hnat : (449898927 : ℕ)^2079*6250000000000^1567 ≤ 863507020339^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449898927 2000000000 863507020339 6250000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256547487/10000000000 : ℝ)^2079 ≤ (42603235735177/100000000000000 : ℝ)^1567 := by
    have hnat : (5256547487 : ℕ)^2079*100000000000000^1567 ≤ 42603235735177^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256547487 10000000000 42603235735177 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347190637/10000000000 : ℝ), (-449898927/2000000000 : ℝ), (5256547487/10000000000 : ℝ)] ![(43580651923177/100000000000000 : ℝ), (863507020339/6250000000000 : ℝ), (42603235735177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347190637/10000000000 : ℝ)|^2079 ≤ (43580651923177/100000000000000 : ℝ)^1567
        have hw : |(5347190637/10000000000 : ℝ)|=(5347190637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-449898927/2000000000 : ℝ)|^2079 ≤ (863507020339/6250000000000 : ℝ)^1567
        have hw : |(-449898927/2000000000 : ℝ)|=(449898927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256547487/10000000000 : ℝ)|^2079 ≤ (42603235735177/100000000000000 : ℝ)^1567
        have hw : |(5256547487/10000000000 : ℝ)|=(5256547487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s4_2 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347190413/10000000000 : ℝ)*x 0 + (525654731/1000000000 : ℝ)*x 1 + (-1124747583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347190413/10000000000 : ℝ)^2079 ≤ (1361895296907/3125000000000 : ℝ)^1567 := by
    have hnat : (5347190413 : ℕ)^2079*3125000000000^1567 ≤ 1361895296907^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347190413 10000000000 1361895296907 3125000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525654731/1000000000 : ℝ)^2079 ≤ (8520646766381/20000000000000 : ℝ)^1567 := by
    have hnat : (525654731 : ℕ)^2079*20000000000000^1567 ≤ 8520646766381^1567*1000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525654731 1000000000 8520646766381 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124747583/5000000000 : ℝ)^2079 ≤ (2763223330473/20000000000000 : ℝ)^1567 := by
    have hnat : (1124747583 : ℕ)^2079*20000000000000^1567 ≤ 2763223330473^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124747583 5000000000 2763223330473 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347190413/10000000000 : ℝ), (525654731/1000000000 : ℝ), (-1124747583/5000000000 : ℝ)] ![(1361895296907/3125000000000 : ℝ), (8520646766381/20000000000000 : ℝ), (2763223330473/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347190413/10000000000 : ℝ)|^2079 ≤ (1361895296907/3125000000000 : ℝ)^1567
        have hw : |(5347190413/10000000000 : ℝ)|=(5347190413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525654731/1000000000 : ℝ)|^2079 ≤ (8520646766381/20000000000000 : ℝ)^1567
        have hw : |(525654731/1000000000 : ℝ)|=(525654731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1124747583/5000000000 : ℝ)|^2079 ≤ (2763223330473/20000000000000 : ℝ)^1567
        have hw : |(-1124747583/5000000000 : ℝ)|=(1124747583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s4_3 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2183428711/5000000000 : ℝ)*x 0 + (4224300851/10000000000 : ℝ)*x 1 + (4514222359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183428711/5000000000 : ℝ)^2079 ≤ (1665590375759/5000000000000 : ℝ)^1567 := by
    have hnat : (2183428711 : ℕ)^2079*5000000000000^1567 ≤ 1665590375759^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183428711 5000000000 1665590375759 5000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224300851/10000000000 : ℝ)^2079 ≤ (255014186899/800000000000 : ℝ)^1567 := by
    have hnat : (4224300851 : ℕ)^2079*800000000000^1567 ≤ 255014186899^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224300851 10000000000 255014186899 800000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514222359/10000000000 : ℝ)^2079 ≤ (34811419118631/100000000000000 : ℝ)^1567 := by
    have hnat : (4514222359 : ℕ)^2079*100000000000000^1567 ≤ 34811419118631^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514222359 10000000000 34811419118631 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183428711/5000000000 : ℝ), (4224300851/10000000000 : ℝ), (4514222359/10000000000 : ℝ)] ![(1665590375759/5000000000000 : ℝ), (255014186899/800000000000 : ℝ), (34811419118631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183428711/5000000000 : ℝ)|^2079 ≤ (1665590375759/5000000000000 : ℝ)^1567
        have hw : |(2183428711/5000000000 : ℝ)|=(2183428711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224300851/10000000000 : ℝ)|^2079 ≤ (255014186899/800000000000 : ℝ)^1567
        have hw : |(4224300851/10000000000 : ℝ)|=(4224300851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514222359/10000000000 : ℝ)|^2079 ≤ (34811419118631/100000000000000 : ℝ)^1567
        have hw : |(4514222359/10000000000 : ℝ)|=(4514222359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s4_4 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-435030637/2000000000 : ℝ)*x 0 + (5256966923/10000000000 : ℝ)*x 1 + (33764991/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435030637/2000000000 : ℝ)^2079 ≤ (13213624113177/100000000000000 : ℝ)^1567 := by
    have hnat : (435030637 : ℕ)^2079*100000000000000^1567 ≤ 13213624113177^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435030637 2000000000 13213624113177 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256966923/10000000000 : ℝ)^2079 ≤ (42607745966847/100000000000000 : ℝ)^1567 := by
    have hnat : (5256966923 : ℕ)^2079*100000000000000^1567 ≤ 42607745966847^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256966923 10000000000 42607745966847 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33764991/62500000 : ℝ)^2079 ≤ (44178629902783/100000000000000 : ℝ)^1567 := by
    have hnat : (33764991 : ℕ)^2079*100000000000000^1567 ≤ 44178629902783^1567*62500000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33764991 62500000 44178629902783 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435030637/2000000000 : ℝ), (5256966923/10000000000 : ℝ), (33764991/62500000 : ℝ)] ![(13213624113177/100000000000000 : ℝ), (42607745966847/100000000000000 : ℝ), (44178629902783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435030637/2000000000 : ℝ)|^2079 ≤ (13213624113177/100000000000000 : ℝ)^1567
        have hw : |(-435030637/2000000000 : ℝ)|=(435030637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256966923/10000000000 : ℝ)|^2079 ≤ (42607745966847/100000000000000 : ℝ)^1567
        have hw : |(5256966923/10000000000 : ℝ)|=(5256966923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33764991/62500000 : ℝ)|^2079 ≤ (44178629902783/100000000000000 : ℝ)^1567
        have hw : |(33764991/62500000 : ℝ)|=(33764991/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s4_5 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331886641/625000000 : ℝ)*x 0 + (-525910947/2500000000 : ℝ)*x 1 + (2701199283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331886641/625000000 : ℝ)^2079 ≤ (21590484935461/50000000000000 : ℝ)^1567 := by
    have hnat : (331886641 : ℕ)^2079*50000000000000^1567 ≤ 21590484935461^1567*625000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331886641 625000000 21590484935461 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525910947/2500000000 : ℝ)^2079 ≤ (632020007247/5000000000000 : ℝ)^1567 := by
    have hnat : (525910947 : ℕ)^2079*5000000000000^1567 ≤ 632020007247^1567*2500000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525910947 2500000000 632020007247 5000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701199283/5000000000 : ℝ)^2079 ≤ (1104465749197/2500000000000 : ℝ)^1567 := by
    have hnat : (2701199283 : ℕ)^2079*2500000000000^1567 ≤ 1104465749197^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701199283 5000000000 1104465749197 2500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331886641/625000000 : ℝ), (-525910947/2500000000 : ℝ), (2701199283/5000000000 : ℝ)] ![(21590484935461/50000000000000 : ℝ), (632020007247/5000000000000 : ℝ), (1104465749197/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331886641/625000000 : ℝ)|^2079 ≤ (21590484935461/50000000000000 : ℝ)^1567
        have hw : |(331886641/625000000 : ℝ)|=(331886641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525910947/2500000000 : ℝ)|^2079 ≤ (632020007247/5000000000000 : ℝ)^1567
        have hw : |(-525910947/2500000000 : ℝ)|=(525910947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701199283/5000000000 : ℝ)|^2079 ≤ (1104465749197/2500000000000 : ℝ)^1567
        have hw : |(2701199283/5000000000 : ℝ)|=(2701199283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s4_6 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655093143/5000000000 : ℝ)*x 0 + (675299813/1250000000 : ℝ)*x 1 + (-2103643831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655093143/5000000000 : ℝ)^2079 ≤ (21590485097291/50000000000000 : ℝ)^1567 := by
    have hnat : (2655093143 : ℕ)^2079*50000000000000^1567 ≤ 21590485097291^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655093143 5000000000 21590485097291 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675299813/1250000000 : ℝ)^2079 ≤ (44178629295209/100000000000000 : ℝ)^1567 := by
    have hnat : (675299813 : ℕ)^2079*100000000000000^1567 ≤ 44178629295209^1567*1250000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675299813 1250000000 44178629295209 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103643831/10000000000 : ℝ)^2079 ≤ (12640400487741/100000000000000 : ℝ)^1567 := by
    have hnat : (2103643831 : ℕ)^2079*100000000000000^1567 ≤ 12640400487741^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103643831 10000000000 12640400487741 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655093143/5000000000 : ℝ), (675299813/1250000000 : ℝ), (-2103643831/10000000000 : ℝ)] ![(21590485097291/50000000000000 : ℝ), (44178629295209/100000000000000 : ℝ), (12640400487741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655093143/5000000000 : ℝ)|^2079 ≤ (21590485097291/50000000000000 : ℝ)^1567
        have hw : |(2655093143/5000000000 : ℝ)|=(2655093143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675299813/1250000000 : ℝ)|^2079 ≤ (44178629295209/100000000000000 : ℝ)^1567
        have hw : |(675299813/1250000000 : ℝ)|=(675299813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2103643831/10000000000 : ℝ)|^2079 ≤ (12640400487741/100000000000000 : ℝ)^1567
        have hw : |(-2103643831/10000000000 : ℝ)|=(2103643831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s4_7 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (436687199/1000000000 : ℝ)*x 0 + (2256695291/5000000000 : ℝ)*x 1 + (845027217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436687199/1000000000 : ℝ)^2079 ≤ (33311954955019/100000000000000 : ℝ)^1567 := by
    have hnat : (436687199 : ℕ)^2079*100000000000000^1567 ≤ 33311954955019^1567*1000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436687199 1000000000 33311954955019 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256695291/5000000000 : ℝ)^2079 ≤ (6960581868611/20000000000000 : ℝ)^1567 := by
    have hnat : (2256695291 : ℕ)^2079*20000000000000^1567 ≤ 6960581868611^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256695291 5000000000 6960581868611 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845027217/2000000000 : ℝ)^2079 ≤ (15942567845199/50000000000000 : ℝ)^1567 := by
    have hnat : (845027217 : ℕ)^2079*50000000000000^1567 ≤ 15942567845199^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845027217 2000000000 15942567845199 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436687199/1000000000 : ℝ), (2256695291/5000000000 : ℝ), (845027217/2000000000 : ℝ)] ![(33311954955019/100000000000000 : ℝ), (6960581868611/20000000000000 : ℝ), (15942567845199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436687199/1000000000 : ℝ)|^2079 ≤ (33311954955019/100000000000000 : ℝ)^1567
        have hw : |(436687199/1000000000 : ℝ)|=(436687199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256695291/5000000000 : ℝ)|^2079 ≤ (6960581868611/20000000000000 : ℝ)^1567
        have hw : |(2256695291/5000000000 : ℝ)|=(2256695291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845027217/2000000000 : ℝ)|^2079 ≤ (15942567845199/50000000000000 : ℝ)^1567
        have hw : |(845027217/2000000000 : ℝ)|=(845027217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1123_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14829/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5289/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11139/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14829/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5289/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14829/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5289/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14829/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5289/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14829/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5289/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14829/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5289/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14829/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5289/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5289/50000 : ℝ) ^ (8315/2048 : ℝ) ≤ (10940100223560659/100000000000000000000 : ℝ) := by
    have hpowers : (5289/50000 : ℝ)^8315 ≤ (10940100223560659/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5289 : ℕ)^8315*100000000000000000000^2048 ≤ 10940100223560659^2048*50000^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5289 50000 10940100223560659 100000000000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5289/50000 : ℝ)) (X := (10940100223560659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14829/100000 : ℝ) ^ (8315/2048 : ℝ) ≤ (21559347333262621/50000000000000000000 : ℝ) := by
    have hpowers : (14829/100000 : ℝ)^8315 ≤ (21559347333262621/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14829 : ℕ)^8315*50000000000000000000^2048 ≤ 21559347333262621^2048*100000^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14829 100000 21559347333262621 50000000000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14829/100000 : ℝ)) (X := (21559347333262621/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010940100223560659/50000000000000000000 : ℝ) ≤ (5000269434492551/5000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (50010940100223560659/50000000000000000000 : ℝ)^2048 ≤ (5000269434492551/5000000000000000 : ℝ)^8315 := by
      have hnat : (50010940100223560659 : ℕ)^2048*5000000000000000^8315 ≤ 5000269434492551^8315*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010940100223560659 50000000000000000000 5000269434492551 5000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269434492551/5000000000000000 : ℝ)) (X := (50010940100223560659/50000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054058794890085901/100000000000000000000 : ℝ) ≤ (1000133120703211/1000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (100054058794890085901/100000000000000000000 : ℝ)^2048 ≤ (1000133120703211/1000000000000000 : ℝ)^8315 := by
      have hnat : (100054058794890085901 : ℕ)^2048*1000000000000000^8315 ≤ 1000133120703211^8315*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054058794890085901 100000000000000000000 1000133120703211 1000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000133120703211/1000000000000000 : ℝ)) (X := (100054058794890085901/100000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25021559347333262621/25000000000000000000 : ℝ) ≤ (5001061772539559/5000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (25021559347333262621/25000000000000000000 : ℝ)^2048 ≤ (5001061772539559/5000000000000000 : ℝ)^8315 := by
      have hnat : (25021559347333262621 : ℕ)^2048*5000000000000000^8315 ≤ 5001061772539559^8315*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021559347333262621 25000000000000000000 5001061772539559 5000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001061772539559/5000000000000000 : ℝ)) (X := (25021559347333262621/25000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10940100223560659/100000000000000000000 : ℝ) ≤ ((7082588004722194559/7085000000000000000 : ℝ)+2*(8253521323/4428125000000 : ℝ)*(5289/50000 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (7082588004722194559/7085000000000000000 : ℝ)+2*(8253521323/4428125000000 : ℝ)*(5289/50000 : ℝ)=(5000269434492551/5000000000000000 : ℝ) by norm_num, show 1+2*(10940100223560659/100000000000000000000 : ℝ)=(50010940100223560659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21559347333262621/50000000000000000000 : ℝ)+(10940100223560659/100000000000000000000 : ℝ) ≤ ((7082588004722194559/7085000000000000000 : ℝ)+(8253521323/4428125000000 : ℝ)*((14829/100000 : ℝ)+(5289/50000 : ℝ)))^(8315/2048 : ℝ) := by
    rw [show (7082588004722194559/7085000000000000000 : ℝ)+(8253521323/4428125000000 : ℝ)*((14829/100000 : ℝ)+(5289/50000 : ℝ))=(1000133120703211/1000000000000000 : ℝ) by norm_num, show 1+(21559347333262621/50000000000000000000 : ℝ)+(10940100223560659/100000000000000000000 : ℝ)=(100054058794890085901/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21559347333262621/50000000000000000000 : ℝ) ≤ ((7082588004722194559/7085000000000000000 : ℝ)+2*(8253521323/4428125000000 : ℝ)*(14829/100000 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (7082588004722194559/7085000000000000000 : ℝ)+2*(8253521323/4428125000000 : ℝ)*(14829/100000 : ℝ)=(5001061772539559/5000000000000000 : ℝ) by norm_num, show 1+2*(21559347333262621/50000000000000000000 : ℝ)=(25021559347333262621/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7082588004722194559/7085000000000000000 : ℝ)*(X 1 0+X 2 0)+(8253521323/4428125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (5289/50000 : ℝ)) (hi := (14829/100000 : ℝ)) (c := (7082588004722194559/7085000000000000000 : ℝ)) (alpha := (8253521323/4428125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7082588004722194559/7085000000000000000 : ℝ)*(X 0 1+X 2 1)+(8253521323/4428125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (5289/50000 : ℝ)) (hi := (14829/100000 : ℝ)) (c := (7082588004722194559/7085000000000000000 : ℝ)) (alpha := (8253521323/4428125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7082588004722194559/7085000000000000000 : ℝ)*(X 0 2+X 1 2)+(8253521323/4428125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (5289/50000 : ℝ)) (hi := (14829/100000 : ℝ)) (c := (7082588004722194559/7085000000000000000 : ℝ)) (alpha := (8253521323/4428125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2175146061/10000000000 : ℝ)*X 0 0+(1080563927/2000000000 : ℝ)*X 0 1+(2628273703/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347190637/10000000000 : ℝ)*X 1 0+(-449898927/2000000000 : ℝ)*X 1 1+(5256547487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347190413/10000000000 : ℝ)*X 2 0+(525654731/1000000000 : ℝ)*X 2 1+(-1124747583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183428711/5000000000 : ℝ)*X 0 0+(4224300851/10000000000 : ℝ)*X 0 1+(4514222359/10000000000 : ℝ)*X 0 2+(2183428711/5000000000 : ℝ)*X 1 0+(4224300851/10000000000 : ℝ)*X 1 1+(4514222359/10000000000 : ℝ)*X 1 2+(2183428711/5000000000 : ℝ)*X 2 0+(4224300851/10000000000 : ℝ)*X 2 1+(4514222359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-435030637/2000000000 : ℝ)*X 0 0+(5256966923/10000000000 : ℝ)*X 0 1+(33764991/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331886641/625000000 : ℝ)*X 1 0+(-525910947/2500000000 : ℝ)*X 1 1+(2701199283/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655093143/5000000000 : ℝ)*X 2 0+(675299813/1250000000 : ℝ)*X 2 1+(-2103643831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436687199/1000000000 : ℝ)*X 0 0+(2256695291/5000000000 : ℝ)*X 0 1+(845027217/2000000000 : ℝ)*X 0 2+(436687199/1000000000 : ℝ)*X 1 0+(2256695291/5000000000 : ℝ)*X 1 1+(845027217/2000000000 : ℝ)*X 1 2+(436687199/1000000000 : ℝ)*X 2 0+(2256695291/5000000000 : ℝ)*X 2 1+(845027217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79797427670895966273394623/27250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1151094871/100000000000000 : ℝ)*(base19) + (1055707071/100000000000000 : ℝ)*(base23) + (73876671/50000000000000 : ℝ)*(upper2) + (50026219/20000000000000 : ℝ)*(upper3) + (5142943063677313/100000000000000 : ℝ)*(major0) + (5142943063677313/100000000000000 : ℝ)*(major1) + (5142943063677313/100000000000000 : ℝ)*(major2) + (1709152424484157/25000000000000 : ℝ)*(sp0) + (3418316315218827/50000000000000 : ℝ)*(sp1) + (3418310198945431/50000000000000 : ℝ)*(sp2) + (431153749043881/12500000000000 : ℝ)*(sp3) + (12041797949/50000000000000 : ℝ)*(sp4) + (12327934593/100000000000000 : ℝ)*(sp6) + (2781982439/12500000000000 : ℝ)*(sp7) + (3449252248210559/100000000000000 : ℝ)*(f.failure) + (273465351261301/4000000000000 : ℝ)*(f.sum) + (14553258733581/3542500000000000000000000000 : ℝ)*base66 + (1565333614977739967/708500000000000000000000000000000 : ℝ)*base67 + (2691997635961260033/708500000000000000000000000000000 : ℝ)*base70 + (604704301900260033/708500000000000000000000000000000 : ℝ)*base72 + (5524778915951/3542500000000000000000000000 : ℝ)*base74 + (7651406865013739967/708500000000000000000000000000000 : ℝ)*base75 + (7557745651848739967/708500000000000000000000000000000 : ℝ)*base77 + (3319468055984739967/708500000000000000000000000000000 : ℝ)*base79 + (7803085675377/7085000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (5405033/1000000000000000000000 : ℝ)*base90 + (5405033/1000000000000000000000 : ℝ)*base92 + (5405033/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (856534605612026152837291449/177125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (864288157/100000000000000 : ℝ)*(base19) + (231766969/25000000000000 : ℝ)*(base23) + (14776897/25000000000000 : ℝ)*(upper3) + (10214983/50000000000000 : ℝ)*(lower4) + (92650357/100000000000000 : ℝ)*(upper5) + (5172620115719763/100000000000000 : ℝ)*(major0) + (5172620115719763/100000000000000 : ℝ)*(major1) + (5172620115719763/100000000000000 : ℝ)*(major2) + (11737427977/50000000000000 : ℝ)*(sp1) + (10694244519/50000000000000 : ℝ)*(sp2) + (6876084113749531/100000000000000 : ℝ)*(sp4) + (343802988730271/5000000000000 : ℝ)*(sp5) + (859507724774077/12500000000000 : ℝ)*(sp6) + (346915595649787/10000000000000 : ℝ)*(sp7) + (346915595649787/10000000000000 : ℝ)*(f.failure) + (6876084113749531/100000000000000 : ℝ)*(f.sum) + (30920116570843/7085000000000000000000000000 : ℝ)*base65 + (2602332409075269517/708500000000000000000000000000000 : ℝ)*base67 + (4736624286890769517/708500000000000000000000000000000 : ℝ)*base69 + (3758853755022769517/708500000000000000000000000000000 : ℝ)*base71 + (12721831171891/3542500000000000000000000000 : ℝ)*base74 + (12575176423352230483/708500000000000000000000000000000 : ℝ)*base76 + (3504327502080769517/708500000000000000000000000000000 : ℝ)*base77 + (8077711712761769517/708500000000000000000000000000000 : ℝ)*base79 + (5046559119521/3542500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (446669/100000000000000000000 : ℝ)*base90 + (446669/100000000000000000000 : ℝ)*base92 + (446669/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1123_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14829/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5289/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1123_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1123_s5_0 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2175827969/10000000000 : ℝ)*x 0 + (5395414447/10000000000 : ℝ)*x 1 + (2631752493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175827969/10000000000 : ℝ)^2079 ≤ (13219062929327/100000000000000 : ℝ)^1567 := by
    have hnat : (2175827969 : ℕ)^2079*100000000000000^1567 ≤ 13219062929327^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175827969 10000000000 13219062929327 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395414447/10000000000 : ℝ)^2079 ≤ (44102871534371/100000000000000 : ℝ)^1567 := by
    have hnat : (5395414447 : ℕ)^2079*100000000000000^1567 ≤ 44102871534371^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395414447 10000000000 44102871534371 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631752493/5000000000 : ℝ)^2079 ≤ (10669516380571/25000000000000 : ℝ)^1567 := by
    have hnat : (2631752493 : ℕ)^2079*25000000000000^1567 ≤ 10669516380571^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631752493 5000000000 10669516380571 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2175827969/10000000000 : ℝ), (5395414447/10000000000 : ℝ), (2631752493/5000000000 : ℝ)] ![(13219062929327/100000000000000 : ℝ), (44102871534371/100000000000000 : ℝ), (10669516380571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2175827969/10000000000 : ℝ)|^2079 ≤ (13219062929327/100000000000000 : ℝ)^1567
        have hw : |(-2175827969/10000000000 : ℝ)|=(2175827969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395414447/10000000000 : ℝ)|^2079 ≤ (44102871534371/100000000000000 : ℝ)^1567
        have hw : |(5395414447/10000000000 : ℝ)|=(5395414447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631752493/5000000000 : ℝ)|^2079 ≤ (10669516380571/25000000000000 : ℝ)^1567
        have hw : |(2631752493/5000000000 : ℝ)|=(2631752493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s5_1 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069067267/2000000000 : ℝ)*x 0 + (-2242769109/10000000000 : ℝ)*x 1 + (526350473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069067267/2000000000 : ℝ)^2079 ≤ (43560602152597/100000000000000 : ℝ)^1567 := by
    have hnat : (1069067267 : ℕ)^2079*100000000000000^1567 ≤ 43560602152597^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069067267 2000000000 43560602152597 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242769109/10000000000 : ℝ)^2079 ≤ (13761335063397/100000000000000 : ℝ)^1567 := by
    have hnat : (2242769109 : ℕ)^2079*100000000000000^1567 ≤ 13761335063397^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242769109 10000000000 13761335063397 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526350473/1000000000 : ℝ)^2079 ≤ (2133903138417/5000000000000 : ℝ)^1567 := by
    have hnat : (526350473 : ℕ)^2079*5000000000000^1567 ≤ 2133903138417^1567*1000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526350473 1000000000 2133903138417 5000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069067267/2000000000 : ℝ), (-2242769109/10000000000 : ℝ), (526350473/1000000000 : ℝ)] ![(43560602152597/100000000000000 : ℝ), (13761335063397/100000000000000 : ℝ), (2133903138417/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069067267/2000000000 : ℝ)|^2079 ≤ (43560602152597/100000000000000 : ℝ)^1567
        have hw : |(1069067267/2000000000 : ℝ)|=(1069067267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2242769109/10000000000 : ℝ)|^2079 ≤ (13761335063397/100000000000000 : ℝ)^1567
        have hw : |(-2242769109/10000000000 : ℝ)|=(2242769109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526350473/1000000000 : ℝ)|^2079 ≤ (2133903138417/5000000000000 : ℝ)^1567
        have hw : |(526350473/1000000000 : ℝ)|=(526350473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s5_2 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53453361/100000000 : ℝ)*x 0 + (2631752459/5000000000 : ℝ)*x 1 + (-560692293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53453361/100000000 : ℝ)^2079 ≤ (43560599611787/100000000000000 : ℝ)^1567 := by
    have hnat : (53453361 : ℕ)^2079*100000000000000^1567 ≤ 43560599611787^1567*100000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53453361 100000000 43560599611787 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631752459/5000000000 : ℝ)^2079 ≤ (2667379049423/6250000000000 : ℝ)^1567 := by
    have hnat : (2631752459 : ℕ)^2079*6250000000000^1567 ≤ 2667379049423^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631752459 5000000000 2667379049423 6250000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560692293/2500000000 : ℝ)^2079 ≤ (13761335576261/100000000000000 : ℝ)^1567 := by
    have hnat : (560692293 : ℕ)^2079*100000000000000^1567 ≤ 13761335576261^1567*2500000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560692293 2500000000 13761335576261 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53453361/100000000 : ℝ), (2631752459/5000000000 : ℝ), (-560692293/2500000000 : ℝ)] ![(43560599611787/100000000000000 : ℝ), (2667379049423/6250000000000 : ℝ), (13761335576261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53453361/100000000 : ℝ)|^2079 ≤ (43560599611787/100000000000000 : ℝ)^1567
        have hw : |(53453361/100000000 : ℝ)|=(53453361/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631752459/5000000000 : ℝ)|^2079 ≤ (2667379049423/6250000000000 : ℝ)^1567
        have hw : |(2631752459/5000000000 : ℝ)|=(2631752459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560692293/2500000000 : ℝ)|^2079 ≤ (13761335576261/100000000000000 : ℝ)^1567
        have hw : |(-560692293/2500000000 : ℝ)|=(560692293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s5_3 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (873450829/2000000000 : ℝ)*x 0 + (1059620891/2500000000 : ℝ)*x 1 + (4499936489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873450829/2000000000 : ℝ)^2079 ≤ (16657911363697/50000000000000 : ℝ)^1567 := by
    have hnat : (873450829 : ℕ)^2079*50000000000000^1567 ≤ 16657911363697^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873450829 2000000000 16657911363697 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059620891/2500000000 : ℝ)^2079 ≤ (1600942166589/5000000000000 : ℝ)^1567 := by
    have hnat : (1059620891 : ℕ)^2079*5000000000000^1567 ≤ 1600942166589^1567*2500000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059620891 2500000000 1600942166589 5000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499936489/10000000000 : ℝ)^2079 ≤ (1386613356779/4000000000000 : ℝ)^1567 := by
    have hnat : (4499936489 : ℕ)^2079*4000000000000^1567 ≤ 1386613356779^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499936489 10000000000 1386613356779 4000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873450829/2000000000 : ℝ), (1059620891/2500000000 : ℝ), (4499936489/10000000000 : ℝ)] ![(16657911363697/50000000000000 : ℝ), (1600942166589/5000000000000 : ℝ), (1386613356779/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873450829/2000000000 : ℝ)|^2079 ≤ (16657911363697/50000000000000 : ℝ)^1567
        have hw : |(873450829/2000000000 : ℝ)|=(873450829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059620891/2500000000 : ℝ)|^2079 ≤ (1600942166589/5000000000000 : ℝ)^1567
        have hw : |(1059620891/2500000000 : ℝ)|=(1059620891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499936489/10000000000 : ℝ)|^2079 ≤ (1386613356779/4000000000000 : ℝ)^1567
        have hw : |(4499936489/10000000000 : ℝ)|=(4499936489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s5_4 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-43516659/200000000 : ℝ)*x 0 + (5263846451/10000000000 : ℝ)*x 1 + (674384003/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43516659/200000000 : ℝ)^2079 ≤ (6609551539329/50000000000000 : ℝ)^1567 := by
    have hnat : (43516659 : ℕ)^2079*50000000000000^1567 ≤ 6609551539329^1567*200000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43516659 200000000 6609551539329 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263846451/10000000000 : ℝ)^2079 ≤ (10670434725827/25000000000000 : ℝ)^1567 := by
    have hnat : (5263846451 : ℕ)^2079*25000000000000^1567 ≤ 10670434725827^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263846451 10000000000 10670434725827 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674384003/1250000000 : ℝ)^2079 ≤ (44099158012599/100000000000000 : ℝ)^1567 := by
    have hnat : (674384003 : ℕ)^2079*100000000000000^1567 ≤ 44099158012599^1567*1250000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674384003 1250000000 44099158012599 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43516659/200000000 : ℝ), (5263846451/10000000000 : ℝ), (674384003/1250000000 : ℝ)] ![(6609551539329/50000000000000 : ℝ), (10670434725827/25000000000000 : ℝ), (44099158012599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43516659/200000000 : ℝ)|^2079 ≤ (6609551539329/50000000000000 : ℝ)^1567
        have hw : |(-43516659/200000000 : ℝ)|=(43516659/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263846451/10000000000 : ℝ)|^2079 ≤ (10670434725827/25000000000000 : ℝ)^1567
        have hw : |(5263846451/10000000000 : ℝ)|=(5263846451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674384003/1250000000 : ℝ)|^2079 ≤ (44099158012599/100000000000000 : ℝ)^1567
        have hw : |(674384003/1250000000 : ℝ)|=(674384003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s5_5 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655982057/5000000000 : ℝ)*x 0 + (-2111202087/10000000000 : ℝ)*x 1 + (5395071943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655982057/5000000000 : ℝ)^2079 ≤ (43200151653029/100000000000000 : ℝ)^1567 := by
    have hnat : (2655982057 : ℕ)^2079*100000000000000^1567 ≤ 43200151653029^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655982057 5000000000 43200151653029 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111202087/10000000000 : ℝ)^2079 ≤ (12700691191567/100000000000000 : ℝ)^1567 := by
    have hnat : (2111202087 : ℕ)^2079*100000000000000^1567 ≤ 12700691191567^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111202087 10000000000 12700691191567 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395071943/10000000000 : ℝ)^2079 ≤ (1378098660443/3125000000000 : ℝ)^1567 := by
    have hnat : (5395071943 : ℕ)^2079*3125000000000^1567 ≤ 1378098660443^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395071943 10000000000 1378098660443 3125000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655982057/5000000000 : ℝ), (-2111202087/10000000000 : ℝ), (5395071943/10000000000 : ℝ)] ![(43200151653029/100000000000000 : ℝ), (12700691191567/100000000000000 : ℝ), (1378098660443/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655982057/5000000000 : ℝ)|^2079 ≤ (43200151653029/100000000000000 : ℝ)^1567
        have hw : |(2655982057/5000000000 : ℝ)|=(2655982057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2111202087/10000000000 : ℝ)|^2079 ≤ (12700691191567/100000000000000 : ℝ)^1567
        have hw : |(-2111202087/10000000000 : ℝ)|=(2111202087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395071943/10000000000 : ℝ)|^2079 ≤ (1378098660443/3125000000000 : ℝ)^1567
        have hw : |(5395071943/10000000000 : ℝ)|=(5395071943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s5_6 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655982037/5000000000 : ℝ)*x 0 + (5395071997/10000000000 : ℝ)*x 1 + (-2111202069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655982037/5000000000 : ℝ)^2079 ≤ (8640030244287/20000000000000 : ℝ)^1567 := by
    have hnat : (2655982037 : ℕ)^2079*20000000000000^1567 ≤ 8640030244287^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655982037 5000000000 8640030244287 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395071997/10000000000 : ℝ)^2079 ≤ (44099157719791/100000000000000 : ℝ)^1567 := by
    have hnat : (5395071997 : ℕ)^2079*100000000000000^1567 ≤ 44099157719791^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395071997 10000000000 44099157719791 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111202069/10000000000 : ℝ)^2079 ≤ (127006910479/1000000000000 : ℝ)^1567 := by
    have hnat : (2111202069 : ℕ)^2079*1000000000000^1567 ≤ 127006910479^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111202069 10000000000 127006910479 1000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655982037/5000000000 : ℝ), (5395071997/10000000000 : ℝ), (-2111202069/10000000000 : ℝ)] ![(8640030244287/20000000000000 : ℝ), (44099157719791/100000000000000 : ℝ), (127006910479/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655982037/5000000000 : ℝ)|^2079 ≤ (8640030244287/20000000000000 : ℝ)^1567
        have hw : |(2655982037/5000000000 : ℝ)|=(2655982037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395071997/10000000000 : ℝ)|^2079 ≤ (44099157719791/100000000000000 : ℝ)^1567
        have hw : |(5395071997/10000000000 : ℝ)|=(5395071997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111202069/10000000000 : ℝ)|^2079 ≤ (127006910479/1000000000000 : ℝ)^1567
        have hw : |(-2111202069/10000000000 : ℝ)|=(2111202069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s5_7 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (873453001/2000000000 : ℝ)*x 0 + (4499259911/10000000000 : ℝ)*x 1 + (529895313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873453001/2000000000 : ℝ)^2079 ≤ (8328983160637/25000000000000 : ℝ)^1567 := by
    have hnat : (873453001 : ℕ)^2079*25000000000000^1567 ≤ 8328983160637^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873453001 2000000000 8328983160637 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499259911/10000000000 : ℝ)^2079 ≤ (6931683817281/20000000000000 : ℝ)^1567 := by
    have hnat : (4499259911 : ℕ)^2079*20000000000000^1567 ≤ 6931683817281^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499259911 10000000000 6931683817281 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529895313/1250000000 : ℝ)^2079 ≤ (6405129651501/20000000000000 : ℝ)^1567 := by
    have hnat : (529895313 : ℕ)^2079*20000000000000^1567 ≤ 6405129651501^1567*1250000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529895313 1250000000 6405129651501 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873453001/2000000000 : ℝ), (4499259911/10000000000 : ℝ), (529895313/1250000000 : ℝ)] ![(8328983160637/25000000000000 : ℝ), (6931683817281/20000000000000 : ℝ), (6405129651501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873453001/2000000000 : ℝ)|^2079 ≤ (8328983160637/25000000000000 : ℝ)^1567
        have hw : |(873453001/2000000000 : ℝ)|=(873453001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499259911/10000000000 : ℝ)|^2079 ≤ (6931683817281/20000000000000 : ℝ)^1567
        have hw : |(4499259911/10000000000 : ℝ)|=(4499259911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529895313/1250000000 : ℝ)|^2079 ≤ (6405129651501/20000000000000 : ℝ)^1567
        have hw : |(529895313/1250000000 : ℝ)|=(529895313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1123_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11287/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11139/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11139/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11139/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11139/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11139/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11139/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11139/100000 : ℝ) ^ (8315/2048 : ℝ) ≤ (421686561407239/3125000000000000000 : ℝ) := by
    have hpowers : (11139/100000 : ℝ)^8315 ≤ (421686561407239/3125000000000000000 : ℝ)^2048 := by
      have hnat : (11139 : ℕ)^8315*3125000000000000000^2048 ≤ 421686561407239^2048*100000^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11139 100000 421686561407239 3125000000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11139/100000 : ℝ)) (X := (421686561407239/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8315/2048 : ℝ) ≤ (18267351866363033/50000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8315 ≤ (18267351866363033/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8315*50000000000000000000^2048 ≤ 18267351866363033^2048*25000^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 18267351866363033 50000000000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (18267351866363033/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562921686561407239/1562500000000000000 : ℝ) ≤ (500033232519881/500000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (1562921686561407239/1562500000000000000 : ℝ)^2048 ≤ (500033232519881/500000000000000 : ℝ)^8315 := by
      have hnat : (1562921686561407239 : ℕ)^2048*500000000000000^8315 ≤ 500033232519881^8315*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562921686561407239 1562500000000000000 500033232519881 500000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500033232519881/500000000000000 : ℝ)) (X := (1562921686561407239/1562500000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025014336848878857/50000000000000000000 : ℝ) ≤ (1250153997914269/1250000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (50025014336848878857/50000000000000000000 : ℝ)^2048 ≤ (1250153997914269/1250000000000000 : ℝ)^8315 := by
      have hnat : (50025014336848878857 : ℕ)^2048*1250000000000000^8315 ≤ 1250153997914269^8315*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025014336848878857 50000000000000000000 1250153997914269 1250000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250153997914269/1250000000000000 : ℝ)) (X := (50025014336848878857/50000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018267351866363033/25000000000000000000 : ℝ) ≤ (2500449829057671/2500000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (25018267351866363033/25000000000000000000 : ℝ)^2048 ≤ (2500449829057671/2500000000000000 : ℝ)^8315 := by
      have hnat : (25018267351866363033 : ℕ)^2048*2500000000000000^8315 ≤ 2500449829057671^8315*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018267351866363033 25000000000000000000 2500449829057671 2500000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500449829057671/2500000000000000 : ℝ)) (X := (25018267351866363033/25000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(421686561407239/3125000000000000000 : ℝ) ≤ ((7739854844891732311/7742500000000000000 : ℝ)+2*(141833229133/77425000000000 : ℝ)*(11139/100000 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (7739854844891732311/7742500000000000000 : ℝ)+2*(141833229133/77425000000000 : ℝ)*(11139/100000 : ℝ)=(500033232519881/500000000000000 : ℝ) by norm_num, show 1+2*(421686561407239/3125000000000000000 : ℝ)=(1562921686561407239/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18267351866363033/50000000000000000000 : ℝ)+(421686561407239/3125000000000000000 : ℝ) ≤ ((7739854844891732311/7742500000000000000 : ℝ)+(141833229133/77425000000000 : ℝ)*((3559/25000 : ℝ)+(11139/100000 : ℝ)))^(8315/2048 : ℝ) := by
    rw [show (7739854844891732311/7742500000000000000 : ℝ)+(141833229133/77425000000000 : ℝ)*((3559/25000 : ℝ)+(11139/100000 : ℝ))=(1250153997914269/1250000000000000 : ℝ) by norm_num, show 1+(18267351866363033/50000000000000000000 : ℝ)+(421686561407239/3125000000000000000 : ℝ)=(50025014336848878857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18267351866363033/50000000000000000000 : ℝ) ≤ ((7739854844891732311/7742500000000000000 : ℝ)+2*(141833229133/77425000000000 : ℝ)*(3559/25000 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (7739854844891732311/7742500000000000000 : ℝ)+2*(141833229133/77425000000000 : ℝ)*(3559/25000 : ℝ)=(2500449829057671/2500000000000000 : ℝ) by norm_num, show 1+2*(18267351866363033/50000000000000000000 : ℝ)=(25018267351866363033/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7739854844891732311/7742500000000000000 : ℝ)*(X 1 0+X 2 0)+(141833229133/77425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (11139/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7739854844891732311/7742500000000000000 : ℝ)) (alpha := (141833229133/77425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7739854844891732311/7742500000000000000 : ℝ)*(X 0 1+X 2 1)+(141833229133/77425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (11139/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7739854844891732311/7742500000000000000 : ℝ)) (alpha := (141833229133/77425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7739854844891732311/7742500000000000000 : ℝ)*(X 0 2+X 1 2)+(141833229133/77425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (11139/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7739854844891732311/7742500000000000000 : ℝ)) (alpha := (141833229133/77425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2175827969/10000000000 : ℝ)*X 0 0+(5395414447/10000000000 : ℝ)*X 0 1+(2631752493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069067267/2000000000 : ℝ)*X 1 0+(-2242769109/10000000000 : ℝ)*X 1 1+(526350473/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53453361/100000000 : ℝ)*X 2 0+(2631752459/5000000000 : ℝ)*X 2 1+(-560692293/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873450829/2000000000 : ℝ)*X 0 0+(1059620891/2500000000 : ℝ)*X 0 1+(4499936489/10000000000 : ℝ)*X 0 2+(873450829/2000000000 : ℝ)*X 1 0+(1059620891/2500000000 : ℝ)*X 1 1+(4499936489/10000000000 : ℝ)*X 1 2+(873450829/2000000000 : ℝ)*X 2 0+(1059620891/2500000000 : ℝ)*X 2 1+(4499936489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-43516659/200000000 : ℝ)*X 0 0+(5263846451/10000000000 : ℝ)*X 0 1+(674384003/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655982057/5000000000 : ℝ)*X 1 0+(-2111202087/10000000000 : ℝ)*X 1 1+(5395071943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655982037/5000000000 : ℝ)*X 2 0+(5395071997/10000000000 : ℝ)*X 2 1+(-2111202069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873453001/2000000000 : ℝ)*X 0 0+(4499259911/10000000000 : ℝ)*X 0 1+(529895313/1250000000 : ℝ)*X 0 2+(873453001/2000000000 : ℝ)*X 1 0+(4499259911/10000000000 : ℝ)*X 1 1+(529895313/1250000000 : ℝ)*X 1 2+(873453001/2000000000 : ℝ)*X 2 0+(4499259911/10000000000 : ℝ)*X 2 1+(529895313/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (502352293215694308885575133/96781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (263854813/12500000000000 : ℝ)*(base19) + (60153511/4000000000000 : ℝ)*(base23) + (15031897/20000000000000 : ℝ)*(upper2) + (35918389/10000000000000 : ℝ)*(upper3) + (110733677/50000000000000 : ℝ)*(upper4) + (2851466481345849/50000000000000 : ℝ)*(major0) + (2851466481345849/50000000000000 : ℝ)*(major1) + (2851466481345849/50000000000000 : ℝ)*(major2) + (7581007368531957/100000000000000 : ℝ)*(sp0) + (1516207839547583/20000000000000 : ℝ)*(sp1) + (1895259951184661/25000000000000 : ℝ)*(sp2) + (956199739888353/25000000000000 : ℝ)*(sp3) + (33940044463/100000000000000 : ℝ)*(sp4) + (6371058429/25000000000000 : ℝ)*(sp7) + (478103055473391/12500000000000 : ℝ)*(f.failure) + (379052065428821/5000000000000 : ℝ)*(f.sum) + (119105597829891/15485000000000000000000000000 : ℝ)*base65 + (1567396003775772961/387125000000000000000000000000000 : ℝ)*base68 + (625023405902977039/387125000000000000000000000000000 : ℝ)*base69 + (5121647983840102039/387125000000000000000000000000000 : ℝ)*base71 + (17013429940471/15485000000000000000000000000 : ℝ)*base73 + (4463136575916477039/387125000000000000000000000000000 : ℝ)*base75 + (2031768422355727039/387125000000000000000000000000000 : ℝ)*base77 + (339226520324227039/387125000000000000000000000000000 : ℝ)*base79 + (21645564974449/3871250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (481383/125000000000000000000 : ℝ)*base89 + (481383/125000000000000000000 : ℝ)*base91 + (481383/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2638647077256868004727663291/387125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (267774453/25000000000000 : ℝ)*(base19) + (615568869/50000000000000 : ℝ)*(base23) + (1464629/1562500000000 : ℝ)*(upper3) + (3720771/4000000000000 : ℝ)*(lower4) + (64321683/100000000000000 : ℝ)*(upper5) + (5732587429046727/100000000000000 : ℝ)*(major0) + (5732587429046727/100000000000000 : ℝ)*(major1) + (5732587429046727/100000000000000 : ℝ)*(major2) + (25672873559/100000000000000 : ℝ)*(sp1) + (16203883067/50000000000000 : ℝ)*(sp2) + (7620461626513777/100000000000000 : ℝ)*(sp4) + (3810217441271203/50000000000000 : ℝ)*(sp5) + (3810213993804953/50000000000000 : ℝ)*(sp6) + (961178251094851/25000000000000 : ℝ)*(sp7) + (961178251094851/25000000000000 : ℝ)*(f.failure) + (7620461626513777/100000000000000 : ℝ)*(f.sum) + (66004880310593/7742500000000000000000000000 : ℝ)*base66 + (2262085175492046097/774250000000000000000000000000000 : ℝ)*base67 + (2615623078738203903/774250000000000000000000000000000 : ℝ)*base70 + (4703774790634453903/774250000000000000000000000000000 : ℝ)*base72 + (160557564727871/15485000000000000000000000000 : ℝ)*base74 + (4613181959971796097/774250000000000000000000000000000 : ℝ)*base75 + (4461798356838203903/774250000000000000000000000000000 : ℝ)*base78 + (6997320676032703903/774250000000000000000000000000000 : ℝ)*base80 + (30291408140213/7742500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3598363/250000000000000000000 : ℝ)*base89 + (3598363/250000000000000000000 : ℝ)*base91 + (3598363/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1123_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11287/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1123_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1123_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (207/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11287/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1123_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1123_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1123_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (207/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11287/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1123_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
