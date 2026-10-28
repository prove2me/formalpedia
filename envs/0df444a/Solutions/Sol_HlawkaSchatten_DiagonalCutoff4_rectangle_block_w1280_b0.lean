-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1280_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:22:57.606902+00:00
-- url     : https://prove2.me/submissions/82b3c05b-85a6-4e9a-9116-cd43b3a05536

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
theorem support_rectangle_w1280_s0_0 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1846373679/10000000000 : ℝ)*x 0 + (240965109/400000000 : ℝ)*x 1 + (2397951279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1846373679/10000000000 : ℝ)^265 ≤ (10782263001759/100000000000000 : ℝ)^201 := by
    have hnat : (1846373679 : ℕ)^265*100000000000000^201 ≤ 10782263001759^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846373679 10000000000 10782263001759 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240965109/400000000 : ℝ)^265 ≤ (6407973932389/12500000000000 : ℝ)^201 := by
    have hnat : (240965109 : ℕ)^265*12500000000000^201 ≤ 6407973932389^201*400000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240965109 400000000 6407973932389 12500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397951279/5000000000 : ℝ)^265 ≤ (37953945525783/100000000000000 : ℝ)^201 := by
    have hnat : (2397951279 : ℕ)^265*100000000000000^201 ≤ 37953945525783^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397951279 5000000000 37953945525783 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1846373679/10000000000 : ℝ), (240965109/400000000 : ℝ), (2397951279/5000000000 : ℝ)] ![(10782263001759/100000000000000 : ℝ), (6407973932389/12500000000000 : ℝ), (37953945525783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1846373679/10000000000 : ℝ)|^265 ≤ (10782263001759/100000000000000 : ℝ)^201
        have hw : |(-1846373679/10000000000 : ℝ)|=(1846373679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(240965109/400000000 : ℝ)|^265 ≤ (6407973932389/12500000000000 : ℝ)^201
        have hw : |(240965109/400000000 : ℝ)|=(240965109/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397951279/5000000000 : ℝ)|^265 ≤ (37953945525783/100000000000000 : ℝ)^201
        have hw : |(2397951279/5000000000 : ℝ)|=(2397951279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s0_1 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5508765523/10000000000 : ℝ)*x 0 + (-20381591/80000000 : ℝ)*x 1 + (74935977/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5508765523/10000000000 : ℝ)^265 ≤ (1139052967419/2500000000000 : ℝ)^201 := by
    have hnat : (5508765523 : ℕ)^265*2500000000000^201 ≤ 1139052967419^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508765523 10000000000 1139052967419 2500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20381591/80000000 : ℝ)^265 ≤ (4120984018923/25000000000000 : ℝ)^201 := by
    have hnat : (20381591 : ℕ)^265*25000000000000^201 ≤ 4120984018923^201*80000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20381591 80000000 4120984018923 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74935977/156250000 : ℝ)^265 ≤ (18976972606387/50000000000000 : ℝ)^201 := by
    have hnat : (74935977 : ℕ)^265*50000000000000^201 ≤ 18976972606387^201*156250000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74935977 156250000 18976972606387 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5508765523/10000000000 : ℝ), (-20381591/80000000 : ℝ), (74935977/156250000 : ℝ)] ![(1139052967419/2500000000000 : ℝ), (4120984018923/25000000000000 : ℝ), (18976972606387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5508765523/10000000000 : ℝ)|^265 ≤ (1139052967419/2500000000000 : ℝ)^201
        have hw : |(5508765523/10000000000 : ℝ)|=(5508765523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20381591/80000000 : ℝ)|^265 ≤ (4120984018923/25000000000000 : ℝ)^201
        have hw : |(-20381591/80000000 : ℝ)|=(20381591/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74935977/156250000 : ℝ)|^265 ≤ (18976972606387/50000000000000 : ℝ)^201
        have hw : |(74935977/156250000 : ℝ)|=(74935977/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s0_2 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2754382771/5000000000 : ℝ)*x 0 + (4795902531/10000000000 : ℝ)*x 1 + (-2547698847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2754382771/5000000000 : ℝ)^265 ≤ (22781059451971/50000000000000 : ℝ)^201 := by
    have hnat : (2754382771 : ℕ)^265*50000000000000^201 ≤ 22781059451971^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754382771 5000000000 22781059451971 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4795902531/10000000000 : ℝ)^265 ≤ (1518157809763/4000000000000 : ℝ)^201 := by
    have hnat : (4795902531 : ℕ)^265*4000000000000^201 ≤ 1518157809763^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795902531 10000000000 1518157809763 4000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547698847/10000000000 : ℝ)^265 ≤ (3296787167369/20000000000000 : ℝ)^201 := by
    have hnat : (2547698847 : ℕ)^265*20000000000000^201 ≤ 3296787167369^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547698847 10000000000 3296787167369 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2754382771/5000000000 : ℝ), (4795902531/10000000000 : ℝ), (-2547698847/10000000000 : ℝ)] ![(22781059451971/50000000000000 : ℝ), (1518157809763/4000000000000 : ℝ), (3296787167369/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2754382771/5000000000 : ℝ)|^265 ≤ (22781059451971/50000000000000 : ℝ)^201
        have hw : |(2754382771/5000000000 : ℝ)|=(2754382771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4795902531/10000000000 : ℝ)|^265 ≤ (1518157809763/4000000000000 : ℝ)^201
        have hw : |(4795902531/10000000000 : ℝ)|=(4795902531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2547698847/10000000000 : ℝ)|^265 ≤ (3296787167369/20000000000000 : ℝ)^201
        have hw : |(-2547698847/10000000000 : ℝ)|=(2547698847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s0_3 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4188182479/10000000000 : ℝ)*x 0 + (1555120623/5000000000 : ℝ)*x 1 + (5622965501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4188182479/10000000000 : ℝ)^265 ≤ (6349002998397/20000000000000 : ℝ)^201 := by
    have hnat : (4188182479 : ℕ)^265*20000000000000^201 ≤ 6349002998397^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188182479 10000000000 6349002998397 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1555120623/5000000000 : ℝ)^265 ≤ (4288700006743/20000000000000 : ℝ)^201 := by
    have hnat : (1555120623 : ℕ)^265*20000000000000^201 ≤ 4288700006743^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555120623 5000000000 4288700006743 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5622965501/10000000000 : ℝ)^265 ≤ (23405742476639/50000000000000 : ℝ)^201 := by
    have hnat : (5622965501 : ℕ)^265*50000000000000^201 ≤ 23405742476639^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5622965501 10000000000 23405742476639 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4188182479/10000000000 : ℝ), (1555120623/5000000000 : ℝ), (5622965501/10000000000 : ℝ)] ![(6349002998397/20000000000000 : ℝ), (4288700006743/20000000000000 : ℝ), (23405742476639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4188182479/10000000000 : ℝ)|^265 ≤ (6349002998397/20000000000000 : ℝ)^201
        have hw : |(4188182479/10000000000 : ℝ)|=(4188182479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1555120623/5000000000 : ℝ)|^265 ≤ (4288700006743/20000000000000 : ℝ)^201
        have hw : |(1555120623/5000000000 : ℝ)|=(1555120623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5622965501/10000000000 : ℝ)|^265 ≤ (23405742476639/50000000000000 : ℝ)^201
        have hw : |(5622965501/10000000000 : ℝ)|=(5622965501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s0_4 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1851164013/10000000000 : ℝ)*x 0 + (1206904981/2500000000 : ℝ)*x 1 + (149782081/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1851164013/10000000000 : ℝ)^265 ≤ (10819159502003/100000000000000 : ℝ)^201 := by
    have hnat : (1851164013 : ℕ)^265*100000000000000^201 ≤ 10819159502003^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851164013 10000000000 10819159502003 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206904981/2500000000 : ℝ)^265 ≤ (38285221428763/100000000000000 : ℝ)^201 := by
    have hnat : (1206904981 : ℕ)^265*100000000000000^201 ≤ 38285221428763^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206904981 2500000000 38285221428763 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149782081/250000000 : ℝ)^265 ≤ (25447809531821/50000000000000 : ℝ)^201 := by
    have hnat : (149782081 : ℕ)^265*50000000000000^201 ≤ 25447809531821^201*250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149782081 250000000 25447809531821 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1851164013/10000000000 : ℝ), (1206904981/2500000000 : ℝ), (149782081/250000000 : ℝ)] ![(10819159502003/100000000000000 : ℝ), (38285221428763/100000000000000 : ℝ), (25447809531821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1851164013/10000000000 : ℝ)|^265 ≤ (10819159502003/100000000000000 : ℝ)^201
        have hw : |(-1851164013/10000000000 : ℝ)|=(1851164013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206904981/2500000000 : ℝ)|^265 ≤ (38285221428763/100000000000000 : ℝ)^201
        have hw : |(1206904981/2500000000 : ℝ)|=(1206904981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149782081/250000000 : ℝ)|^265 ≤ (25447809531821/50000000000000 : ℝ)^201
        have hw : |(149782081/250000000 : ℝ)|=(149782081/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s0_5 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5174482859/10000000000 : ℝ)*x 0 + (-1352315737/10000000000 : ℝ)*x 1 + (5991285739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174482859/10000000000 : ℝ)^265 ≤ (41952699634079/100000000000000 : ℝ)^201 := by
    have hnat : (5174482859 : ℕ)^265*100000000000000^201 ≤ 41952699634079^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174482859 10000000000 41952699634079 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352315737/10000000000 : ℝ)^265 ≤ (3575826653469/50000000000000 : ℝ)^201 := by
    have hnat : (1352315737 : ℕ)^265*50000000000000^201 ≤ 3575826653469^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352315737 10000000000 3575826653469 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5991285739/10000000000 : ℝ)^265 ≤ (1017912941039/2000000000000 : ℝ)^201 := by
    have hnat : (5991285739 : ℕ)^265*2000000000000^201 ≤ 1017912941039^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5991285739 10000000000 1017912941039 2000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174482859/10000000000 : ℝ), (-1352315737/10000000000 : ℝ), (5991285739/10000000000 : ℝ)] ![(41952699634079/100000000000000 : ℝ), (3575826653469/50000000000000 : ℝ), (1017912941039/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174482859/10000000000 : ℝ)|^265 ≤ (41952699634079/100000000000000 : ℝ)^201
        have hw : |(5174482859/10000000000 : ℝ)|=(5174482859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1352315737/10000000000 : ℝ)|^265 ≤ (3575826653469/50000000000000 : ℝ)^201
        have hw : |(-1352315737/10000000000 : ℝ)|=(1352315737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5991285739/10000000000 : ℝ)|^265 ≤ (1017912941039/2000000000000 : ℝ)^201
        have hw : |(5991285739/10000000000 : ℝ)|=(5991285739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s0_6 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5174484057/10000000000 : ℝ)*x 0 + (5991283659/10000000000 : ℝ)*x 1 + (-33807931/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174484057/10000000000 : ℝ)^265 ≤ (41952712439669/100000000000000 : ℝ)^201 := by
    have hnat : (5174484057 : ℕ)^265*100000000000000^201 ≤ 41952712439669^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174484057 10000000000 41952712439669 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5991283659/10000000000 : ℝ)^265 ≤ (50895623756359/100000000000000 : ℝ)^201 := by
    have hnat : (5991283659 : ℕ)^265*100000000000000^201 ≤ 50895623756359^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5991283659 10000000000 50895623756359 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33807931/250000000 : ℝ)^265 ≤ (3575831893179/50000000000000 : ℝ)^201 := by
    have hnat : (33807931 : ℕ)^265*50000000000000^201 ≤ 3575831893179^201*250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33807931 250000000 3575831893179 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174484057/10000000000 : ℝ), (5991283659/10000000000 : ℝ), (-33807931/250000000 : ℝ)] ![(41952712439669/100000000000000 : ℝ), (50895623756359/100000000000000 : ℝ), (3575831893179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174484057/10000000000 : ℝ)|^265 ≤ (41952712439669/100000000000000 : ℝ)^201
        have hw : |(5174484057/10000000000 : ℝ)|=(5174484057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5991283659/10000000000 : ℝ)|^265 ≤ (50895623756359/100000000000000 : ℝ)^201
        have hw : |(5991283659/10000000000 : ℝ)|=(5991283659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33807931/250000000 : ℝ)|^265 ≤ (3575831893179/50000000000000 : ℝ)^201
        have hw : |(-33807931/250000000 : ℝ)|=(33807931/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s0_7 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2098993257/5000000000 : ℝ)*x 0 + (5558084087/10000000000 : ℝ)*x 1 + (635485723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098993257/5000000000 : ℝ)^265 ≤ (31843024079553/100000000000000 : ℝ)^201 := by
    have hnat : (2098993257 : ℕ)^265*100000000000000^201 ≤ 31843024079553^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098993257 5000000000 31843024079553 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5558084087/10000000000 : ℝ)^265 ≤ (5762583764569/12500000000000 : ℝ)^201 := by
    have hnat : (5558084087 : ℕ)^265*12500000000000^201 ≤ 5762583764569^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5558084087 10000000000 5762583764569 12500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635485723/2000000000 : ℝ)^265 ≤ (22056305791169/100000000000000 : ℝ)^201 := by
    have hnat : (635485723 : ℕ)^265*100000000000000^201 ≤ 22056305791169^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635485723 2000000000 22056305791169 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098993257/5000000000 : ℝ), (5558084087/10000000000 : ℝ), (635485723/2000000000 : ℝ)] ![(31843024079553/100000000000000 : ℝ), (5762583764569/12500000000000 : ℝ), (22056305791169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098993257/5000000000 : ℝ)|^265 ≤ (31843024079553/100000000000000 : ℝ)^201
        have hw : |(2098993257/5000000000 : ℝ)|=(2098993257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5558084087/10000000000 : ℝ)|^265 ≤ (5762583764569/12500000000000 : ℝ)^201
        have hw : |(5558084087/10000000000 : ℝ)|=(5558084087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635485723/2000000000 : ℝ)|^265 ≤ (22056305791169/100000000000000 : ℝ)^201
        have hw : |(635485723/2000000000 : ℝ)|=(635485723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1280_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (939/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6831/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4239/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4239 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4239*1^1024 ≤ 0^1024*1^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4239/1024 : ℝ) ≤ (2252517972744780419/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4239 ≤ (2252517972744780419/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4239*100000000000000000000^1024 ≤ 2252517972744780419^1024*5^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2252517972744780419 100000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2252517972744780419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4239 := by
      have hnat : (1 : ℕ)^1024*1^4239 ≤ 1^4239*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102252517972744780419/100000000000000000000 : ℝ) ≤ (2513488629047363/2500000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (102252517972744780419/100000000000000000000 : ℝ)^1024 ≤ (2513488629047363/2500000000000000 : ℝ)^4239 := by
      have hnat : (102252517972744780419 : ℕ)^1024*2500000000000000^4239 ≤ 2513488629047363^4239*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102252517972744780419 100000000000000000000 2513488629047363 2500000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513488629047363/2500000000000000 : ℝ)) (X := (102252517972744780419/100000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52252517972744780419/50000000000000000000 : ℝ) ≤ (1263488629047363/1250000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (52252517972744780419/50000000000000000000 : ℝ)^1024 ≤ (1263488629047363/1250000000000000 : ℝ)^4239 := by
      have hnat : (52252517972744780419 : ℕ)^1024*1250000000000000^4239 ≤ 1263488629047363^4239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52252517972744780419 50000000000000000000 1263488629047363 1250000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1263488629047363/1250000000000000 : ℝ)) (X := (52252517972744780419/50000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(13488629047363/1000000000000000 : ℝ)*(0 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(13488629047363/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2252517972744780419/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(13488629047363/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4239/1024 : ℝ) := by
    rw [show (1 : ℝ)+(13488629047363/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2513488629047363/2500000000000000 : ℝ) by norm_num, show 1+(2252517972744780419/100000000000000000000 : ℝ)+(0 : ℝ)=(102252517972744780419/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2252517972744780419/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(13488629047363/1000000000000000 : ℝ)*(2/5 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(13488629047363/1000000000000000 : ℝ)*(2/5 : ℝ)=(1263488629047363/1250000000000000 : ℝ) by norm_num, show 1+2*(2252517972744780419/100000000000000000000 : ℝ)=(52252517972744780419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(13488629047363/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13488629047363/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(13488629047363/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13488629047363/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(13488629047363/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13488629047363/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1846373679/10000000000 : ℝ)*X 0 0+(240965109/400000000 : ℝ)*X 0 1+(2397951279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5508765523/10000000000 : ℝ)*X 1 0+(-20381591/80000000 : ℝ)*X 1 1+(74935977/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2754382771/5000000000 : ℝ)*X 2 0+(4795902531/10000000000 : ℝ)*X 2 1+(-2547698847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4188182479/10000000000 : ℝ)*X 0 0+(1555120623/5000000000 : ℝ)*X 0 1+(5622965501/10000000000 : ℝ)*X 0 2+(4188182479/10000000000 : ℝ)*X 1 0+(1555120623/5000000000 : ℝ)*X 1 1+(5622965501/10000000000 : ℝ)*X 1 2+(4188182479/10000000000 : ℝ)*X 2 0+(1555120623/5000000000 : ℝ)*X 2 1+(5622965501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1851164013/10000000000 : ℝ)*X 0 0+(1206904981/2500000000 : ℝ)*X 0 1+(149782081/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174482859/10000000000 : ℝ)*X 1 0+(-1352315737/10000000000 : ℝ)*X 1 1+(5991285739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174484057/10000000000 : ℝ)*X 2 0+(5991283659/10000000000 : ℝ)*X 2 1+(-33807931/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2098993257/5000000000 : ℝ)*X 0 0+(5558084087/10000000000 : ℝ)*X 0 1+(635485723/2000000000 : ℝ)*X 0 2+(2098993257/5000000000 : ℝ)*X 1 0+(5558084087/10000000000 : ℝ)*X 1 1+(635485723/2000000000 : ℝ)*X 1 2+(2098993257/5000000000 : ℝ)*X 2 0+(5558084087/10000000000 : ℝ)*X 2 1+(635485723/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62649983484790253047077/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32665171/100000000000000 : ℝ)*(base1) + (153064423/25000000000000 : ℝ)*(base19) + (615065859/100000000000000 : ℝ)*(base23) + (67578053/100000000000000 : ℝ)*(upper3) + (37706369/50000000000000 : ℝ)*(upper5) + (303040754121323/50000000000000 : ℝ)*(major0) + (303040754121323/50000000000000 : ℝ)*(major1) + (606081508242647/100000000000000 : ℝ)*(major2) + (16283695093623/2000000000000 : ℝ)*(sp0) + (814186058412501/100000000000000 : ℝ)*(sp1) + (407093027802167/50000000000000 : ℝ)*(sp2) + (99493828693319/25000000000000 : ℝ)*(sp3) + (974327107/50000000000000 : ℝ)*(sp4) + (114355417/12500000000000 : ℝ)*(sp7) + (397976262281783/100000000000000 : ℝ)*(f.failure) + (814186670670193/100000000000000 : ℝ)*(f.sum) + (243451937667641/100000000000000000000000000000 : ℝ)*base66 + (635782101910139/100000000000000000000000000000 : ℝ)*base68 + (101865316421249/50000000000000000000000000000 : ℝ)*base69 + (751404633610139/100000000000000000000000000000 : ℝ)*base72 + (420786885367641/100000000000000000000000000000 : ℝ)*base74 + (273877943021249/50000000000000000000000000000 : ℝ)*base75 + (457649431578751/50000000000000000000000000000 : ℝ)*base78 + (45751658878751/50000000000000000000000000000 : ℝ)*base80 + (109156585228751/25000000000000000000000000000 : ℝ)*base82 + (55939427/10000000000000000000000 : ℝ)*base89 + (55939427/10000000000000000000000 : ℝ)*base91 + (44060573/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1492389539688811129191/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (325473351/100000000000000 : ℝ)*(base1) + (88332457/10000000000000 : ℝ)*(base19) + (1051455061/100000000000000 : ℝ)*(base23) + (172810873/100000000000000 : ℝ)*(upper3) + (31985199444163/5000000000000 : ℝ)*(major0) + (31985199444163/5000000000000 : ℝ)*(major1) + (31985199444163/5000000000000 : ℝ)*(major2) + (840905677/50000000000000 : ℝ)*(sp1) + (120462607/10000000000000 : ℝ)*(sp2) + (204764267/50000000000000 : ℝ)*(sp3) + (859354077065361/100000000000000 : ℝ)*(sp4) + (429675593228043/50000000000000 : ℝ)*(sp5) + (859351495510879/100000000000000 : ℝ)*(sp6) + (420053331984403/100000000000000 : ℝ)*(sp7) + (26253379186643/6250000000000 : ℝ)*(f.failure) + (85935375159201/10000000000000 : ℝ)*(f.sum) + (250307195331/2500000000000000000000000000 : ℝ)*base66 + (26681504052831/5000000000000000000000000000 : ℝ)*base68 + (18710434202831/5000000000000000000000000000 : ℝ)*base70 + (26426573827831/5000000000000000000000000000 : ℝ)*base72 + (2581089840331/2500000000000000000000000000 : ℝ)*base74 + (51337488332831/5000000000000000000000000000 : ℝ)*base76 + (40416863962831/5000000000000000000000000000 : ℝ)*base78 + (31767288387831/5000000000000000000000000000 : ℝ)*base80 + (7677295569669/2500000000000000000000000000 : ℝ)*base81 + (662767/625000000000000000000 : ℝ)*base89 + (662767/625000000000000000000 : ℝ)*base91 + (662767/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1280_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (939/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6831/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1280_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1280_s1_0 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-408031031/2000000000 : ℝ)*x 0 + (5671098703/10000000000 : ℝ)*x 1 + (2512437473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408031031/2000000000 : ℝ)^265 ≤ (12298565650071/100000000000000 : ℝ)^201 := by
    have hnat : (408031031 : ℕ)^265*100000000000000^201 ≤ 12298565650071^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408031031 2000000000 12298565650071 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5671098703/10000000000 : ℝ)^265 ≤ (23670252347329/50000000000000 : ℝ)^201 := by
    have hnat : (5671098703 : ℕ)^265*50000000000000^201 ≤ 23670252347329^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671098703 10000000000 23670252347329 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512437473/5000000000 : ℝ)^265 ≤ (4036092965079/10000000000000 : ℝ)^201 := by
    have hnat : (2512437473 : ℕ)^265*10000000000000^201 ≤ 4036092965079^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512437473 5000000000 4036092965079 10000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408031031/2000000000 : ℝ), (5671098703/10000000000 : ℝ), (2512437473/5000000000 : ℝ)] ![(12298565650071/100000000000000 : ℝ), (23670252347329/50000000000000 : ℝ), (4036092965079/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408031031/2000000000 : ℝ)|^265 ≤ (12298565650071/100000000000000 : ℝ)^201
        have hw : |(-408031031/2000000000 : ℝ)|=(408031031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5671098703/10000000000 : ℝ)|^265 ≤ (23670252347329/50000000000000 : ℝ)^201
        have hw : |(5671098703/10000000000 : ℝ)|=(5671098703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2512437473/5000000000 : ℝ)|^265 ≤ (4036092965079/10000000000000 : ℝ)^201
        have hw : |(2512437473/5000000000 : ℝ)|=(2512437473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s1_1 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5412263831/10000000000 : ℝ)*x 0 + (-59672589/250000000 : ℝ)*x 1 + (5024874789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412263831/10000000000 : ℝ)^265 ≤ (44512777803563/100000000000000 : ℝ)^201 := by
    have hnat : (5412263831 : ℕ)^265*100000000000000^201 ≤ 44512777803563^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412263831 10000000000 44512777803563 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59672589/250000000 : ℝ)^265 ≤ (15126294199191/100000000000000 : ℝ)^201 := by
    have hnat : (59672589 : ℕ)^265*100000000000000^201 ≤ 15126294199191^201*250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59672589 250000000 15126294199191 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5024874789/10000000000 : ℝ)^265 ≤ (40360927988199/100000000000000 : ℝ)^201 := by
    have hnat : (5024874789 : ℕ)^265*100000000000000^201 ≤ 40360927988199^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024874789 10000000000 40360927988199 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412263831/10000000000 : ℝ), (-59672589/250000000 : ℝ), (5024874789/10000000000 : ℝ)] ![(44512777803563/100000000000000 : ℝ), (15126294199191/100000000000000 : ℝ), (40360927988199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412263831/10000000000 : ℝ)|^265 ≤ (44512777803563/100000000000000 : ℝ)^201
        have hw : |(5412263831/10000000000 : ℝ)|=(5412263831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-59672589/250000000 : ℝ)|^265 ≤ (15126294199191/100000000000000 : ℝ)^201
        have hw : |(-59672589/250000000 : ℝ)|=(59672589/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5024874789/10000000000 : ℝ)|^265 ≤ (40360927988199/100000000000000 : ℝ)^201
        have hw : |(5024874789/10000000000 : ℝ)|=(5024874789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s1_2 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (338266477/625000000 : ℝ)*x 0 + (628109369/1250000000 : ℝ)*x 1 + (-2386903611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338266477/625000000 : ℝ)^265 ≤ (2782048477861/6250000000000 : ℝ)^201 := by
    have hnat : (338266477 : ℕ)^265*6250000000000^201 ≤ 2782048477861^201*625000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338266477 625000000 2782048477861 6250000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (628109369/1250000000 : ℝ)^265 ≤ (5045116214291/12500000000000 : ℝ)^201 := by
    have hnat : (628109369 : ℕ)^265*12500000000000^201 ≤ 5045116214291^201*1250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628109369 1250000000 5045116214291 12500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386903611/10000000000 : ℝ)^265 ≤ (15126294625297/100000000000000 : ℝ)^201 := by
    have hnat : (2386903611 : ℕ)^265*100000000000000^201 ≤ 15126294625297^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386903611 10000000000 15126294625297 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338266477/625000000 : ℝ), (628109369/1250000000 : ℝ), (-2386903611/10000000000 : ℝ)] ![(2782048477861/6250000000000 : ℝ), (5045116214291/12500000000000 : ℝ), (15126294625297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338266477/625000000 : ℝ)|^265 ≤ (2782048477861/6250000000000 : ℝ)^201
        have hw : |(338266477/625000000 : ℝ)|=(338266477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(628109369/1250000000 : ℝ)|^265 ≤ (5045116214291/12500000000000 : ℝ)^201
        have hw : |(628109369/1250000000 : ℝ)|=(628109369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2386903611/10000000000 : ℝ)|^265 ≤ (15126294625297/100000000000000 : ℝ)^201
        have hw : |(-2386903611/10000000000 : ℝ)|=(2386903611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s1_3 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4303237207/10000000000 : ℝ)*x 0 + (14416271/39062500 : ℝ)*x 1 + (1002524217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303237207/10000000000 : ℝ)^265 ≤ (32899764590133/100000000000000 : ℝ)^201 := by
    have hnat : (4303237207 : ℕ)^265*100000000000000^201 ≤ 32899764590133^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303237207 10000000000 32899764590133 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14416271/39062500 : ℝ)^265 ≤ (13434510329857/50000000000000 : ℝ)^201 := by
    have hnat : (14416271 : ℕ)^265*50000000000000^201 ≤ 13434510329857^201*39062500^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14416271 39062500 13434510329857 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002524217/2000000000 : ℝ)^265 ≤ (2011560736543/5000000000000 : ℝ)^201 := by
    have hnat : (1002524217 : ℕ)^265*5000000000000^201 ≤ 2011560736543^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002524217 2000000000 2011560736543 5000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303237207/10000000000 : ℝ), (14416271/39062500 : ℝ), (1002524217/2000000000 : ℝ)] ![(32899764590133/100000000000000 : ℝ), (13434510329857/50000000000000 : ℝ), (2011560736543/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303237207/10000000000 : ℝ)|^265 ≤ (32899764590133/100000000000000 : ℝ)^201
        have hw : |(4303237207/10000000000 : ℝ)|=(4303237207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14416271/39062500 : ℝ)|^265 ≤ (13434510329857/50000000000000 : ℝ)^201
        have hw : |(14416271/39062500 : ℝ)|=(14416271/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002524217/2000000000 : ℝ)|^265 ≤ (2011560736543/5000000000000 : ℝ)^201
        have hw : |(1002524217/2000000000 : ℝ)|=(1002524217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s1_4 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-408163751/2000000000 : ℝ)*x 0 + (2516688599/5000000000 : ℝ)*x 1 + (5662434191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408163751/2000000000 : ℝ)^265 ≤ (6151920006121/50000000000000 : ℝ)^201 := by
    have hnat : (408163751 : ℕ)^265*50000000000000^201 ≤ 6151920006121^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408163751 2000000000 6151920006121 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516688599/5000000000 : ℝ)^265 ≤ (1264093456907/3125000000000 : ℝ)^201 := by
    have hnat : (2516688599 : ℕ)^265*3125000000000^201 ≤ 1264093456907^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516688599 5000000000 1264093456907 3125000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5662434191/10000000000 : ℝ)^265 ≤ (47245169355641/100000000000000 : ℝ)^201 := by
    have hnat : (5662434191 : ℕ)^265*100000000000000^201 ≤ 47245169355641^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662434191 10000000000 47245169355641 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408163751/2000000000 : ℝ), (2516688599/5000000000 : ℝ), (5662434191/10000000000 : ℝ)] ![(6151920006121/50000000000000 : ℝ), (1264093456907/3125000000000 : ℝ), (47245169355641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408163751/2000000000 : ℝ)|^265 ≤ (6151920006121/50000000000000 : ℝ)^201
        have hw : |(-408163751/2000000000 : ℝ)|=(408163751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2516688599/5000000000 : ℝ)|^265 ≤ (1264093456907/3125000000000 : ℝ)^201
        have hw : |(2516688599/5000000000 : ℝ)|=(2516688599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5662434191/10000000000 : ℝ)|^265 ≤ (47245169355641/100000000000000 : ℝ)^201
        have hw : |(5662434191/10000000000 : ℝ)|=(5662434191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s1_5 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1049096503/2000000000 : ℝ)*x 0 + (-1749344079/10000000000 : ℝ)*x 1 + (1132486921/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049096503/2000000000 : ℝ)^265 ≤ (42713277616797/100000000000000 : ℝ)^201 := by
    have hnat : (1049096503 : ℕ)^265*100000000000000^201 ≤ 42713277616797^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049096503 2000000000 42713277616797 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1749344079/10000000000 : ℝ)^265 ≤ (2008309693217/20000000000000 : ℝ)^201 := by
    have hnat : (1749344079 : ℕ)^265*20000000000000^201 ≤ 2008309693217^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749344079 10000000000 2008309693217 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132486921/2000000000 : ℝ)^265 ≤ (36910292117/78125000000 : ℝ)^201 := by
    have hnat : (1132486921 : ℕ)^265*78125000000^201 ≤ 36910292117^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132486921 2000000000 36910292117 78125000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049096503/2000000000 : ℝ), (-1749344079/10000000000 : ℝ), (1132486921/2000000000 : ℝ)] ![(42713277616797/100000000000000 : ℝ), (2008309693217/20000000000000 : ℝ), (36910292117/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049096503/2000000000 : ℝ)|^265 ≤ (42713277616797/100000000000000 : ℝ)^201
        have hw : |(1049096503/2000000000 : ℝ)|=(1049096503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1749344079/10000000000 : ℝ)|^265 ≤ (2008309693217/20000000000000 : ℝ)^201
        have hw : |(-1749344079/10000000000 : ℝ)|=(1749344079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132486921/2000000000 : ℝ)|^265 ≤ (36910292117/78125000000 : ℝ)^201
        have hw : |(1132486921/2000000000 : ℝ)|=(1132486921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s1_6 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (209819297/400000000 : ℝ)*x 0 + (2831217153/5000000000 : ℝ)*x 1 + (-2733351/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209819297/400000000 : ℝ)^265 ≤ (4271327665059/10000000000000 : ℝ)^201 := by
    have hnat : (209819297 : ℕ)^265*10000000000000^201 ≤ 4271327665059^201*400000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209819297 400000000 4271327665059 10000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2831217153/5000000000 : ℝ)^265 ≤ (23622585310337/50000000000000 : ℝ)^201 := by
    have hnat : (2831217153 : ℕ)^265*50000000000000^201 ≤ 23622585310337^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831217153 5000000000 23622585310337 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733351/15625000 : ℝ)^265 ≤ (2510388177919/25000000000000 : ℝ)^201 := by
    have hnat : (2733351 : ℕ)^265*25000000000000^201 ≤ 2510388177919^201*15625000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733351 15625000 2510388177919 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209819297/400000000 : ℝ), (2831217153/5000000000 : ℝ), (-2733351/15625000 : ℝ)] ![(4271327665059/10000000000000 : ℝ), (23622585310337/50000000000000 : ℝ), (2510388177919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209819297/400000000 : ℝ)|^265 ≤ (4271327665059/10000000000000 : ℝ)^201
        have hw : |(209819297/400000000 : ℝ)|=(209819297/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2831217153/5000000000 : ℝ)|^265 ≤ (23622585310337/50000000000000 : ℝ)^201
        have hw : |(2831217153/5000000000 : ℝ)|=(2831217153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2733351/15625000 : ℝ)|^265 ≤ (2510388177919/25000000000000 : ℝ)^201
        have hw : |(-2733351/15625000 : ℝ)|=(2733351/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s1_7 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (860918877/2000000000 : ℝ)*x 0 + (499522719/1000000000 : ℝ)*x 1 + (1854145501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860918877/2000000000 : ℝ)^265 ≤ (32913445215043/100000000000000 : ℝ)^201 := by
    have hnat : (860918877 : ℕ)^265*100000000000000^201 ≤ 32913445215043^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860918877 2000000000 32913445215043 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499522719/1000000000 : ℝ)^265 ≤ (10011815657529/25000000000000 : ℝ)^201 := by
    have hnat : (499522719 : ℕ)^265*25000000000000^201 ≤ 10011815657529^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499522719 1000000000 10011815657529 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1854145501/5000000000 : ℝ)^265 ≤ (27039292146189/100000000000000 : ℝ)^201 := by
    have hnat : (1854145501 : ℕ)^265*100000000000000^201 ≤ 27039292146189^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854145501 5000000000 27039292146189 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860918877/2000000000 : ℝ), (499522719/1000000000 : ℝ), (1854145501/5000000000 : ℝ)] ![(32913445215043/100000000000000 : ℝ), (10011815657529/25000000000000 : ℝ), (27039292146189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860918877/2000000000 : ℝ)|^265 ≤ (32913445215043/100000000000000 : ℝ)^201
        have hw : |(860918877/2000000000 : ℝ)|=(860918877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499522719/1000000000 : ℝ)|^265 ≤ (10011815657529/25000000000000 : ℝ)^201
        have hw : |(499522719/1000000000 : ℝ)|=(499522719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1854145501/5000000000 : ℝ)|^265 ≤ (27039292146189/100000000000000 : ℝ)^201
        have hw : |(1854145501/5000000000 : ℝ)|=(1854145501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1280_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6831/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (393/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4987/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6831/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6831/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6831/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6831/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6831/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6831/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (939/100000 : ℝ) ^ (4239/1024 : ℝ) ≤ (6329484093/1562500000000000000 : ℝ) := by
    have hpowers : (939/100000 : ℝ)^4239 ≤ (6329484093/1562500000000000000 : ℝ)^1024 := by
      have hnat : (939 : ℕ)^4239*1562500000000000000^1024 ≤ 6329484093^1024*100000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        939 100000 6329484093 1562500000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (939/100000 : ℝ)) (X := (6329484093/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6831/25000 : ℝ) ^ (4239/1024 : ℝ) ≤ (93008232435067477/20000000000000000000 : ℝ) := by
    have hpowers : (6831/25000 : ℝ)^4239 ≤ (93008232435067477/20000000000000000000 : ℝ)^1024 := by
      have hnat : (6831 : ℕ)^4239*20000000000000000000^1024 ≤ 93008232435067477^1024*25000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6831 25000 93008232435067477 20000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6831/25000 : ℝ)) (X := (93008232435067477/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781250006329484093/781250000000000000 : ℝ) ≤ (5000000009785541/5000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (781250006329484093/781250000000000000 : ℝ)^1024 ≤ (5000000009785541/5000000000000000 : ℝ)^4239 := by
      have hnat : (781250006329484093 : ℕ)^1024*5000000000000000^4239 ≤ 5000000009785541^4239*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781250006329484093 781250000000000000 5000000009785541 5000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000009785541/5000000000000000 : ℝ)) (X := (781250006329484093/781250000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100465041567262319337/100000000000000000000 : ℝ) ≤ (5005607042415197/5000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (100465041567262319337/100000000000000000000 : ℝ)^1024 ≤ (5005607042415197/5000000000000000 : ℝ)^4239 := by
      have hnat : (100465041567262319337 : ℕ)^1024*5000000000000000^4239 ≤ 5005607042415197^4239*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100465041567262319337 100000000000000000000 5005607042415197 5000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005607042415197/5000000000000000 : ℝ)) (X := (100465041567262319337/100000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10093008232435067477/10000000000000000000 : ℝ) ≤ (5011214075044853/5000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (10093008232435067477/10000000000000000000 : ℝ)^1024 ≤ (5011214075044853/5000000000000000 : ℝ)^4239 := by
      have hnat : (10093008232435067477 : ℕ)^1024*5000000000000000^4239 ≤ 5011214075044853^4239*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10093008232435067477 10000000000000000000 5011214075044853 5000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011214075044853/5000000000000000 : ℝ)) (X := (10093008232435067477/10000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6329484093/1562500000000000000 : ℝ) ≤ ((43971490083637668439/43975000000000000000 : ℝ)+2*(233626359569/54968750000000 : ℝ)*(939/100000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (43971490083637668439/43975000000000000000 : ℝ)+2*(233626359569/54968750000000 : ℝ)*(939/100000 : ℝ)=(5000000009785541/5000000000000000 : ℝ) by norm_num, show 1+2*(6329484093/1562500000000000000 : ℝ)=(781250006329484093/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(93008232435067477/20000000000000000000 : ℝ)+(6329484093/1562500000000000000 : ℝ) ≤ ((43971490083637668439/43975000000000000000 : ℝ)+(233626359569/54968750000000 : ℝ)*((6831/25000 : ℝ)+(939/100000 : ℝ)))^(4239/1024 : ℝ) := by
    rw [show (43971490083637668439/43975000000000000000 : ℝ)+(233626359569/54968750000000 : ℝ)*((6831/25000 : ℝ)+(939/100000 : ℝ))=(5005607042415197/5000000000000000 : ℝ) by norm_num, show 1+(93008232435067477/20000000000000000000 : ℝ)+(6329484093/1562500000000000000 : ℝ)=(100465041567262319337/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(93008232435067477/20000000000000000000 : ℝ) ≤ ((43971490083637668439/43975000000000000000 : ℝ)+2*(233626359569/54968750000000 : ℝ)*(6831/25000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (43971490083637668439/43975000000000000000 : ℝ)+2*(233626359569/54968750000000 : ℝ)*(6831/25000 : ℝ)=(5011214075044853/5000000000000000 : ℝ) by norm_num, show 1+2*(93008232435067477/20000000000000000000 : ℝ)=(10093008232435067477/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43971490083637668439/43975000000000000000 : ℝ)*(X 1 0+X 2 0)+(233626359569/54968750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (939/100000 : ℝ)) (hi := (6831/25000 : ℝ)) (c := (43971490083637668439/43975000000000000000 : ℝ)) (alpha := (233626359569/54968750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43971490083637668439/43975000000000000000 : ℝ)*(X 0 1+X 2 1)+(233626359569/54968750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (939/100000 : ℝ)) (hi := (6831/25000 : ℝ)) (c := (43971490083637668439/43975000000000000000 : ℝ)) (alpha := (233626359569/54968750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43971490083637668439/43975000000000000000 : ℝ)*(X 0 2+X 1 2)+(233626359569/54968750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (939/100000 : ℝ)) (hi := (6831/25000 : ℝ)) (c := (43971490083637668439/43975000000000000000 : ℝ)) (alpha := (233626359569/54968750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-408031031/2000000000 : ℝ)*X 0 0+(5671098703/10000000000 : ℝ)*X 0 1+(2512437473/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5412263831/10000000000 : ℝ)*X 1 0+(-59672589/250000000 : ℝ)*X 1 1+(5024874789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((338266477/625000000 : ℝ)*X 2 0+(628109369/1250000000 : ℝ)*X 2 1+(-2386903611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4303237207/10000000000 : ℝ)*X 0 0+(14416271/39062500 : ℝ)*X 0 1+(1002524217/2000000000 : ℝ)*X 0 2+(4303237207/10000000000 : ℝ)*X 1 0+(14416271/39062500 : ℝ)*X 1 1+(1002524217/2000000000 : ℝ)*X 1 2+(4303237207/10000000000 : ℝ)*X 2 0+(14416271/39062500 : ℝ)*X 2 1+(1002524217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-408163751/2000000000 : ℝ)*X 0 0+(2516688599/5000000000 : ℝ)*X 0 1+(5662434191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049096503/2000000000 : ℝ)*X 1 0+(-1749344079/10000000000 : ℝ)*X 1 1+(1132486921/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((209819297/400000000 : ℝ)*X 2 0+(2831217153/5000000000 : ℝ)*X 2 1+(-2733351/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((860918877/2000000000 : ℝ)*X 0 0+(499522719/1000000000 : ℝ)*X 0 1+(1854145501/5000000000 : ℝ)*X 0 2+(860918877/2000000000 : ℝ)*X 1 0+(499522719/1000000000 : ℝ)*X 1 1+(1854145501/5000000000 : ℝ)*X 1 2+(860918877/2000000000 : ℝ)*X 2 0+(499522719/1000000000 : ℝ)*X 2 1+(1854145501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4592790030971346745633617/625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80254341/100000000000000 : ℝ)*(base1) + (190575767/12500000000000 : ℝ)*(base19) + (1467708347/100000000000000 : ℝ)*(base23) + (176655071/100000000000000 : ℝ)*(upper3) + (714329/500000000000 : ℝ)*(upper5) + (575968534479141/50000000000000 : ℝ)*(major0) + (575968534479141/50000000000000 : ℝ)*(major1) + (575968534479141/50000000000000 : ℝ)*(major2) + (386864998223443/25000000000000 : ℝ)*(sp0) + (30949330014927/2000000000000 : ℝ)*(sp1) + (1547466557644139/100000000000000 : ℝ)*(sp2) + (378200840653097/50000000000000 : ℝ)*(sp3) + (1622542611/20000000000000 : ℝ)*(sp4) + (2053027367/50000000000000 : ℝ)*(sp7) + (189101466903817/25000000000000 : ℝ)*(f.failure) + (773734012676243/50000000000000 : ℝ)*(f.sum) + (35338914483/25000000000000000000000000 : ℝ)*base66 + (9005673894380461/1250000000000000000000000000000 : ℝ)*base67 + (6179638311869539/1250000000000000000000000000000 : ℝ)*base70 + (6537621909380461/1250000000000000000000000000000 : ℝ)*base71 + (6822378623/6250000000000000000000000 : ℝ)*base73 + (1720226228119539/1250000000000000000000000000000 : ℝ)*base76 + (5915889411880461/1250000000000000000000000000000 : ℝ)*base77 + (4467162991880461/1250000000000000000000000000000 : ℝ)*base79 + (115244676133/25000000000000000000000000 : ℝ)*base82 + (19653027/2500000000000000000000 : ℝ)*base90 + (19653027/2500000000000000000000 : ℝ)*base92 + (19653027/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22687499352900042330266587041/2198750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11977229/20000000000000 : ℝ)*(base1) + (404258761/20000000000000 : ℝ)*(base19) + (1956635053/100000000000000 : ℝ)*(base23) + (33133831/12500000000000 : ℝ)*(upper3) + (45819011/20000000000000 : ℝ)*(upper5) + (1183360123560591/100000000000000 : ℝ)*(major0) + (1183360123560591/100000000000000 : ℝ)*(major1) + (1183360123560591/100000000000000 : ℝ)*(major2) + (10094447267/100000000000000 : ℝ)*(sp1) + (8918690143/100000000000000 : ℝ)*(sp2) + (39742012946667/2500000000000 : ℝ)*(sp4) + (198708542779933/12500000000000 : ℝ)*(sp5) + (79483479132767/5000000000000 : ℝ)*(sp6) + (777039385309083/100000000000000 : ℝ)*(sp7) + (194259861298807/25000000000000 : ℝ)*(f.failure) + (317936091596107/20000000000000 : ℝ)*(f.sum) + (20809155206661/43975000000000000000000000000 : ℝ)*base66 + (7735554482066912551/4397500000000000000000000000000000 : ℝ)*base68 + (17986556336376912551/4397500000000000000000000000000000 : ℝ)*base70 + (23438329459411912551/4397500000000000000000000000000000 : ℝ)*base72 + (35354828123343/21987500000000000000000000000 : ℝ)*base74 + (17005243230819412551/4397500000000000000000000000000000 : ℝ)*base76 + (3044074663414412551/4397500000000000000000000000000000 : ℝ)*base78 + (30972514116626912551/4397500000000000000000000000000000 : ℝ)*base80 + (140723335487711/43975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (11693283/2500000000000000000000 : ℝ)*base89 + (11693283/2500000000000000000000 : ℝ)*base91 + (11693283/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1280_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6831/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (393/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4987/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1280_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1280_s2_0 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-130374609/625000000 : ℝ)*x 0 + (1374499843/2500000000 : ℝ)*x 1 + (2584358069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130374609/625000000 : ℝ)^265 ≤ (6332086621347/50000000000000 : ℝ)^201 := by
    have hnat : (130374609 : ℕ)^265*50000000000000^201 ≤ 6332086621347^201*625000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130374609 625000000 6332086621347 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374499843/2500000000 : ℝ)^265 ≤ (22722378727197/50000000000000 : ℝ)^201 := by
    have hnat : (1374499843 : ℕ)^265*50000000000000^201 ≤ 22722378727197^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374499843 2500000000 22722378727197 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2584358069/5000000000 : ℝ)^265 ≤ (8378213856773/20000000000000 : ℝ)^201 := by
    have hnat : (2584358069 : ℕ)^265*20000000000000^201 ≤ 8378213856773^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584358069 5000000000 8378213856773 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130374609/625000000 : ℝ), (1374499843/2500000000 : ℝ), (2584358069/5000000000 : ℝ)] ![(6332086621347/50000000000000 : ℝ), (22722378727197/50000000000000 : ℝ), (8378213856773/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130374609/625000000 : ℝ)|^265 ≤ (6332086621347/50000000000000 : ℝ)^201
        have hw : |(-130374609/625000000 : ℝ)|=(130374609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374499843/2500000000 : ℝ)|^265 ≤ (22722378727197/50000000000000 : ℝ)^201
        have hw : |(1374499843/2500000000 : ℝ)|=(1374499843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2584358069/5000000000 : ℝ)|^265 ≤ (8378213856773/20000000000000 : ℝ)^201
        have hw : |(2584358069/5000000000 : ℝ)|=(2584358069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s2_1 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2685245749/5000000000 : ℝ)*x 0 + (-451352727/2000000000 : ℝ)*x 1 + (5168716957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685245749/5000000000 : ℝ)^265 ≤ (44060391572139/100000000000000 : ℝ)^201 := by
    have hnat : (2685245749 : ℕ)^265*100000000000000^201 ≤ 44060391572139^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685245749 5000000000 44060391572139 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451352727/2000000000 : ℝ)^265 ≤ (14048530380971/100000000000000 : ℝ)^201 := by
    have hnat : (451352727 : ℕ)^265*100000000000000^201 ≤ 14048530380971^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451352727 2000000000 14048530380971 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5168716957/10000000000 : ℝ)^265 ≤ (10472769508791/25000000000000 : ℝ)^201 := by
    have hnat : (5168716957 : ℕ)^265*25000000000000^201 ≤ 10472769508791^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168716957 10000000000 10472769508791 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685245749/5000000000 : ℝ), (-451352727/2000000000 : ℝ), (5168716957/10000000000 : ℝ)] ![(44060391572139/100000000000000 : ℝ), (14048530380971/100000000000000 : ℝ), (10472769508791/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685245749/5000000000 : ℝ)|^265 ≤ (44060391572139/100000000000000 : ℝ)^201
        have hw : |(2685245749/5000000000 : ℝ)|=(2685245749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451352727/2000000000 : ℝ)|^265 ≤ (14048530380971/100000000000000 : ℝ)^201
        have hw : |(-451352727/2000000000 : ℝ)|=(451352727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5168716957/10000000000 : ℝ)|^265 ≤ (10472769508791/25000000000000 : ℝ)^201
        have hw : |(5168716957/10000000000 : ℝ)|=(5168716957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s2_2 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5370491977/10000000000 : ℝ)*x 0 + (1292179069/2500000000 : ℝ)*x 1 + (-225676389/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370491977/10000000000 : ℝ)^265 ≤ (44060396753211/100000000000000 : ℝ)^201 := by
    have hnat : (5370491977 : ℕ)^265*100000000000000^201 ≤ 44060396753211^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370491977 10000000000 44060396753211 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292179069/2500000000 : ℝ)^265 ≤ (41891070758443/100000000000000 : ℝ)^201 := by
    have hnat : (1292179069 : ℕ)^265*100000000000000^201 ≤ 41891070758443^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292179069 2500000000 41891070758443 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225676389/1000000000 : ℝ)^265 ≤ (2809706494761/20000000000000 : ℝ)^201 := by
    have hnat : (225676389 : ℕ)^265*20000000000000^201 ≤ 2809706494761^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225676389 1000000000 2809706494761 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370491977/10000000000 : ℝ), (1292179069/2500000000 : ℝ), (-225676389/1000000000 : ℝ)] ![(44060396753211/100000000000000 : ℝ), (41891070758443/100000000000000 : ℝ), (2809706494761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370491977/10000000000 : ℝ)|^265 ≤ (44060396753211/100000000000000 : ℝ)^201
        have hw : |(5370491977/10000000000 : ℝ)|=(5370491977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292179069/2500000000 : ℝ)|^265 ≤ (41891070758443/100000000000000 : ℝ)^201
        have hw : |(1292179069/2500000000 : ℝ)|=(1292179069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225676389/1000000000 : ℝ)|^265 ≤ (2809706494761/20000000000000 : ℝ)^201
        have hw : |(-225676389/1000000000 : ℝ)|=(225676389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s2_3 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1083763103/2500000000 : ℝ)*x 0 + (4010759233/10000000000 : ℝ)*x 1 + (4684418521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083763103/2500000000 : ℝ)^265 ≤ (33220828932691/100000000000000 : ℝ)^201 := by
    have hnat : (1083763103 : ℕ)^265*100000000000000^201 ≤ 33220828932691^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083763103 2500000000 33220828932691 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010759233/10000000000 : ℝ)^265 ≤ (149920418117/500000000000 : ℝ)^201 := by
    have hnat : (4010759233 : ℕ)^265*500000000000^201 ≤ 149920418117^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010759233 10000000000 149920418117 500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4684418521/10000000000 : ℝ)^265 ≤ (36795087434369/100000000000000 : ℝ)^201 := by
    have hnat : (4684418521 : ℕ)^265*100000000000000^201 ≤ 36795087434369^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4684418521 10000000000 36795087434369 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083763103/2500000000 : ℝ), (4010759233/10000000000 : ℝ), (4684418521/10000000000 : ℝ)] ![(33220828932691/100000000000000 : ℝ), (149920418117/500000000000 : ℝ), (36795087434369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083763103/2500000000 : ℝ)|^265 ≤ (33220828932691/100000000000000 : ℝ)^201
        have hw : |(1083763103/2500000000 : ℝ)|=(1083763103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010759233/10000000000 : ℝ)|^265 ≤ (149920418117/500000000000 : ℝ)^201
        have hw : |(4010759233/10000000000 : ℝ)|=(4010759233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4684418521/10000000000 : ℝ)|^265 ≤ (36795087434369/100000000000000 : ℝ)^201
        have hw : |(4684418521/10000000000 : ℝ)|=(4684418521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s2_4 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1043040307/5000000000 : ℝ)*x 0 + (1292733357/2500000000 : ℝ)*x 1 + (137394029/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043040307/5000000000 : ℝ)^265 ≤ (2532973713063/20000000000000 : ℝ)^201 := by
    have hnat : (1043040307 : ℕ)^265*20000000000000^201 ≤ 2532973713063^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043040307 5000000000 2532973713063 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292733357/2500000000 : ℝ)^265 ≤ (10478690853041/25000000000000 : ℝ)^201 := by
    have hnat : (1292733357 : ℕ)^265*25000000000000^201 ≤ 10478690853041^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292733357 2500000000 10478690853041 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137394029/250000000 : ℝ)^265 ≤ (11355092001339/25000000000000 : ℝ)^201 := by
    have hnat : (137394029 : ℕ)^265*25000000000000^201 ≤ 11355092001339^201*250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137394029 250000000 11355092001339 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1043040307/5000000000 : ℝ), (1292733357/2500000000 : ℝ), (137394029/250000000 : ℝ)] ![(2532973713063/20000000000000 : ℝ), (10478690853041/25000000000000 : ℝ), (11355092001339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1043040307/5000000000 : ℝ)|^265 ≤ (2532973713063/20000000000000 : ℝ)^201
        have hw : |(-1043040307/5000000000 : ℝ)|=(1043040307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292733357/2500000000 : ℝ)|^265 ≤ (10478690853041/25000000000000 : ℝ)^201
        have hw : |(1292733357/2500000000 : ℝ)|=(1292733357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137394029/250000000 : ℝ)|^265 ≤ (11355092001339/25000000000000 : ℝ)^201
        have hw : |(137394029/250000000 : ℝ)|=(137394029/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s2_5 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5286216309/10000000000 : ℝ)*x 0 + (-1929718747/10000000000 : ℝ)*x 1 + (2747880659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286216309/10000000000 : ℝ)^265 ≤ (10787779994427/25000000000000 : ℝ)^201 := by
    have hnat : (5286216309 : ℕ)^265*25000000000000^201 ≤ 10787779994427^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286216309 10000000000 10787779994427 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929718747/10000000000 : ℝ)^265 ≤ (178570473039/1562500000000 : ℝ)^201 := by
    have hnat : (1929718747 : ℕ)^265*1562500000000^201 ≤ 178570473039^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929718747 10000000000 178570473039 1562500000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747880659/5000000000 : ℝ)^265 ≤ (9084073945389/20000000000000 : ℝ)^201 := by
    have hnat : (2747880659 : ℕ)^265*20000000000000^201 ≤ 9084073945389^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747880659 5000000000 9084073945389 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286216309/10000000000 : ℝ), (-1929718747/10000000000 : ℝ), (2747880659/5000000000 : ℝ)] ![(10787779994427/25000000000000 : ℝ), (178570473039/1562500000000 : ℝ), (9084073945389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286216309/10000000000 : ℝ)|^265 ≤ (10787779994427/25000000000000 : ℝ)^201
        have hw : |(5286216309/10000000000 : ℝ)|=(5286216309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1929718747/10000000000 : ℝ)|^265 ≤ (178570473039/1562500000000 : ℝ)^201
        have hw : |(-1929718747/10000000000 : ℝ)|=(1929718747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747880659/5000000000 : ℝ)|^265 ≤ (9084073945389/20000000000000 : ℝ)^201
        have hw : |(2747880659/5000000000 : ℝ)|=(2747880659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s2_6 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (330388531/625000000 : ℝ)*x 0 + (5495761169/10000000000 : ℝ)*x 1 + (-964859349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330388531/625000000 : ℝ)^265 ≤ (2157556099511/5000000000000 : ℝ)^201 := by
    have hnat : (330388531 : ℕ)^265*5000000000000^201 ≤ 2157556099511^201*625000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330388531 625000000 2157556099511 5000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5495761169/10000000000 : ℝ)^265 ≤ (45420368103421/100000000000000 : ℝ)^201 := by
    have hnat : (5495761169 : ℕ)^265*100000000000000^201 ≤ 45420368103421^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495761169 10000000000 45420368103421 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964859349/5000000000 : ℝ)^265 ≤ (11428509891899/100000000000000 : ℝ)^201 := by
    have hnat : (964859349 : ℕ)^265*100000000000000^201 ≤ 11428509891899^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964859349 5000000000 11428509891899 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330388531/625000000 : ℝ), (5495761169/10000000000 : ℝ), (-964859349/5000000000 : ℝ)] ![(2157556099511/5000000000000 : ℝ), (45420368103421/100000000000000 : ℝ), (11428509891899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330388531/625000000 : ℝ)|^265 ≤ (2157556099511/5000000000000 : ℝ)^201
        have hw : |(330388531/625000000 : ℝ)|=(330388531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5495761169/10000000000 : ℝ)|^265 ≤ (45420368103421/100000000000000 : ℝ)^201
        have hw : |(5495761169/10000000000 : ℝ)|=(5495761169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964859349/5000000000 : ℝ)|^265 ≤ (11428509891899/100000000000000 : ℝ)^201
        have hw : |(-964859349/5000000000 : ℝ)|=(964859349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s2_7 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (433523043/1000000000 : ℝ)*x 0 + (467988139/1000000000 : ℝ)*x 1 + (16061369/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433523043/1000000000 : ℝ)^265 ≤ (4152828440601/12500000000000 : ℝ)^201 := by
    have hnat : (433523043 : ℕ)^265*12500000000000^201 ≤ 4152828440601^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433523043 1000000000 4152828440601 12500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (467988139/1000000000 : ℝ)^265 ≤ (9187027256527/25000000000000 : ℝ)^201 := by
    have hnat : (467988139 : ℕ)^265*25000000000000^201 ≤ 9187027256527^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467988139 1000000000 9187027256527 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16061369/40000000 : ℝ)^265 ≤ (7507315859699/25000000000000 : ℝ)^201 := by
    have hnat : (16061369 : ℕ)^265*25000000000000^201 ≤ 7507315859699^201*40000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16061369 40000000 7507315859699 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433523043/1000000000 : ℝ), (467988139/1000000000 : ℝ), (16061369/40000000 : ℝ)] ![(4152828440601/12500000000000 : ℝ), (9187027256527/25000000000000 : ℝ), (7507315859699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433523043/1000000000 : ℝ)|^265 ≤ (4152828440601/12500000000000 : ℝ)^201
        have hw : |(433523043/1000000000 : ℝ)|=(433523043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(467988139/1000000000 : ℝ)|^265 ≤ (9187027256527/25000000000000 : ℝ)^201
        have hw : |(467988139/1000000000 : ℝ)|=(467988139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16061369/40000000 : ℝ)|^265 ≤ (7507315859699/25000000000000 : ℝ)^201
        have hw : |(16061369/40000000 : ℝ)|=(16061369/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1280_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4987/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (393/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1883/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16373/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4987/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (393/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4987/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (393/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4987/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (393/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4987/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (393/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4987/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (393/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4987/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (393/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (393/6250 : ℝ) ^ (4239/1024 : ℝ) ≤ (106234183589271/10000000000000000000 : ℝ) := by
    have hpowers : (393/6250 : ℝ)^4239 ≤ (106234183589271/10000000000000000000 : ℝ)^1024 := by
      have hnat : (393 : ℕ)^4239*10000000000000000000^1024 ≤ 106234183589271^1024*6250^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        393 6250 106234183589271 10000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (393/6250 : ℝ)) (X := (106234183589271/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4987/25000 : ℝ) ^ (4239/1024 : ℝ) ≤ (126423985606996277/100000000000000000000 : ℝ) := by
    have hpowers : (4987/25000 : ℝ)^4239 ≤ (126423985606996277/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4987 : ℕ)^4239*100000000000000000000^1024 ≤ 126423985606996277^1024*25000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4987 25000 126423985606996277 100000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4987/25000 : ℝ)) (X := (126423985606996277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000106234183589271/5000000000000000000 : ℝ) ≤ (10000051324806567/10000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (5000106234183589271/5000000000000000000 : ℝ)^1024 ≤ (10000051324806567/10000000000000000 : ℝ)^4239 := by
      have hnat : (5000106234183589271 : ℕ)^1024*10000000000000000^4239 ≤ 10000051324806567^4239*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000106234183589271 5000000000000000000 10000051324806567 10000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000051324806567/10000000000000000 : ℝ)) (X := (5000106234183589271/5000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100127486327442888987/100000000000000000000 : ℝ) ≤ (625192384604291/625000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (100127486327442888987/100000000000000000000 : ℝ)^1024 ≤ (625192384604291/625000000000000 : ℝ)^4239 := by
      have hnat : (100127486327442888987 : ℕ)^1024*625000000000000^4239 ≤ 625192384604291^4239*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100127486327442888987 100000000000000000000 625192384604291 625000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625192384604291/625000000000000 : ℝ)) (X := (100127486327442888987/100000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50126423985606996277/50000000000000000000 : ℝ) ≤ (2001220996506149/2000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (50126423985606996277/50000000000000000000 : ℝ)^1024 ≤ (2001220996506149/2000000000000000 : ℝ)^4239 := by
      have hnat : (50126423985606996277 : ℕ)^1024*2000000000000000^4239 ≤ 2001220996506149^4239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50126423985606996277 50000000000000000000 2001220996506149 2000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001220996506149/2000000000000000 : ℝ)) (X := (50126423985606996277/50000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(106234183589271/10000000000000000000 : ℝ) ≤ ((34140658924272018489/34150000000000000000 : ℝ)+2*(3026828862089/1366000000000000 : ℝ)*(393/6250 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (34140658924272018489/34150000000000000000 : ℝ)+2*(3026828862089/1366000000000000 : ℝ)*(393/6250 : ℝ)=(10000051324806567/10000000000000000 : ℝ) by norm_num, show 1+2*(106234183589271/10000000000000000000 : ℝ)=(5000106234183589271/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(126423985606996277/100000000000000000000 : ℝ)+(106234183589271/10000000000000000000 : ℝ) ≤ ((34140658924272018489/34150000000000000000 : ℝ)+(3026828862089/1366000000000000 : ℝ)*((4987/25000 : ℝ)+(393/6250 : ℝ)))^(4239/1024 : ℝ) := by
    rw [show (34140658924272018489/34150000000000000000 : ℝ)+(3026828862089/1366000000000000 : ℝ)*((4987/25000 : ℝ)+(393/6250 : ℝ))=(625192384604291/625000000000000 : ℝ) by norm_num, show 1+(126423985606996277/100000000000000000000 : ℝ)+(106234183589271/10000000000000000000 : ℝ)=(100127486327442888987/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(126423985606996277/100000000000000000000 : ℝ) ≤ ((34140658924272018489/34150000000000000000 : ℝ)+2*(3026828862089/1366000000000000 : ℝ)*(4987/25000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (34140658924272018489/34150000000000000000 : ℝ)+2*(3026828862089/1366000000000000 : ℝ)*(4987/25000 : ℝ)=(2001220996506149/2000000000000000 : ℝ) by norm_num, show 1+2*(126423985606996277/100000000000000000000 : ℝ)=(50126423985606996277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34140658924272018489/34150000000000000000 : ℝ)*(X 1 0+X 2 0)+(3026828862089/1366000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (393/6250 : ℝ)) (hi := (4987/25000 : ℝ)) (c := (34140658924272018489/34150000000000000000 : ℝ)) (alpha := (3026828862089/1366000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34140658924272018489/34150000000000000000 : ℝ)*(X 0 1+X 2 1)+(3026828862089/1366000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (393/6250 : ℝ)) (hi := (4987/25000 : ℝ)) (c := (34140658924272018489/34150000000000000000 : ℝ)) (alpha := (3026828862089/1366000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34140658924272018489/34150000000000000000 : ℝ)*(X 0 2+X 1 2)+(3026828862089/1366000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (393/6250 : ℝ)) (hi := (4987/25000 : ℝ)) (c := (34140658924272018489/34150000000000000000 : ℝ)) (alpha := (3026828862089/1366000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-130374609/625000000 : ℝ)*X 0 0+(1374499843/2500000000 : ℝ)*X 0 1+(2584358069/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685245749/5000000000 : ℝ)*X 1 0+(-451352727/2000000000 : ℝ)*X 1 1+(5168716957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370491977/10000000000 : ℝ)*X 2 0+(1292179069/2500000000 : ℝ)*X 2 1+(-225676389/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083763103/2500000000 : ℝ)*X 0 0+(4010759233/10000000000 : ℝ)*X 0 1+(4684418521/10000000000 : ℝ)*X 0 2+(1083763103/2500000000 : ℝ)*X 1 0+(4010759233/10000000000 : ℝ)*X 1 1+(4684418521/10000000000 : ℝ)*X 1 2+(1083763103/2500000000 : ℝ)*X 2 0+(4010759233/10000000000 : ℝ)*X 2 1+(4684418521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1043040307/5000000000 : ℝ)*X 0 0+(1292733357/2500000000 : ℝ)*X 0 1+(137394029/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5286216309/10000000000 : ℝ)*X 1 0+(-1929718747/10000000000 : ℝ)*X 1 1+(2747880659/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330388531/625000000 : ℝ)*X 2 0+(5495761169/10000000000 : ℝ)*X 2 1+(-964859349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((433523043/1000000000 : ℝ)*X 0 0+(467988139/1000000000 : ℝ)*X 0 1+(16061369/40000000 : ℝ)*X 0 2+(433523043/1000000000 : ℝ)*X 1 0+(467988139/1000000000 : ℝ)*X 1 1+(16061369/40000000 : ℝ)*X 1 2+(433523043/1000000000 : ℝ)*X 2 0+(467988139/1000000000 : ℝ)*X 2 1+(16061369/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1090238499968016322939323723/213437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1841624973/100000000000000 : ℝ)*(base19) + (2071694177/100000000000000 : ℝ)*(base23) + (10955461/50000000000000 : ℝ)*(lower2) + (29496147/6250000000000 : ℝ)*(upper3) + (32227859/10000000000000 : ℝ)*(upper5) + (565175646372931/25000000000000 : ℝ)*(major0) + (565175646372931/25000000000000 : ℝ)*(major1) + (565175646372931/25000000000000 : ℝ)*(major2) + (3036920975045083/100000000000000 : ℝ)*(sp0) + (759234878435603/25000000000000 : ℝ)*(sp1) + (379617410459151/12500000000000 : ℝ)*(sp2) + (742222868928621/50000000000000 : ℝ)*(sp3) + (10190161151/50000000000000 : ℝ)*(sp4) + (17907492187/100000000000000 : ℝ)*(sp7) + (148446364534943/10000000000000 : ℝ)*(f.failure) + (607388271073477/20000000000000 : ℝ)*(f.sum) + (40717239539809/17075000000000000000000000000 : ℝ)*base65 + (6307814114000873/1250000000000000000000000000000 : ℝ)*base67 + (268682666500873/1250000000000000000000000000000 : ℝ)*base69 + (3700831938499127/1250000000000000000000000000000 : ℝ)*base72 + (140487766303659/17075000000000000000000000000 : ℝ)*base73 + (2716882029000873/1250000000000000000000000000000 : ℝ)*base75 + (5241869261500873/1250000000000000000000000000000 : ℝ)*base77 + (3278646269000873/1250000000000000000000000000000 : ℝ)*base79 + (96611965555459/17075000000000000000000000000 : ℝ)*base81 + (10335467/1000000000000000000000 : ℝ)*base89 + (10335467/1000000000000000000000 : ℝ)*base91 + (10335467/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93687332805902164966521/34150000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62967369/12500000000000 : ℝ)*(base19) + (761839157/100000000000000 : ℝ)*(base23) + (115221771/100000000000000 : ℝ)*(upper3) + (49959527/100000000000000 : ℝ)*(lower4) + (1145838999265013/50000000000000 : ℝ)*(major0) + (1145838999265013/50000000000000 : ℝ)*(major1) + (1145838999265013/50000000000000 : ℝ)*(major2) + (4901946839/100000000000000 : ℝ)*(sp1) + (8332216279/100000000000000 : ℝ)*(sp2) + (179533/20000000000000 : ℝ)*(sp3) + (769638155307111/25000000000000 : ℝ)*(sp4) + (3078547215542653/100000000000000 : ℝ)*(sp5) + (192408970448313/6250000000000 : ℝ)*(sp6) + (376200820871763/25000000000000 : ℝ)*(sp7) + (376200821096179/25000000000000 : ℝ)*(f.failure) + (769638155307111/25000000000000 : ℝ)*(f.sum) + (228999388682443/34150000000000000000000000000 : ℝ)*base66 + (6925835309550879/2500000000000000000000000000000 : ℝ)*base67 + (10639944689550879/2500000000000000000000000000000 : ℝ)*base69 + (19011998895449121/2500000000000000000000000000000 : ℝ)*base72 + (80310696604193/34150000000000000000000000000 : ℝ)*base74 + (3774831652949121/2500000000000000000000000000000 : ℝ)*base76 + (1668576275449121/2500000000000000000000000000000 : ℝ)*base78 + (15358941999550879/2500000000000000000000000000000 : ℝ)*base79 + (52112966642507/34150000000000000000000000000 : ℝ)*base81 + (17510449/2500000000000000000000 : ℝ)*base90 + (17510449/2500000000000000000000 : ℝ)*base92 + (17510449/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1280_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4987/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (393/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1883/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16373/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1280_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1280_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1883/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16373/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1280_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1280_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1280_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1883/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16373/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1280_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
