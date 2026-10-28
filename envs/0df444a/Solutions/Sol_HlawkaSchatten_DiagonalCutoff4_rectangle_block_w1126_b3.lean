-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1126_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:48.526483+00:00
-- url     : https://prove2.me/submissions/ed689fac-9295-4c77-a656-f49a63de8abc

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
theorem support_rectangle_w1126_box_0 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047138941/10000000000 : ℝ)*x 0 + (5376537431/10000000000 : ℝ)*x 1 + (672067163/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047138941/10000000000 : ℝ)^8319 ≤ (12194948302931/100000000000000 : ℝ)^6271 := by
    have hnat : (2047138941 : ℕ)^8319*100000000000000^6271 ≤ 12194948302931^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047138941 10000000000 12194948302931 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376537431/10000000000 : ℝ)^8319 ≤ (43902526528531/100000000000000 : ℝ)^6271 := by
    have hnat : (5376537431 : ℕ)^8319*100000000000000^6271 ≤ 43902526528531^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376537431 10000000000 43902526528531 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672067163/1250000000 : ℝ)^8319 ≤ (10975631288207/25000000000000 : ℝ)^6271 := by
    have hnat : (672067163 : ℕ)^8319*25000000000000^6271 ≤ 10975631288207^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672067163 1250000000 10975631288207 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047138941/10000000000 : ℝ), (5376537431/10000000000 : ℝ), (672067163/1250000000 : ℝ)] ![(12194948302931/100000000000000 : ℝ), (43902526528531/100000000000000 : ℝ), (10975631288207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047138941/10000000000 : ℝ)|^8319 ≤ (12194948302931/100000000000000 : ℝ)^6271
        have hw : |(-2047138941/10000000000 : ℝ)|=(2047138941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376537431/10000000000 : ℝ)|^8319 ≤ (43902526528531/100000000000000 : ℝ)^6271
        have hw : |(5376537431/10000000000 : ℝ)|=(5376537431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672067163/1250000000 : ℝ)|^8319 ≤ (10975631288207/25000000000000 : ℝ)^6271
        have hw : |(672067163/1250000000 : ℝ)|=(672067163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_1 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661979027/1250000000 : ℝ)*x 0 + (-2156548659/10000000000 : ℝ)*x 1 + (1075307493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661979027/1250000000 : ℝ)^8319 ≤ (21515226267167/50000000000000 : ℝ)^6271 := by
    have hnat : (661979027 : ℕ)^8319*50000000000000^6271 ≤ 21515226267167^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661979027 1250000000 21515226267167 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156548659/10000000000 : ℝ)^8319 ≤ (816688785043/6250000000000 : ℝ)^6271 := by
    have hnat : (2156548659 : ℕ)^8319*6250000000000^6271 ≤ 816688785043^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156548659 10000000000 816688785043 6250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075307493/2000000000 : ℝ)^8319 ≤ (4390252689683/10000000000000 : ℝ)^6271 := by
    have hnat : (1075307493 : ℕ)^8319*10000000000000^6271 ≤ 4390252689683^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075307493 2000000000 4390252689683 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661979027/1250000000 : ℝ), (-2156548659/10000000000 : ℝ), (1075307493/2000000000 : ℝ)] ![(21515226267167/50000000000000 : ℝ), (816688785043/6250000000000 : ℝ), (4390252689683/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661979027/1250000000 : ℝ)|^8319 ≤ (21515226267167/50000000000000 : ℝ)^6271
        have hw : |(661979027/1250000000 : ℝ)|=(661979027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2156548659/10000000000 : ℝ)|^8319 ≤ (816688785043/6250000000000 : ℝ)^6271
        have hw : |(-2156548659/10000000000 : ℝ)|=(2156548659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075307493/2000000000 : ℝ)|^8319 ≤ (4390252689683/10000000000000 : ℝ)^6271
        have hw : |(1075307493/2000000000 : ℝ)|=(1075307493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_2 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661979051/1250000000 : ℝ)*x 0 + (1344134319/2500000000 : ℝ)*x 1 + (-2156548657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661979051/1250000000 : ℝ)^8319 ≤ (4303045460389/10000000000000 : ℝ)^6271 := by
    have hnat : (661979051 : ℕ)^8319*10000000000000^6271 ≤ 4303045460389^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661979051 1250000000 4303045460389 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344134319/2500000000 : ℝ)^8319 ≤ (43902524849523/100000000000000 : ℝ)^6271 := by
    have hnat : (1344134319 : ℕ)^8319*100000000000000^6271 ≤ 43902524849523^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344134319 2500000000 43902524849523 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156548657/10000000000 : ℝ)^8319 ≤ (3266755136153/25000000000000 : ℝ)^6271 := by
    have hnat : (2156548657 : ℕ)^8319*25000000000000^6271 ≤ 3266755136153^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156548657 10000000000 3266755136153 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661979051/1250000000 : ℝ), (1344134319/2500000000 : ℝ), (-2156548657/10000000000 : ℝ)] ![(4303045460389/10000000000000 : ℝ), (43902524849523/100000000000000 : ℝ), (3266755136153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661979051/1250000000 : ℝ)|^8319 ≤ (4303045460389/10000000000000 : ℝ)^6271
        have hw : |(661979051/1250000000 : ℝ)|=(661979051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344134319/2500000000 : ℝ)|^8319 ≤ (43902524849523/100000000000000 : ℝ)^6271
        have hw : |(1344134319/2500000000 : ℝ)|=(1344134319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2156548657/10000000000 : ℝ)|^8319 ≤ (3266755136153/25000000000000 : ℝ)^6271
        have hw : |(-2156548657/10000000000 : ℝ)|=(2156548657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_3 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2237326207/5000000000 : ℝ)*x 0 + (2157597231/5000000000 : ℝ)*x 1 + (86303897/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2237326207/5000000000 : ℝ)^8319 ≤ (17205739649209/50000000000000 : ℝ)^6271 := by
    have hnat : (2237326207 : ℕ)^8319*50000000000000^6271 ≤ 17205739649209^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237326207 5000000000 17205739649209 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157597231/5000000000 : ℝ)^8319 ≤ (16397129193127/50000000000000 : ℝ)^6271 := by
    have hnat : (2157597231 : ℕ)^8319*50000000000000^6271 ≤ 16397129193127^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157597231 5000000000 16397129193127 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86303897/200000000 : ℝ)^8319 ≤ (2049641393621/6250000000000 : ℝ)^6271 := by
    have hnat : (86303897 : ℕ)^8319*6250000000000^6271 ≤ 2049641393621^6271*200000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86303897 200000000 2049641393621 6250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2237326207/5000000000 : ℝ), (2157597231/5000000000 : ℝ), (86303897/200000000 : ℝ)] ![(17205739649209/50000000000000 : ℝ), (16397129193127/50000000000000 : ℝ), (2049641393621/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2237326207/5000000000 : ℝ)|^8319 ≤ (17205739649209/50000000000000 : ℝ)^6271
        have hw : |(2237326207/5000000000 : ℝ)|=(2237326207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2157597231/5000000000 : ℝ)|^8319 ≤ (16397129193127/50000000000000 : ℝ)^6271
        have hw : |(2157597231/5000000000 : ℝ)|=(2157597231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(86303897/200000000 : ℝ)|^8319 ≤ (2049641393621/6250000000000 : ℝ)^6271
        have hw : |(86303897/200000000 : ℝ)|=(86303897/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_4 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-287921867/1250000000 : ℝ)*x 0 + (5280932773/10000000000 : ℝ)*x 1 + (1320233233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287921867/1250000000 : ℝ)^8319 ≤ (7130072960943/50000000000000 : ℝ)^6271 := by
    have hnat : (287921867 : ℕ)^8319*50000000000000^6271 ≤ 7130072960943^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287921867 1250000000 7130072960943 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280932773/10000000000 : ℝ)^8319 ≤ (42869926172787/100000000000000 : ℝ)^6271 := by
    have hnat : (5280932773 : ℕ)^8319*100000000000000^6271 ≤ 42869926172787^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280932773 10000000000 42869926172787 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320233233/2500000000 : ℝ)^8319 ≤ (21434963942531/50000000000000 : ℝ)^6271 := by
    have hnat : (1320233233 : ℕ)^8319*50000000000000^6271 ≤ 21434963942531^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320233233 2500000000 21434963942531 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-287921867/1250000000 : ℝ), (5280932773/10000000000 : ℝ), (1320233233/2500000000 : ℝ)] ![(7130072960943/50000000000000 : ℝ), (42869926172787/100000000000000 : ℝ), (21434963942531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-287921867/1250000000 : ℝ)|^8319 ≤ (7130072960943/50000000000000 : ℝ)^6271
        have hw : |(-287921867/1250000000 : ℝ)|=(287921867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280932773/10000000000 : ℝ)|^8319 ≤ (42869926172787/100000000000000 : ℝ)^6271
        have hw : |(5280932773/10000000000 : ℝ)|=(5280932773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320233233/2500000000 : ℝ)|^8319 ≤ (21434963942531/50000000000000 : ℝ)^6271
        have hw : |(1320233233/2500000000 : ℝ)|=(1320233233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_5 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340850381/2500000000 : ℝ)*x 0 + (-1097054251/5000000000 : ℝ)*x 1 + (2640466309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340850381/2500000000 : ℝ)^8319 ≤ (1367509096353/3125000000000 : ℝ)^6271 := by
    have hnat : (1340850381 : ℕ)^8319*3125000000000^6271 ≤ 1367509096353^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340850381 2500000000 1367509096353 3125000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097054251/5000000000 : ℝ)^8319 ≤ (417805762397/3125000000000 : ℝ)^6271 := by
    have hnat : (1097054251 : ℕ)^8319*3125000000000^6271 ≤ 417805762397^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097054251 5000000000 417805762397 3125000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640466309/5000000000 : ℝ)^8319 ≤ (10717481125897/25000000000000 : ℝ)^6271 := by
    have hnat : (2640466309 : ℕ)^8319*25000000000000^6271 ≤ 10717481125897^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640466309 5000000000 10717481125897 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340850381/2500000000 : ℝ), (-1097054251/5000000000 : ℝ), (2640466309/5000000000 : ℝ)] ![(1367509096353/3125000000000 : ℝ), (417805762397/3125000000000 : ℝ), (10717481125897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340850381/2500000000 : ℝ)|^8319 ≤ (1367509096353/3125000000000 : ℝ)^6271
        have hw : |(1340850381/2500000000 : ℝ)|=(1340850381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1097054251/5000000000 : ℝ)|^8319 ≤ (417805762397/3125000000000 : ℝ)^6271
        have hw : |(-1097054251/5000000000 : ℝ)|=(1097054251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640466309/5000000000 : ℝ)|^8319 ≤ (10717481125897/25000000000000 : ℝ)^6271
        have hw : |(2640466309/5000000000 : ℝ)|=(2640466309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_6 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340850333/2500000000 : ℝ)*x 0 + (1056186529/2000000000 : ℝ)*x 1 + (-548527181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340850333/2500000000 : ℝ)^8319 ≤ (43760289005153/100000000000000 : ℝ)^6271 := by
    have hnat : (1340850333 : ℕ)^8319*100000000000000^6271 ≤ 43760289005153^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340850333 2500000000 43760289005153 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056186529/2000000000 : ℝ)^8319 ≤ (2679370299647/6250000000000 : ℝ)^6271 := by
    have hnat : (1056186529 : ℕ)^8319*6250000000000^6271 ≤ 2679370299647^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056186529 2000000000 2679370299647 6250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548527181/2500000000 : ℝ)^8319 ≤ (6684893095623/50000000000000 : ℝ)^6271 := by
    have hnat : (548527181 : ℕ)^8319*50000000000000^6271 ≤ 6684893095623^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548527181 2500000000 6684893095623 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340850333/2500000000 : ℝ), (1056186529/2000000000 : ℝ), (-548527181/2500000000 : ℝ)] ![(43760289005153/100000000000000 : ℝ), (2679370299647/6250000000000 : ℝ), (6684893095623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340850333/2500000000 : ℝ)|^8319 ≤ (43760289005153/100000000000000 : ℝ)^6271
        have hw : |(1340850333/2500000000 : ℝ)|=(1340850333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056186529/2000000000 : ℝ)|^8319 ≤ (2679370299647/6250000000000 : ℝ)^6271
        have hw : |(1056186529/2000000000 : ℝ)|=(1056186529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548527181/2500000000 : ℝ)|^8319 ≤ (6684893095623/50000000000000 : ℝ)^6271
        have hw : |(-548527181/2500000000 : ℝ)|=(548527181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_7 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212943097/500000000 : ℝ)*x 0 + (884613811/2000000000 : ℝ)*x 1 + (2211534399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212943097/500000000 : ℝ)^8319 ≤ (32227547621299/100000000000000 : ℝ)^6271 := by
    have hnat : (212943097 : ℕ)^8319*100000000000000^6271 ≤ 32227547621299^6271*500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212943097 500000000 32227547621299 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884613811/2000000000 : ℝ)^8319 ≤ (1694311374231/5000000000000 : ℝ)^6271 := by
    have hnat : (884613811 : ℕ)^8319*5000000000000^6271 ≤ 1694311374231^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884613811 2000000000 1694311374231 5000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211534399/5000000000 : ℝ)^8319 ≤ (16943112436329/50000000000000 : ℝ)^6271 := by
    have hnat : (2211534399 : ℕ)^8319*50000000000000^6271 ≤ 16943112436329^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211534399 5000000000 16943112436329 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212943097/500000000 : ℝ), (884613811/2000000000 : ℝ), (2211534399/5000000000 : ℝ)] ![(32227547621299/100000000000000 : ℝ), (1694311374231/5000000000000 : ℝ), (16943112436329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212943097/500000000 : ℝ)|^8319 ≤ (32227547621299/100000000000000 : ℝ)^6271
        have hw : |(212943097/500000000 : ℝ)|=(212943097/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884613811/2000000000 : ℝ)|^8319 ≤ (1694311374231/5000000000000 : ℝ)^6271
        have hw : |(884613811/2000000000 : ℝ)|=(884613811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2211534399/5000000000 : ℝ)|^8319 ≤ (16943112436329/50000000000000 : ℝ)^6271
        have hw : |(2211534399/5000000000 : ℝ)|=(2211534399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_8 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2249810727/10000000000 : ℝ)*x 0 + (208637727/400000000 : ℝ)*x 1 + (673268107/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2249810727/10000000000 : ℝ)^8319 ≤ (691095531629/5000000000000 : ℝ)^6271 := by
    have hnat : (2249810727 : ℕ)^8319*5000000000000^6271 ≤ 691095531629^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249810727 10000000000 691095531629 5000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208637727/400000000 : ℝ)^8319 ≤ (8434292368241/20000000000000 : ℝ)^6271 := by
    have hnat : (208637727 : ℕ)^8319*20000000000000^6271 ≤ 8434292368241^6271*400000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208637727 400000000 8434292368241 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673268107/1250000000 : ℝ)^8319 ≤ (44006627508871/100000000000000 : ℝ)^6271 := by
    have hnat : (673268107 : ℕ)^8319*100000000000000^6271 ≤ 44006627508871^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673268107 1250000000 44006627508871 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2249810727/10000000000 : ℝ), (208637727/400000000 : ℝ), (673268107/1250000000 : ℝ)] ![(691095531629/5000000000000 : ℝ), (8434292368241/20000000000000 : ℝ), (44006627508871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2249810727/10000000000 : ℝ)|^8319 ≤ (691095531629/5000000000000 : ℝ)^6271
        have hw : |(-2249810727/10000000000 : ℝ)|=(2249810727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208637727/400000000 : ℝ)|^8319 ≤ (8434292368241/20000000000000 : ℝ)^6271
        have hw : |(208637727/400000000 : ℝ)|=(208637727/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673268107/1250000000 : ℝ)|^8319 ≤ (44006627508871/100000000000000 : ℝ)^6271
        have hw : |(673268107/1250000000 : ℝ)|=(673268107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_9 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289038843/10000000000 : ℝ)*x 0 + (-2152704317/10000000000 : ℝ)*x 1 + (168317031/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289038843/10000000000 : ℝ)^8319 ≤ (429572425229/1000000000000 : ℝ)^6271 := by
    have hnat : (5289038843 : ℕ)^8319*1000000000000^6271 ≤ 429572425229^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289038843 10000000000 429572425229 1000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2152704317/10000000000 : ℝ)^8319 ≤ (13036128479667/100000000000000 : ℝ)^6271 := by
    have hnat : (2152704317 : ℕ)^8319*100000000000000^6271 ≤ 13036128479667^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152704317 10000000000 13036128479667 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168317031/312500000 : ℝ)^8319 ≤ (1760265159317/4000000000000 : ℝ)^6271 := by
    have hnat : (168317031 : ℕ)^8319*4000000000000^6271 ≤ 1760265159317^6271*312500000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168317031 312500000 1760265159317 4000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289038843/10000000000 : ℝ), (-2152704317/10000000000 : ℝ), (168317031/312500000 : ℝ)] ![(429572425229/1000000000000 : ℝ), (13036128479667/100000000000000 : ℝ), (1760265159317/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289038843/10000000000 : ℝ)|^8319 ≤ (429572425229/1000000000000 : ℝ)^6271
        have hw : |(5289038843/10000000000 : ℝ)|=(5289038843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2152704317/10000000000 : ℝ)|^8319 ≤ (13036128479667/100000000000000 : ℝ)^6271
        have hw : |(-2152704317/10000000000 : ℝ)|=(2152704317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168317031/312500000 : ℝ)|^8319 ≤ (1760265159317/4000000000000 : ℝ)^6271
        have hw : |(168317031/312500000 : ℝ)|=(168317031/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_10 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66112987/125000000 : ℝ)*x 0 + (5386144463/10000000000 : ℝ)*x 1 + (-2152704873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66112987/125000000 : ℝ)^8319 ≤ (42957243783507/100000000000000 : ℝ)^6271 := by
    have hnat : (66112987 : ℕ)^8319*100000000000000^6271 ≤ 42957243783507^6271*125000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66112987 125000000 42957243783507 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386144463/10000000000 : ℝ)^8319 ≤ (44006623249289/100000000000000 : ℝ)^6271 := by
    have hnat : (5386144463 : ℕ)^8319*100000000000000^6271 ≤ 44006623249289^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386144463 10000000000 44006623249289 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152704873/10000000000 : ℝ)^8319 ≤ (13036132946229/100000000000000 : ℝ)^6271 := by
    have hnat : (2152704873 : ℕ)^8319*100000000000000^6271 ≤ 13036132946229^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152704873 10000000000 13036132946229 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66112987/125000000 : ℝ), (5386144463/10000000000 : ℝ), (-2152704873/10000000000 : ℝ)] ![(42957243783507/100000000000000 : ℝ), (44006623249289/100000000000000 : ℝ), (13036132946229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66112987/125000000 : ℝ)|^8319 ≤ (42957243783507/100000000000000 : ℝ)^6271
        have hw : |(66112987/125000000 : ℝ)|=(66112987/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386144463/10000000000 : ℝ)|^8319 ≤ (44006623249289/100000000000000 : ℝ)^6271
        have hw : |(5386144463/10000000000 : ℝ)|=(5386144463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2152704873/10000000000 : ℝ)|^8319 ≤ (13036132946229/100000000000000 : ℝ)^6271
        have hw : |(-2152704873/10000000000 : ℝ)|=(2152704873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_11 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2248032397/5000000000 : ℝ)*x 0 + (860869513/2000000000 : ℝ)*x 1 + (430434829/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2248032397/5000000000 : ℝ)^8319 ≤ (34630095407729/100000000000000 : ℝ)^6271 := by
    have hnat : (2248032397 : ℕ)^8319*100000000000000^6271 ≤ 34630095407729^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248032397 5000000000 34630095407729 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (860869513/2000000000 : ℝ)^8319 ≤ (16342474320103/50000000000000 : ℝ)^6271 := by
    have hnat : (860869513 : ℕ)^8319*50000000000000^6271 ≤ 16342474320103^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860869513 2000000000 16342474320103 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430434829/1000000000 : ℝ)^8319 ≤ (163424779717/500000000000 : ℝ)^6271 := by
    have hnat : (430434829 : ℕ)^8319*500000000000^6271 ≤ 163424779717^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430434829 1000000000 163424779717 500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2248032397/5000000000 : ℝ), (860869513/2000000000 : ℝ), (430434829/1000000000 : ℝ)] ![(34630095407729/100000000000000 : ℝ), (16342474320103/50000000000000 : ℝ), (163424779717/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2248032397/5000000000 : ℝ)|^8319 ≤ (34630095407729/100000000000000 : ℝ)^6271
        have hw : |(2248032397/5000000000 : ℝ)|=(2248032397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(860869513/2000000000 : ℝ)|^8319 ≤ (16342474320103/50000000000000 : ℝ)^6271
        have hw : |(860869513/2000000000 : ℝ)|=(860869513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(430434829/1000000000 : ℝ)|^8319 ≤ (163424779717/500000000000 : ℝ)^6271
        have hw : |(430434829/1000000000 : ℝ)|=(430434829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_12 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2101032503/10000000000 : ℝ)*x 0 + (1088047483/2000000000 : ℝ)*x 1 + (1318225387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101032503/10000000000 : ℝ)^8319 ≤ (12622664756061/100000000000000 : ℝ)^6271 := by
    have hnat : (2101032503 : ℕ)^8319*100000000000000^6271 ≤ 12622664756061^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101032503 10000000000 12622664756061 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088047483/2000000000 : ℝ)^8319 ≤ (1114846900947/2500000000000 : ℝ)^6271 := by
    have hnat : (1088047483 : ℕ)^8319*2500000000000^6271 ≤ 1114846900947^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088047483 2000000000 1114846900947 2500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318225387/2500000000 : ℝ)^8319 ≤ (4278345918827/10000000000000 : ℝ)^6271 := by
    have hnat : (1318225387 : ℕ)^8319*10000000000000^6271 ≤ 4278345918827^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318225387 2500000000 4278345918827 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2101032503/10000000000 : ℝ), (1088047483/2000000000 : ℝ), (1318225387/2500000000 : ℝ)] ![(12622664756061/100000000000000 : ℝ), (1114846900947/2500000000000 : ℝ), (4278345918827/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2101032503/10000000000 : ℝ)|^8319 ≤ (12622664756061/100000000000000 : ℝ)^6271
        have hw : |(-2101032503/10000000000 : ℝ)|=(2101032503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088047483/2000000000 : ℝ)|^8319 ≤ (1114846900947/2500000000000 : ℝ)^6271
        have hw : |(1088047483/2000000000 : ℝ)|=(1088047483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318225387/2500000000 : ℝ)|^8319 ≤ (4278345918827/10000000000000 : ℝ)^6271
        have hw : |(1318225387/2500000000 : ℝ)|=(1318225387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_13 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684537569/5000000000 : ℝ)*x 0 + (-137325379/625000000 : ℝ)*x 1 + (527290159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684537569/5000000000 : ℝ)^8319 ≤ (21910855483809/50000000000000 : ℝ)^6271 := by
    have hnat : (2684537569 : ℕ)^8319*50000000000000^6271 ≤ 21910855483809^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684537569 5000000000 21910855483809 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137325379/625000000 : ℝ)^8319 ≤ (13394829377847/100000000000000 : ℝ)^6271 := by
    have hnat : (137325379 : ℕ)^8319*100000000000000^6271 ≤ 13394829377847^6271*625000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137325379 625000000 13394829377847 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527290159/1000000000 : ℝ)^8319 ≤ (5347932455043/12500000000000 : ℝ)^6271 := by
    have hnat : (527290159 : ℕ)^8319*12500000000000^6271 ≤ 5347932455043^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527290159 1000000000 5347932455043 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684537569/5000000000 : ℝ), (-137325379/625000000 : ℝ), (527290159/1000000000 : ℝ)] ![(21910855483809/50000000000000 : ℝ), (13394829377847/100000000000000 : ℝ), (5347932455043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684537569/5000000000 : ℝ)|^8319 ≤ (21910855483809/50000000000000 : ℝ)^6271
        have hw : |(2684537569/5000000000 : ℝ)|=(2684537569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137325379/625000000 : ℝ)|^8319 ≤ (13394829377847/100000000000000 : ℝ)^6271
        have hw : |(-137325379/625000000 : ℝ)|=(137325379/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527290159/1000000000 : ℝ)|^8319 ≤ (5347932455043/12500000000000 : ℝ)^6271
        have hw : |(527290159/1000000000 : ℝ)|=(527290159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_14 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369075117/10000000000 : ℝ)*x 0 + (105458031/200000000 : ℝ)*x 1 + (-17165673/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369075117/10000000000 : ℝ)^8319 ≤ (43821710740243/100000000000000 : ℝ)^6271 := by
    have hnat : (5369075117 : ℕ)^8319*100000000000000^6271 ≤ 43821710740243^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369075117 10000000000 43821710740243 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105458031/200000000 : ℝ)^8319 ≤ (42783459209797/100000000000000 : ℝ)^6271 := by
    have hnat : (105458031 : ℕ)^8319*100000000000000^6271 ≤ 42783459209797^6271*200000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105458031 200000000 42783459209797 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17165673/78125000 : ℝ)^8319 ≤ (13394830024827/100000000000000 : ℝ)^6271 := by
    have hnat : (17165673 : ℕ)^8319*100000000000000^6271 ≤ 13394830024827^6271*78125000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17165673 78125000 13394830024827 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369075117/10000000000 : ℝ), (105458031/200000000 : ℝ), (-17165673/78125000 : ℝ)] ![(43821710740243/100000000000000 : ℝ), (42783459209797/100000000000000 : ℝ), (13394830024827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369075117/10000000000 : ℝ)|^8319 ≤ (43821710740243/100000000000000 : ℝ)^6271
        have hw : |(5369075117/10000000000 : ℝ)|=(5369075117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105458031/200000000 : ℝ)|^8319 ≤ (42783459209797/100000000000000 : ℝ)^6271
        have hw : |(105458031/200000000 : ℝ)|=(105458031/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17165673/78125000 : ℝ)|^8319 ≤ (13394830024827/100000000000000 : ℝ)^6271
        have hw : |(-17165673/78125000 : ℝ)|=(17165673/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_box_15 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060125861/2500000000 : ℝ)*x 0 + (110803151/250000000 : ℝ)*x 1 + (1108031513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060125861/2500000000 : ℝ)^8319 ≤ (32043386047039/100000000000000 : ℝ)^6271 := by
    have hnat : (1060125861 : ℕ)^8319*100000000000000^6271 ≤ 32043386047039^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060125861 2500000000 32043386047039 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110803151/250000000 : ℝ)^8319 ≤ (33978306909249/100000000000000 : ℝ)^6271 := by
    have hnat : (110803151 : ℕ)^8319*100000000000000^6271 ≤ 33978306909249^6271*250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110803151 250000000 33978306909249 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108031513/2500000000 : ℝ)^8319 ≤ (33978307031289/100000000000000 : ℝ)^6271 := by
    have hnat : (1108031513 : ℕ)^8319*100000000000000^6271 ≤ 33978307031289^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108031513 2500000000 33978307031289 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060125861/2500000000 : ℝ), (110803151/250000000 : ℝ), (1108031513/2500000000 : ℝ)] ![(32043386047039/100000000000000 : ℝ), (33978306909249/100000000000000 : ℝ), (33978307031289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060125861/2500000000 : ℝ)|^8319 ≤ (32043386047039/100000000000000 : ℝ)^6271
        have hw : |(1060125861/2500000000 : ℝ)|=(1060125861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110803151/250000000 : ℝ)|^8319 ≤ (33978306909249/100000000000000 : ℝ)^6271
        have hw : |(110803151/250000000 : ℝ)|=(110803151/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108031513/2500000000 : ℝ)|^8319 ≤ (33978307031289/100000000000000 : ℝ)^6271
        have hw : |(1108031513/2500000000 : ℝ)|=(1108031513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1126_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62229/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29643/50000 : ℝ) ∧ (79759/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83089/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11333/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11333/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11333/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11333/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11333/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11333/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11333/100000 : ℝ) ^ (4159/1024 : ℝ) ≤ (2885556601438847/20000000000000000000 : ℝ) := by
    have hpowers : (11333/100000 : ℝ)^4159 ≤ (2885556601438847/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11333 : ℕ)^4159*20000000000000000000^1024 ≤ 2885556601438847^1024*100000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11333 100000 2885556601438847 20000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11333/100000 : ℝ)) (X := (2885556601438847/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14039/100000 : ℝ) ^ (4159/1024 : ℝ) ≤ (137703785062779/400000000000000000 : ℝ) := by
    have hpowers : (14039/100000 : ℝ)^4159 ≤ (137703785062779/400000000000000000 : ℝ)^1024 := by
      have hnat : (14039 : ℕ)^4159*400000000000000000^1024 ≤ 137703785062779^1024*100000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14039 100000 137703785062779 400000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14039/100000 : ℝ)) (X := (137703785062779/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002885556601438847/10000000000000000000 : ℝ) ≤ (5000355192193371/5000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (10002885556601438847/10000000000000000000 : ℝ)^1024 ≤ (5000355192193371/5000000000000000 : ℝ)^4159 := by
      have hnat : (10002885556601438847 : ℕ)^1024*5000000000000000^4159 ≤ 5000355192193371^4159*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002885556601438847 10000000000000000000 5000355192193371 5000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000355192193371/5000000000000000 : ℝ)) (X := (10002885556601438847/10000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009770745854577797/20000000000000000000 : ℝ) ≤ (2500300655267201/2500000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (20009770745854577797/20000000000000000000 : ℝ)^1024 ≤ (2500300655267201/2500000000000000 : ℝ)^4159 := by
      have hnat : (20009770745854577797 : ℕ)^1024*2500000000000000^4159 ≤ 2500300655267201^4159*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009770745854577797 20000000000000000000 2500300655267201 2500000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500300655267201/2500000000000000 : ℝ)) (X := (20009770745854577797/20000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (200137703785062779/200000000000000000 : ℝ) ≤ (5000847428875433/5000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (200137703785062779/200000000000000000 : ℝ)^1024 ≤ (5000847428875433/5000000000000000 : ℝ)^4159 := by
      have hnat : (200137703785062779 : ℕ)^1024*5000000000000000^4159 ≤ 5000847428875433^4159*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200137703785062779 200000000000000000 5000847428875433 5000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000847428875433/5000000000000000 : ℝ)) (X := (200137703785062779/200000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2885556601438847/20000000000000000000 : ℝ) ≤ ((84533641448484083/84562500000000000 : ℝ)+2*(246118341031/135300000000000 : ℝ)*(11333/100000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (84533641448484083/84562500000000000 : ℝ)+2*(246118341031/135300000000000 : ℝ)*(11333/100000 : ℝ)=(5000355192193371/5000000000000000 : ℝ) by norm_num, show 1+2*(2885556601438847/20000000000000000000 : ℝ)=(10002885556601438847/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(137703785062779/400000000000000000 : ℝ)+(2885556601438847/20000000000000000000 : ℝ) ≤ ((84533641448484083/84562500000000000 : ℝ)+(246118341031/135300000000000 : ℝ)*((14039/100000 : ℝ)+(11333/100000 : ℝ)))^(4159/1024 : ℝ) := by
    rw [show (84533641448484083/84562500000000000 : ℝ)+(246118341031/135300000000000 : ℝ)*((14039/100000 : ℝ)+(11333/100000 : ℝ))=(2500300655267201/2500000000000000 : ℝ) by norm_num, show 1+(137703785062779/400000000000000000 : ℝ)+(2885556601438847/20000000000000000000 : ℝ)=(20009770745854577797/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(137703785062779/400000000000000000 : ℝ) ≤ ((84533641448484083/84562500000000000 : ℝ)+2*(246118341031/135300000000000 : ℝ)*(14039/100000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (84533641448484083/84562500000000000 : ℝ)+2*(246118341031/135300000000000 : ℝ)*(14039/100000 : ℝ)=(5000847428875433/5000000000000000 : ℝ) by norm_num, show 1+2*(137703785062779/400000000000000000 : ℝ)=(200137703785062779/200000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84533641448484083/84562500000000000 : ℝ)*(X 1 0+X 2 0)+(246118341031/135300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (11333/100000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (84533641448484083/84562500000000000 : ℝ)) (alpha := (246118341031/135300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84533641448484083/84562500000000000 : ℝ)*(X 0 1+X 2 1)+(246118341031/135300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (11333/100000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (84533641448484083/84562500000000000 : ℝ)) (alpha := (246118341031/135300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84533641448484083/84562500000000000 : ℝ)*(X 0 2+X 1 2)+(246118341031/135300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (11333/100000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (84533641448484083/84562500000000000 : ℝ)) (alpha := (246118341031/135300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2047138941/10000000000 : ℝ)*X 0 0+(5376537431/10000000000 : ℝ)*X 0 1+(672067163/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((661979027/1250000000 : ℝ)*X 1 0+(-2156548659/10000000000 : ℝ)*X 1 1+(1075307493/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((661979051/1250000000 : ℝ)*X 2 0+(1344134319/2500000000 : ℝ)*X 2 1+(-2156548657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2237326207/5000000000 : ℝ)*X 0 0+(2157597231/5000000000 : ℝ)*X 0 1+(86303897/200000000 : ℝ)*X 0 2+(2237326207/5000000000 : ℝ)*X 1 0+(2157597231/5000000000 : ℝ)*X 1 1+(86303897/200000000 : ℝ)*X 1 2+(2237326207/5000000000 : ℝ)*X 2 0+(2157597231/5000000000 : ℝ)*X 2 1+(86303897/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-287921867/1250000000 : ℝ)*X 0 0+(5280932773/10000000000 : ℝ)*X 0 1+(1320233233/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1340850381/2500000000 : ℝ)*X 1 0+(-1097054251/5000000000 : ℝ)*X 1 1+(2640466309/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340850333/2500000000 : ℝ)*X 2 0+(1056186529/2000000000 : ℝ)*X 2 1+(-548527181/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((212943097/500000000 : ℝ)*X 0 0+(884613811/2000000000 : ℝ)*X 0 1+(2211534399/5000000000 : ℝ)*X 0 2+(212943097/500000000 : ℝ)*X 1 0+(884613811/2000000000 : ℝ)*X 1 1+(2211534399/5000000000 : ℝ)*X 1 2+(212943097/500000000 : ℝ)*X 2 0+(884613811/2000000000 : ℝ)*X 2 1+(2211534399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2249810727/10000000000 : ℝ)*X 0 0+(208637727/400000000 : ℝ)*X 0 1+(673268107/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289038843/10000000000 : ℝ)*X 1 0+(-2152704317/10000000000 : ℝ)*X 1 1+(168317031/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((66112987/125000000 : ℝ)*X 2 0+(5386144463/10000000000 : ℝ)*X 2 1+(-2152704873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2248032397/5000000000 : ℝ)*X 0 0+(860869513/2000000000 : ℝ)*X 0 1+(430434829/1000000000 : ℝ)*X 0 2+(2248032397/5000000000 : ℝ)*X 1 0+(860869513/2000000000 : ℝ)*X 1 1+(430434829/1000000000 : ℝ)*X 1 2+(2248032397/5000000000 : ℝ)*X 2 0+(860869513/2000000000 : ℝ)*X 2 1+(430434829/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2101032503/10000000000 : ℝ)*X 0 0+(1088047483/2000000000 : ℝ)*X 0 1+(1318225387/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684537569/5000000000 : ℝ)*X 1 0+(-137325379/625000000 : ℝ)*X 1 1+(527290159/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369075117/10000000000 : ℝ)*X 2 0+(105458031/200000000 : ℝ)*X 2 1+(-17165673/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1060125861/2500000000 : ℝ)*X 0 0+(110803151/250000000 : ℝ)*X 0 1+(1108031513/2500000000 : ℝ)*X 0 2+(1060125861/2500000000 : ℝ)*X 1 0+(110803151/250000000 : ℝ)*X 1 1+(1108031513/2500000000 : ℝ)*X 1 2+(1060125861/2500000000 : ℝ)*X 2 0+(110803151/250000000 : ℝ)*X 2 1+(1108031513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62229/100000 : ℝ) ≤ (-54813083470060016808682406913/88085937500000000000000000000 : ℝ) := by norm_num
    linear_combination (48514417/50000000000000 : ℝ)*(lower0) + (26120291/50000000000000 : ℝ)*(upper1) + (80500577/50000000000000 : ℝ)*(lower4) + (976769076478647/25000000000000 : ℝ)*(major0) + (976769076478647/25000000000000 : ℝ)*(major1) + (976769076478647/25000000000000 : ℝ)*(major2) + (2873869773/25000000000000 : ℝ)*(sp1) + (20503063621/100000000000000 : ℝ)*(sp2) + (1508472979/50000000000000 : ℝ)*(sp3) + (5215535283265707/100000000000000 : ℝ)*(sp4) + (5215525811021557/100000000000000 : ℝ)*(sp5) + (1303879200859257/25000000000000 : ℝ)*(sp6) + (654838640967901/25000000000000 : ℝ)*(sp7) + (1011617471/50000000000000 : ℝ)*(sp12) + (1309678790408781/50000000000000 : ℝ)*(f.failure) + (5215537306500649/100000000000000 : ℝ)*(f.sum) + (3587046720197/1127500000000000000000000000 : ℝ)*base66 + (1574563231893491/1409375000000000000000000000000 : ℝ)*base68 + (2297133652241471/352343750000000000000000000000 : ℝ)*base69 + (963550019678971/352343750000000000000000000000 : ℝ)*base71 + (21301457169647/1127500000000000000000000000 : ℝ)*base74 + (2985765328598567/704687500000000000000000000000 : ℝ)*base75 + (509349665911149/88085937500000000000000000000 : ℝ)*base77 + (132780128147721/352343750000000000000000000000 : ℝ)*base79 + (4703365373211/2255000000000000000000000000 : ℝ)*base81 + (272457/625000000000000000000 : ℝ)*base90 + (272457/625000000000000000000 : ℝ)*base92 + (272457/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29643/50000 : ℝ) ≤ (208899748712192034935917879979/352343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (42545033/50000000000000 : ℝ)*(upper0) + (12579773/50000000000000 : ℝ)*(lower1) + (42512439/100000000000000 : ℝ)*(upper4) + (26765321/100000000000000 : ℝ)*(upper5) + (496370941988453/12500000000000 : ℝ)*(major0) + (496370941988453/12500000000000 : ℝ)*(major1) + (496370941988453/12500000000000 : ℝ)*(major2) + (2629990529999619/50000000000000 : ℝ)*(sp0) + (5259974833730259/100000000000000 : ℝ)*(sp1) + (525995690624243/10000000000000 : ℝ)*(sp2) + (2662190731614151/100000000000000 : ℝ)*(sp3) + (6226268979/100000000000000 : ℝ)*(sp5) + (203354743/50000000000000 : ℝ)*(sp7) + (3019219601/12500000000000 : ℝ)*(sp10) + (1331095569161819/50000000000000 : ℝ)*(f.failure) + (2629990529999619/50000000000000 : ℝ)*(f.sum) + (6376451862149/1691250000000000000000000000 : ℝ)*base66 + (36283720804114691/704687500000000000000000000000 : ℝ)*base67 + (2840626575270941/704687500000000000000000000000 : ℝ)*base69 + (774495534985309/704687500000000000000000000000 : ℝ)*base72 + (284806711457299/6765000000000000000000000000 : ℝ)*base73 + (9145868827557507/1409375000000000000000000000000 : ℝ)*base75 + (1827800411608441/704687500000000000000000000000 : ℝ)*base77 + (2601000370880783/352343750000000000000000000000 : ℝ)*base79 + (2287565007271/1691250000000000000000000000 : ℝ)*base81 + (5104257/625000000000000000000 : ℝ)*base89 + (5104257/625000000000000000000 : ℝ)*base91 + (5104257/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79759/100000 : ℝ) ≤ (102194473614480286698462680429/128125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (364666167/100000000000000 : ℝ)*(upper0) + (85323931/100000000000000 : ℝ)*(upper2) + (27224789/50000000000000 : ℝ)*(lower3) + (110712231/25000000000000 : ℝ)*(lower5) + (277433057297459/6250000000000 : ℝ)*(major0) + (277433057297459/6250000000000 : ℝ)*(major1) + (277433057297459/6250000000000 : ℝ)*(major2) + (113393999567/50000000000000 : ℝ)*(sp1) + (83145658407/100000000000000 : ℝ)*(sp3) + (3969741139/50000000000000 : ℝ)*(sp4) + (5875343843007423/100000000000000 : ℝ)*(sp8) + (5875124994490567/100000000000000 : ℝ)*(sp9) + (5875351782489701/100000000000000 : ℝ)*(sp10) + (2975835725243229/100000000000000 : ℝ)*(sp11) + (743979717725409/25000000000000 : ℝ)*(f.failure) + (5875351782489701/100000000000000 : ℝ)*(f.sum) + (8191906373489/6765000000000000000000000000 : ℝ)*base65 + (1338248365174921/704687500000000000000000000000 : ℝ)*base67 + (1614052049924199/176171875000000000000000000000 : ℝ)*base69 + (7634389183909217/1409375000000000000000000000000 : ℝ)*base71 + (26898492268223/3382500000000000000000000000 : ℝ)*base74 + (3993324971431171/704687500000000000000000000000 : ℝ)*base75 + (2433464036770273/352343750000000000000000000000 : ℝ)*base77 + (7411533708231171/704687500000000000000000000000 : ℝ)*base79 + (11016254690609/6765000000000000000000000000 : ℝ)*base81 + (936973/312500000000000000000 : ℝ)*base90 + (936973/312500000000000000000 : ℝ)*base92 + (936973/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83089/100000 : ℝ) ≤ (-53227002181829229743792904891/64062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2399897/100000000000000 : ℝ)*(lower0) + (14707/1250000000000 : ℝ)*(upper1) + (25505787/100000000000000 : ℝ)*(upper3) + (20129681/50000000000000 : ℝ)*(lower4) + (2236903719168111/50000000000000 : ℝ)*(major0) + (2236903719168111/50000000000000 : ℝ)*(major1) + (2236903719168111/50000000000000 : ℝ)*(major2) + (47937649/5000000000000 : ℝ)*(sp4) + (12209550271/25000000000000 : ℝ)*(sp6) + (21537514183/100000000000000 : ℝ)*(sp7) + (747000919770923/12500000000000 : ℝ)*(sp12) + (5976008316920363/100000000000000 : ℝ)*(sp13) + (5975959478719279/100000000000000 : ℝ)*(sp14) + (37491004662083/1250000000000 : ℝ)*(sp15) + (374912738810103/12500000000000 : ℝ)*(f.failure) + (5976008316920363/100000000000000 : ℝ)*(f.sum) + (2325399391723/1127500000000000000000000000 : ℝ)*base66 + (11618658755354071/1409375000000000000000000000000 : ℝ)*base67 + (12023194498654451/352343750000000000000000000000 : ℝ)*base70 + (1086028431995549/352343750000000000000000000000 : ℝ)*base71 + (2164254673121/2255000000000000000000000000 : ℝ)*base74 + (3651896237881723/704687500000000000000000000000 : ℝ)*base75 + (14763215177710321/1409375000000000000000000000000 : ℝ)*base77 + (19706943873385321/1409375000000000000000000000000 : ℝ)*base79 + (7256078977227/281875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2010909/156250000000000000000 : ℝ)*base89 + (2010909/156250000000000000000 : ℝ)*base91 + (2010909/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1126_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29643/50000 : ℝ) else (79759/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83089/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1126_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1126_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29643/50000 : ℝ) else (79759/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83089/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1126_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29643/50000 : ℝ) else (79759/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83089/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1126_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
