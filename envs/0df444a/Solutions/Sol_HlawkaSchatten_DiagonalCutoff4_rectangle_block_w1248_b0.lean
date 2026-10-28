-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1248_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:22:20.054536+00:00
-- url     : https://prove2.me/submissions/b6d4b3eb-3004-4d46-ab67-dc9c1edf0736

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
theorem support_rectangle_w1248_s0_0 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-929355077/5000000000 : ℝ)*x 0 + (1206030793/2000000000 : ℝ)*x 1 + (4793730289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929355077/5000000000 : ℝ)^8441 ≤ (1355231112559/12500000000000 : ℝ)^6393 := by
    have hnat : (929355077 : ℕ)^8441*12500000000000^6393 ≤ 1355231112559^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929355077 5000000000 1355231112559 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206030793/2000000000 : ℝ)^8441 ≤ (10256200813567/20000000000000 : ℝ)^6393 := by
    have hnat : (1206030793 : ℕ)^8441*20000000000000^6393 ≤ 10256200813567^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206030793 2000000000 10256200813567 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4793730289/10000000000 : ℝ)^8441 ≤ (94692867517/250000000000 : ℝ)^6393 := by
    have hnat : (4793730289 : ℕ)^8441*250000000000^6393 ≤ 94692867517^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793730289 10000000000 94692867517 250000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929355077/5000000000 : ℝ), (1206030793/2000000000 : ℝ), (4793730289/10000000000 : ℝ)] ![(1355231112559/12500000000000 : ℝ), (10256200813567/20000000000000 : ℝ), (94692867517/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929355077/5000000000 : ℝ)|^8441 ≤ (1355231112559/12500000000000 : ℝ)^6393
        have hw : |(-929355077/5000000000 : ℝ)|=(929355077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206030793/2000000000 : ℝ)|^8441 ≤ (10256200813567/20000000000000 : ℝ)^6393
        have hw : |(1206030793/2000000000 : ℝ)|=(1206030793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4793730289/10000000000 : ℝ)|^8441 ≤ (94692867517/250000000000 : ℝ)^6393
        have hw : |(4793730289/10000000000 : ℝ)|=(4793730289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s0_1 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5510821479/10000000000 : ℝ)*x 0 + (-2565382337/10000000000 : ℝ)*x 1 + (4793730231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510821479/10000000000 : ℝ)^8441 ≤ (11382952071807/25000000000000 : ℝ)^6393 := by
    have hnat : (5510821479 : ℕ)^8441*25000000000000^6393 ≤ 11382952071807^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510821479 10000000000 11382952071807 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2565382337/10000000000 : ℝ)^8441 ≤ (414776132499/2500000000000 : ℝ)^6393 := by
    have hnat : (2565382337 : ℕ)^8441*2500000000000^6393 ≤ 414776132499^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565382337 10000000000 414776132499 2500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4793730231/10000000000 : ℝ)^8441 ≤ (37877146401709/100000000000000 : ℝ)^6393 := by
    have hnat : (4793730231 : ℕ)^8441*100000000000000^6393 ≤ 37877146401709^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793730231 10000000000 37877146401709 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510821479/10000000000 : ℝ), (-2565382337/10000000000 : ℝ), (4793730231/10000000000 : ℝ)] ![(11382952071807/25000000000000 : ℝ), (414776132499/2500000000000 : ℝ), (37877146401709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510821479/10000000000 : ℝ)|^8441 ≤ (11382952071807/25000000000000 : ℝ)^6393
        have hw : |(5510821479/10000000000 : ℝ)|=(5510821479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2565382337/10000000000 : ℝ)|^8441 ≤ (414776132499/2500000000000 : ℝ)^6393
        have hw : |(-2565382337/10000000000 : ℝ)|=(2565382337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4793730231/10000000000 : ℝ)|^8441 ≤ (37877146401709/100000000000000 : ℝ)^6393
        have hw : |(4793730231/10000000000 : ℝ)|=(4793730231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s0_2 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2755410697/5000000000 : ℝ)*x 0 + (4793730321/10000000000 : ℝ)*x 1 + (-1282691167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755410697/5000000000 : ℝ)^8441 ≤ (45531807359957/100000000000000 : ℝ)^6393 := by
    have hnat : (2755410697 : ℕ)^8441*100000000000000^6393 ≤ 45531807359957^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755410697 5000000000 45531807359957 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4793730321/10000000000 : ℝ)^8441 ≤ (37877147340643/100000000000000 : ℝ)^6393 := by
    have hnat : (4793730321 : ℕ)^8441*100000000000000^6393 ≤ 37877147340643^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793730321 10000000000 37877147340643 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282691167/5000000000 : ℝ)^8441 ≤ (16591045274343/100000000000000 : ℝ)^6393 := by
    have hnat : (1282691167 : ℕ)^8441*100000000000000^6393 ≤ 16591045274343^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282691167 5000000000 16591045274343 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755410697/5000000000 : ℝ), (4793730321/10000000000 : ℝ), (-1282691167/5000000000 : ℝ)] ![(45531807359957/100000000000000 : ℝ), (37877147340643/100000000000000 : ℝ), (16591045274343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755410697/5000000000 : ℝ)|^8441 ≤ (45531807359957/100000000000000 : ℝ)^6393
        have hw : |(2755410697/5000000000 : ℝ)|=(2755410697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4793730321/10000000000 : ℝ)|^8441 ≤ (37877147340643/100000000000000 : ℝ)^6393
        have hw : |(4793730321/10000000000 : ℝ)|=(4793730321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1282691167/5000000000 : ℝ)|^8441 ≤ (16591045274343/100000000000000 : ℝ)^6393
        have hw : |(-1282691167/5000000000 : ℝ)|=(1282691167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s0_3 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4192550711/10000000000 : ℝ)*x 0 + (623333479/2000000000 : ℝ)*x 1 + (5627746029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192550711/10000000000 : ℝ)^8441 ≤ (15867522220881/50000000000000 : ℝ)^6393 := by
    have hnat : (4192550711 : ℕ)^8441*50000000000000^6393 ≤ 15867522220881^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192550711 10000000000 15867522220881 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623333479/2000000000 : ℝ)^8441 ≤ (4290658970523/20000000000000 : ℝ)^6393 := by
    have hnat : (623333479 : ℕ)^8441*20000000000000^6393 ≤ 4290658970523^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623333479 2000000000 4290658970523 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5627746029/10000000000 : ℝ)^8441 ≤ (11702915173383/25000000000000 : ℝ)^6393 := by
    have hnat : (5627746029 : ℕ)^8441*25000000000000^6393 ≤ 11702915173383^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5627746029 10000000000 11702915173383 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192550711/10000000000 : ℝ), (623333479/2000000000 : ℝ), (5627746029/10000000000 : ℝ)] ![(15867522220881/50000000000000 : ℝ), (4290658970523/20000000000000 : ℝ), (11702915173383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192550711/10000000000 : ℝ)|^8441 ≤ (15867522220881/50000000000000 : ℝ)^6393
        have hw : |(4192550711/10000000000 : ℝ)|=(4192550711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623333479/2000000000 : ℝ)|^8441 ≤ (4290658970523/20000000000000 : ℝ)^6393
        have hw : |(623333479/2000000000 : ℝ)|=(623333479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5627746029/10000000000 : ℝ)|^8441 ≤ (11702915173383/25000000000000 : ℝ)^6393
        have hw : |(5627746029/10000000000 : ℝ)|=(5627746029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s0_4 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1863550629/10000000000 : ℝ)*x 0 + (4825566957/10000000000 : ℝ)*x 1 + (374824489/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863550629/10000000000 : ℝ)^8441 ≤ (10879143836709/100000000000000 : ℝ)^6393 := by
    have hnat : (1863550629 : ℕ)^8441*100000000000000^6393 ≤ 10879143836709^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863550629 10000000000 10879143836709 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4825566957/10000000000 : ℝ)^8441 ≤ (7641927850523/20000000000000 : ℝ)^6393 := by
    have hnat : (4825566957 : ℕ)^8441*20000000000000^6393 ≤ 7641927850523^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4825566957 10000000000 7641927850523 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374824489/625000000 : ℝ)^8441 ≤ (50911216896051/100000000000000 : ℝ)^6393 := by
    have hnat : (374824489 : ℕ)^8441*100000000000000^6393 ≤ 50911216896051^6393*625000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374824489 625000000 50911216896051 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1863550629/10000000000 : ℝ), (4825566957/10000000000 : ℝ), (374824489/625000000 : ℝ)] ![(10879143836709/100000000000000 : ℝ), (7641927850523/20000000000000 : ℝ), (50911216896051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1863550629/10000000000 : ℝ)|^8441 ≤ (10879143836709/100000000000000 : ℝ)^6393
        have hw : |(-1863550629/10000000000 : ℝ)|=(1863550629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4825566957/10000000000 : ℝ)|^8441 ≤ (7641927850523/20000000000000 : ℝ)^6393
        have hw : |(4825566957/10000000000 : ℝ)|=(4825566957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(374824489/625000000 : ℝ)|^8441 ≤ (50911216896051/100000000000000 : ℝ)^6393
        have hw : |(374824489/625000000 : ℝ)|=(374824489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s0_5 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2587191407/5000000000 : ℝ)*x 0 + (-680959269/5000000000 : ℝ)*x 1 + (5997194153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587191407/5000000000 : ℝ)^8441 ≤ (10474493778417/25000000000000 : ℝ)^6393 := by
    have hnat : (2587191407 : ℕ)^8441*25000000000000^6393 ≤ 10474493778417^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587191407 5000000000 10474493778417 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680959269/5000000000 : ℝ)^8441 ≤ (7190781865827/100000000000000 : ℝ)^6393 := by
    have hnat : (680959269 : ℕ)^8441*100000000000000^6393 ≤ 7190781865827^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680959269 5000000000 7190781865827 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5997194153/10000000000 : ℝ)^8441 ≤ (12727810750271/25000000000000 : ℝ)^6393 := by
    have hnat : (5997194153 : ℕ)^8441*25000000000000^6393 ≤ 12727810750271^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5997194153 10000000000 12727810750271 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587191407/5000000000 : ℝ), (-680959269/5000000000 : ℝ), (5997194153/10000000000 : ℝ)] ![(10474493778417/25000000000000 : ℝ), (7190781865827/100000000000000 : ℝ), (12727810750271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587191407/5000000000 : ℝ)|^8441 ≤ (10474493778417/25000000000000 : ℝ)^6393
        have hw : |(2587191407/5000000000 : ℝ)|=(2587191407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-680959269/5000000000 : ℝ)|^8441 ≤ (7190781865827/100000000000000 : ℝ)^6393
        have hw : |(-680959269/5000000000 : ℝ)|=(680959269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5997194153/10000000000 : ℝ)|^8441 ≤ (12727810750271/25000000000000 : ℝ)^6393
        have hw : |(5997194153/10000000000 : ℝ)|=(5997194153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s0_6 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (517438377/1000000000 : ℝ)*x 0 + (5997192263/10000000000 : ℝ)*x 1 + (-85120007/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517438377/1000000000 : ℝ)^8441 ≤ (4189798533439/10000000000000 : ℝ)^6393 := by
    have hnat : (517438377 : ℕ)^8441*10000000000000^6393 ≤ 4189798533439^6393*1000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517438377 1000000000 4189798533439 10000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5997192263/10000000000 : ℝ)^8441 ≤ (6363902727083/12500000000000 : ℝ)^6393 := by
    have hnat : (5997192263 : ℕ)^8441*12500000000000^6393 ≤ 6363902727083^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5997192263 10000000000 6363902727083 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85120007/625000000 : ℝ)^8441 ≤ (3595396419333/50000000000000 : ℝ)^6393 := by
    have hnat : (85120007 : ℕ)^8441*50000000000000^6393 ≤ 3595396419333^6393*625000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85120007 625000000 3595396419333 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517438377/1000000000 : ℝ), (5997192263/10000000000 : ℝ), (-85120007/625000000 : ℝ)] ![(4189798533439/10000000000000 : ℝ), (6363902727083/12500000000000 : ℝ), (3595396419333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517438377/1000000000 : ℝ)|^8441 ≤ (4189798533439/10000000000000 : ℝ)^6393
        have hw : |(517438377/1000000000 : ℝ)|=(517438377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5997192263/10000000000 : ℝ)|^8441 ≤ (6363902727083/12500000000000 : ℝ)^6393
        have hw : |(5997192263/10000000000 : ℝ)|=(5997192263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85120007/625000000 : ℝ)|^8441 ≤ (3595396419333/50000000000000 : ℝ)^6393
        have hw : |(-85120007/625000000 : ℝ)|=(85120007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s0_7 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (210119139/500000000 : ℝ)*x 0 + (2781546843/5000000000 : ℝ)*x 1 + (1591802487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210119139/500000000 : ℝ)^8441 ≤ (6366669087521/20000000000000 : ℝ)^6393 := by
    have hnat : (210119139 : ℕ)^8441*20000000000000^6393 ≤ 6366669087521^6393*500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210119139 500000000 6366669087521 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2781546843/5000000000 : ℝ)^8441 ≤ (46102914008707/100000000000000 : ℝ)^6393 := by
    have hnat : (2781546843 : ℕ)^8441*100000000000000^6393 ≤ 46102914008707^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781546843 5000000000 46102914008707 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1591802487/5000000000 : ℝ)^8441 ≤ (2757967566803/12500000000000 : ℝ)^6393 := by
    have hnat : (1591802487 : ℕ)^8441*12500000000000^6393 ≤ 2757967566803^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1591802487 5000000000 2757967566803 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210119139/500000000 : ℝ), (2781546843/5000000000 : ℝ), (1591802487/5000000000 : ℝ)] ![(6366669087521/20000000000000 : ℝ), (46102914008707/100000000000000 : ℝ), (2757967566803/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210119139/500000000 : ℝ)|^8441 ≤ (6366669087521/20000000000000 : ℝ)^6393
        have hw : |(210119139/500000000 : ℝ)|=(210119139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2781546843/5000000000 : ℝ)|^8441 ≤ (46102914008707/100000000000000 : ℝ)^6393
        have hw : |(2781546843/5000000000 : ℝ)|=(2781546843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1591802487/5000000000 : ℝ)|^8441 ≤ (2757967566803/12500000000000 : ℝ)^6393
        have hw : |(1591802487/5000000000 : ℝ)|=(1591802487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1248_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (421/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13707/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1055/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1055 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1055*1^256 ≤ 0^256*1^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1055/256 : ℝ) ≤ (286392691135016833/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1055 ≤ (286392691135016833/12500000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1055*12500000000000000000^256 ≤ 286392691135016833^256*5^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 286392691135016833 12500000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (286392691135016833/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1055 := by
      have hnat : (1 : ℕ)^256*1^1055 ≤ 1^1055*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12786392691135016833/12500000000000000000 : ℝ) ≤ (10055119502579293/10000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (12786392691135016833/12500000000000000000 : ℝ)^256 ≤ (10055119502579293/10000000000000000 : ℝ)^1055 := by
      have hnat : (12786392691135016833 : ℕ)^256*10000000000000000^1055 ≤ 10055119502579293^1055*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12786392691135016833 12500000000000000000 10055119502579293 10000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055119502579293/10000000000000000 : ℝ)) (X := (12786392691135016833/12500000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6536392691135016833/6250000000000000000 : ℝ) ≤ (5055119502579293/5000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (6536392691135016833/6250000000000000000 : ℝ)^256 ≤ (5055119502579293/5000000000000000 : ℝ)^1055 := by
      have hnat : (6536392691135016833 : ℕ)^256*5000000000000000^1055 ≤ 5055119502579293^1055*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6536392691135016833 6250000000000000000 5055119502579293 5000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055119502579293/5000000000000000 : ℝ)) (X := (6536392691135016833/6250000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55119502579293/4000000000000000 : ℝ)*(0 : ℝ))^(1055/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(55119502579293/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(286392691135016833/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55119502579293/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1055/256 : ℝ) := by
    rw [show (1 : ℝ)+(55119502579293/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055119502579293/10000000000000000 : ℝ) by norm_num, show 1+(286392691135016833/12500000000000000000 : ℝ)+(0 : ℝ)=(12786392691135016833/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(286392691135016833/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55119502579293/4000000000000000 : ℝ)*(2/5 : ℝ))^(1055/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(55119502579293/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055119502579293/5000000000000000 : ℝ) by norm_num, show 1+2*(286392691135016833/12500000000000000000 : ℝ)=(6536392691135016833/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55119502579293/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55119502579293/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55119502579293/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55119502579293/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55119502579293/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55119502579293/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-929355077/5000000000 : ℝ)*X 0 0+(1206030793/2000000000 : ℝ)*X 0 1+(4793730289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5510821479/10000000000 : ℝ)*X 1 0+(-2565382337/10000000000 : ℝ)*X 1 1+(4793730231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2755410697/5000000000 : ℝ)*X 2 0+(4793730321/10000000000 : ℝ)*X 2 1+(-1282691167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4192550711/10000000000 : ℝ)*X 0 0+(623333479/2000000000 : ℝ)*X 0 1+(5627746029/10000000000 : ℝ)*X 0 2+(4192550711/10000000000 : ℝ)*X 1 0+(623333479/2000000000 : ℝ)*X 1 1+(5627746029/10000000000 : ℝ)*X 1 2+(4192550711/10000000000 : ℝ)*X 2 0+(623333479/2000000000 : ℝ)*X 2 1+(5627746029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1863550629/10000000000 : ℝ)*X 0 0+(4825566957/10000000000 : ℝ)*X 0 1+(374824489/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587191407/5000000000 : ℝ)*X 1 0+(-680959269/5000000000 : ℝ)*X 1 1+(5997194153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((517438377/1000000000 : ℝ)*X 2 0+(5997192263/10000000000 : ℝ)*X 2 1+(-85120007/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((210119139/500000000 : ℝ)*X 0 0+(2781546843/5000000000 : ℝ)*X 0 1+(1591802487/5000000000 : ℝ)*X 0 2+(210119139/500000000 : ℝ)*X 1 0+(2781546843/5000000000 : ℝ)*X 1 1+(1591802487/5000000000 : ℝ)*X 1 2+(210119139/500000000 : ℝ)*X 2 0+(2781546843/5000000000 : ℝ)*X 2 1+(1591802487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53709812167943858286309/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55679523/100000000000000 : ℝ)*(base1) + (525362221/50000000000000 : ℝ)*(base19) + (969376711/100000000000000 : ℝ)*(base23) + (8609101/12500000000000 : ℝ)*(base24) + (46639651/20000000000000 : ℝ)*(upper3) + (150878552271171/25000000000000 : ℝ)*(major0) + (150878552271171/25000000000000 : ℝ)*(major1) + (150878552271171/25000000000000 : ℝ)*(major2) + (808787813058863/100000000000000 : ℝ)*(sp0) + (161757810735247/20000000000000 : ℝ)*(sp1) + (404394533075579/50000000000000 : ℝ)*(sp2) + (398236308292473/100000000000000 : ℝ)*(sp3) + (1173510669/50000000000000 : ℝ)*(sp4) + (1806570521/100000000000000 : ℝ)*(sp7) + (99559542635629/25000000000000 : ℝ)*(f.failure) + (808790104400677/100000000000000 : ℝ)*(f.sum) + (97042843487897/50000000000000000000000000000 : ℝ)*base66 + (689984184737897/100000000000000000000000000000 : ℝ)*base68 + (350727643537897/100000000000000000000000000000 : ℝ)*base70 + (289140159337897/100000000000000000000000000000 : ℝ)*base72 + (157651686837897/50000000000000000000000000000 : ℝ)*base74 + (260289480137897/100000000000000000000000000000 : ℝ)*base76 + (588582428037897/100000000000000000000000000000 : ℝ)*base78 + (24913330437897/100000000000000000000000000000 : ℝ)*base80 + (147314245512103/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (328997/39062500000000000000 : ℝ)*base90 + (328997/39062500000000000000 : ℝ)*base92 + (328997/39062500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (728636917423423340778357/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186046633/100000000000000 : ℝ)*(base1) + (862875187/50000000000000 : ℝ)*(base19) + (93773529/5000000000000 : ℝ)*(base23) + (178317221/50000000000000 : ℝ)*(upper3) + (23460539/50000000000000 : ℝ)*(upper5) + (318443271766317/50000000000000 : ℝ)*(major0) + (318443271766317/50000000000000 : ℝ)*(major1) + (318443271766317/50000000000000 : ℝ)*(major2) + (3501205649/100000000000000 : ℝ)*(sp1) + (3378616109/100000000000000 : ℝ)*(sp2) + (426756804728819/50000000000000 : ℝ)*(sp4) + (853508196454983/100000000000000 : ℝ)*(sp5) + (853508169324317/100000000000000 : ℝ)*(sp6) + (420259234728651/100000000000000 : ℝ)*(sp7) + (105064855193821/25000000000000 : ℝ)*(f.failure) + (426756711705503/50000000000000 : ℝ)*(f.sum) + (82517911273881/100000000000000000000000000000 : ℝ)*base65 + (1426552428673881/200000000000000000000000000000 : ℝ)*base67 + (98726898126119/200000000000000000000000000000 : ℝ)*base70 + (708399903526119/200000000000000000000000000000 : ℝ)*base72 + (719445357173881/100000000000000000000000000000 : ℝ)*base73 + (1748054419326119/200000000000000000000000000000 : ℝ)*base76 + (843634704126119/200000000000000000000000000000 : ℝ)*base78 + (965134130126119/200000000000000000000000000000 : ℝ)*base80 + (142192642673881/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (53603/39062500000000000000 : ℝ)*base90 + (53603/39062500000000000000 : ℝ)*base92 + (53603/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1248_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (421/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13707/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1248_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1248_s1_0 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-32120023/156250000 : ℝ)*x 0 + (5674108757/10000000000 : ℝ)*x 1 + (1004738319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32120023/156250000 : ℝ)^8441 ≤ (12384000352977/100000000000000 : ℝ)^6393 := by
    have hnat : (32120023 : ℕ)^8441*100000000000000^6393 ≤ 12384000352977^6393*156250000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32120023 156250000 12384000352977 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5674108757/10000000000 : ℝ)^8441 ≤ (2957594928199/6250000000000 : ℝ)^6393 := by
    have hnat : (5674108757 : ℕ)^8441*6250000000000^6393 ≤ 2957594928199^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674108757 10000000000 2957594928199 6250000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004738319/2000000000 : ℝ)^8441 ≤ (2518405049267/6250000000000 : ℝ)^6393 := by
    have hnat : (1004738319 : ℕ)^8441*6250000000000^6393 ≤ 2518405049267^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004738319 2000000000 2518405049267 6250000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32120023/156250000 : ℝ), (5674108757/10000000000 : ℝ), (1004738319/2000000000 : ℝ)] ![(12384000352977/100000000000000 : ℝ), (2957594928199/6250000000000 : ℝ), (2518405049267/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32120023/156250000 : ℝ)|^8441 ≤ (12384000352977/100000000000000 : ℝ)^6393
        have hw : |(-32120023/156250000 : ℝ)|=(32120023/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5674108757/10000000000 : ℝ)|^8441 ≤ (2957594928199/6250000000000 : ℝ)^6393
        have hw : |(5674108757/10000000000 : ℝ)|=(5674108757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004738319/2000000000 : ℝ)|^8441 ≤ (2518405049267/6250000000000 : ℝ)^6393
        have hw : |(1004738319/2000000000 : ℝ)|=(1004738319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s1_1 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5413334349/10000000000 : ℝ)*x 0 + (-2404848697/10000000000 : ℝ)*x 1 + (5023691857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413334349/10000000000 : ℝ)^8441 ≤ (1778853596113/4000000000000 : ℝ)^6393 := by
    have hnat : (5413334349 : ℕ)^8441*4000000000000^6393 ≤ 1778853596113^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413334349 10000000000 1778853596113 4000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2404848697/10000000000 : ℝ)^8441 ≤ (15234176521159/100000000000000 : ℝ)^6393 := by
    have hnat : (2404848697 : ℕ)^8441*100000000000000^6393 ≤ 15234176521159^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404848697 10000000000 15234176521159 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5023691857/10000000000 : ℝ)^8441 ≤ (40294483562953/100000000000000 : ℝ)^6393 := by
    have hnat : (5023691857 : ℕ)^8441*100000000000000^6393 ≤ 40294483562953^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023691857 10000000000 40294483562953 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413334349/10000000000 : ℝ), (-2404848697/10000000000 : ℝ), (5023691857/10000000000 : ℝ)] ![(1778853596113/4000000000000 : ℝ), (15234176521159/100000000000000 : ℝ), (40294483562953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413334349/10000000000 : ℝ)|^8441 ≤ (1778853596113/4000000000000 : ℝ)^6393
        have hw : |(5413334349/10000000000 : ℝ)|=(5413334349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2404848697/10000000000 : ℝ)|^8441 ≤ (15234176521159/100000000000000 : ℝ)^6393
        have hw : |(-2404848697/10000000000 : ℝ)|=(2404848697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5023691857/10000000000 : ℝ)|^8441 ≤ (40294483562953/100000000000000 : ℝ)^6393
        have hw : |(5023691857/10000000000 : ℝ)|=(5023691857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s1_2 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (84583353/156250000 : ℝ)*x 0 + (2511845841/5000000000 : ℝ)*x 1 + (-2404848603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84583353/156250000 : ℝ)^8441 ≤ (8894268507723/20000000000000 : ℝ)^6393 := by
    have hnat : (84583353 : ℕ)^8441*20000000000000^6393 ≤ 8894268507723^6393*156250000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84583353 156250000 8894268507723 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2511845841/5000000000 : ℝ)^8441 ≤ (10073620427409/25000000000000 : ℝ)^6393 := by
    have hnat : (2511845841 : ℕ)^8441*25000000000000^6393 ≤ 10073620427409^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511845841 5000000000 10073620427409 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2404848603/10000000000 : ℝ)^8441 ≤ (15234175734931/100000000000000 : ℝ)^6393 := by
    have hnat : (2404848603 : ℕ)^8441*100000000000000^6393 ≤ 15234175734931^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404848603 10000000000 15234175734931 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84583353/156250000 : ℝ), (2511845841/5000000000 : ℝ), (-2404848603/10000000000 : ℝ)] ![(8894268507723/20000000000000 : ℝ), (10073620427409/25000000000000 : ℝ), (15234175734931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84583353/156250000 : ℝ)|^8441 ≤ (8894268507723/20000000000000 : ℝ)^6393
        have hw : |(84583353/156250000 : ℝ)|=(84583353/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2511845841/5000000000 : ℝ)|^8441 ≤ (10073620427409/25000000000000 : ℝ)^6393
        have hw : |(2511845841/5000000000 : ℝ)|=(2511845841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2404848603/10000000000 : ℝ)|^8441 ≤ (15234175734931/100000000000000 : ℝ)^6393
        have hw : |(-2404848603/10000000000 : ℝ)|=(2404848603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s1_3 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4308332901/10000000000 : ℝ)*x 0 + (3696517769/10000000000 : ℝ)*x 1 + (2508732099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308332901/10000000000 : ℝ)^8441 ≤ (4112160865437/12500000000000 : ℝ)^6393 := by
    have hnat : (4308332901 : ℕ)^8441*12500000000000^6393 ≤ 4112160865437^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308332901 10000000000 4112160865437 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3696517769/10000000000 : ℝ)^8441 ≤ (1679635606999/6250000000000 : ℝ)^6393 := by
    have hnat : (3696517769 : ℕ)^8441*6250000000000^6393 ≤ 1679635606999^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3696517769 10000000000 1679635606999 6250000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508732099/5000000000 : ℝ)^8441 ≤ (40228543348677/100000000000000 : ℝ)^6393 := by
    have hnat : (2508732099 : ℕ)^8441*100000000000000^6393 ≤ 40228543348677^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508732099 5000000000 40228543348677 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308332901/10000000000 : ℝ), (3696517769/10000000000 : ℝ), (2508732099/5000000000 : ℝ)] ![(4112160865437/12500000000000 : ℝ), (1679635606999/6250000000000 : ℝ), (40228543348677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308332901/10000000000 : ℝ)|^8441 ≤ (4112160865437/12500000000000 : ℝ)^6393
        have hw : |(4308332901/10000000000 : ℝ)|=(4308332901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3696517769/10000000000 : ℝ)|^8441 ≤ (1679635606999/6250000000000 : ℝ)^6393
        have hw : |(3696517769/10000000000 : ℝ)|=(3696517769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2508732099/5000000000 : ℝ)|^8441 ≤ (40228543348677/100000000000000 : ℝ)^6393
        have hw : |(2508732099/5000000000 : ℝ)|=(2508732099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s1_4 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-257043821/1250000000 : ℝ)*x 0 + (5032215479/10000000000 : ℝ)*x 1 + (5665423223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257043821/1250000000 : ℝ)^8441 ≤ (774332670447/6250000000000 : ℝ)^6393 := by
    have hnat : (257043821 : ℕ)^8441*6250000000000^6393 ≤ 774332670447^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257043821 1250000000 774332670447 6250000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5032215479/10000000000 : ℝ)^8441 ≤ (40384776534131/100000000000000 : ℝ)^6393 := by
    have hnat : (5032215479 : ℕ)^8441*100000000000000^6393 ≤ 40384776534131^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032215479 10000000000 40384776534131 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5665423223/10000000000 : ℝ)^8441 ≤ (47225900729613/100000000000000 : ℝ)^6393 := by
    have hnat : (5665423223 : ℕ)^8441*100000000000000^6393 ≤ 47225900729613^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665423223 10000000000 47225900729613 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257043821/1250000000 : ℝ), (5032215479/10000000000 : ℝ), (5665423223/10000000000 : ℝ)] ![(774332670447/6250000000000 : ℝ), (40384776534131/100000000000000 : ℝ), (47225900729613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257043821/1250000000 : ℝ)|^8441 ≤ (774332670447/6250000000000 : ℝ)^6393
        have hw : |(-257043821/1250000000 : ℝ)|=(257043821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5032215479/10000000000 : ℝ)|^8441 ≤ (40384776534131/100000000000000 : ℝ)^6393
        have hw : |(5032215479/10000000000 : ℝ)|=(5032215479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5665423223/10000000000 : ℝ)|^8441 ≤ (47225900729613/100000000000000 : ℝ)^6393
        have hw : |(5665423223/10000000000 : ℝ)|=(5665423223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s1_5 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1049144021/2000000000 : ℝ)*x 0 + (-220389631/1250000000 : ℝ)*x 1 + (2832711729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049144021/2000000000 : ℝ)^8441 ≤ (21331165223881/50000000000000 : ℝ)^6393 := by
    have hnat : (1049144021 : ℕ)^8441*50000000000000^6393 ≤ 21331165223881^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049144021 2000000000 21331165223881 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220389631/1250000000 : ℝ)^8441 ≤ (10111766226623/100000000000000 : ℝ)^6393 := by
    have hnat : (220389631 : ℕ)^8441*100000000000000^6393 ≤ 10111766226623^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220389631 1250000000 10111766226623 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2832711729/5000000000 : ℝ)^8441 ≤ (11806475829017/25000000000000 : ℝ)^6393 := by
    have hnat : (2832711729 : ℕ)^8441*25000000000000^6393 ≤ 11806475829017^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832711729 5000000000 11806475829017 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049144021/2000000000 : ℝ), (-220389631/1250000000 : ℝ), (2832711729/5000000000 : ℝ)] ![(21331165223881/50000000000000 : ℝ), (10111766226623/100000000000000 : ℝ), (11806475829017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049144021/2000000000 : ℝ)|^8441 ≤ (21331165223881/50000000000000 : ℝ)^6393
        have hw : |(1049144021/2000000000 : ℝ)|=(1049144021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220389631/1250000000 : ℝ)|^8441 ≤ (10111766226623/100000000000000 : ℝ)^6393
        have hw : |(-220389631/1250000000 : ℝ)|=(220389631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2832711729/5000000000 : ℝ)|^8441 ≤ (11806475829017/25000000000000 : ℝ)^6393
        have hw : |(2832711729/5000000000 : ℝ)|=(2832711729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s1_6 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2622860017/5000000000 : ℝ)*x 0 + (708177909/1250000000 : ℝ)*x 1 + (-1763117419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622860017/5000000000 : ℝ)^8441 ≤ (8532465937071/20000000000000 : ℝ)^6393 := by
    have hnat : (2622860017 : ℕ)^8441*20000000000000^6393 ≤ 8532465937071^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622860017 5000000000 8532465937071 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708177909/1250000000 : ℝ)^8441 ≤ (11806475317229/25000000000000 : ℝ)^6393 := by
    have hnat : (708177909 : ℕ)^8441*25000000000000^6393 ≤ 11806475317229^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708177909 1250000000 11806475317229 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1763117419/10000000000 : ℝ)^8441 ≤ (10111769035993/100000000000000 : ℝ)^6393 := by
    have hnat : (1763117419 : ℕ)^8441*100000000000000^6393 ≤ 10111769035993^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763117419 10000000000 10111769035993 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622860017/5000000000 : ℝ), (708177909/1250000000 : ℝ), (-1763117419/10000000000 : ℝ)] ![(8532465937071/20000000000000 : ℝ), (11806475317229/25000000000000 : ℝ), (10111769035993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622860017/5000000000 : ℝ)|^8441 ≤ (8532465937071/20000000000000 : ℝ)^6393
        have hw : |(2622860017/5000000000 : ℝ)|=(2622860017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708177909/1250000000 : ℝ)|^8441 ≤ (11806475317229/25000000000000 : ℝ)^6393
        have hw : |(708177909/1250000000 : ℝ)|=(708177909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1763117419/10000000000 : ℝ)|^8441 ≤ (10111769035993/100000000000000 : ℝ)^6393
        have hw : |(-1763117419/10000000000 : ℝ)|=(1763117419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s1_7 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (538711463/1250000000 : ℝ)*x 0 + (1000030599/2000000000 : ℝ)*x 1 + (3714157813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538711463/1250000000 : ℝ)^8441 ≤ (2056936678563/6250000000000 : ℝ)^6393 := by
    have hnat : (538711463 : ℕ)^8441*6250000000000^6393 ≤ 2056936678563^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538711463 1250000000 2056936678563 6250000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000030599/2000000000 : ℝ)^8441 ≤ (40045385215029/100000000000000 : ℝ)^6393 := by
    have hnat : (1000030599 : ℕ)^8441*100000000000000^6393 ≤ 40045385215029^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000030599 2000000000 40045385215029 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3714157813/10000000000 : ℝ)^8441 ≤ (3380453489193/12500000000000 : ℝ)^6393 := by
    have hnat : (3714157813 : ℕ)^8441*12500000000000^6393 ≤ 3380453489193^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714157813 10000000000 3380453489193 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538711463/1250000000 : ℝ), (1000030599/2000000000 : ℝ), (3714157813/10000000000 : ℝ)] ![(2056936678563/6250000000000 : ℝ), (40045385215029/100000000000000 : ℝ), (3380453489193/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538711463/1250000000 : ℝ)|^8441 ≤ (2056936678563/6250000000000 : ℝ)^6393
        have hw : |(538711463/1250000000 : ℝ)|=(538711463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000030599/2000000000 : ℝ)|^8441 ≤ (40045385215029/100000000000000 : ℝ)^6393
        have hw : |(1000030599/2000000000 : ℝ)|=(1000030599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3714157813/10000000000 : ℝ)|^8441 ≤ (3380453489193/12500000000000 : ℝ)^6393
        have hw : |(3714157813/10000000000 : ℝ)|=(3714157813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1248_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13707/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (421/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3111/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9987/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13707/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (421/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13707/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (421/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13707/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (421/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13707/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (421/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13707/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (421/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13707/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (421/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (421/50000 : ℝ) ^ (1055/256 : ℝ) ≤ (281849083587/100000000000000000000 : ℝ) := by
    have hpowers : (421/50000 : ℝ)^1055 ≤ (281849083587/100000000000000000000 : ℝ)^256 := by
      have hnat : (421 : ℕ)^1055*100000000000000000000^256 ≤ 281849083587^256*50000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        421 50000 281849083587 100000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (421/50000 : ℝ)) (X := (281849083587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13707/50000 : ℝ) ^ (1055/256 : ℝ) ≤ (241435767693196123/50000000000000000000 : ℝ) := by
    have hpowers : (13707/50000 : ℝ)^1055 ≤ (241435767693196123/50000000000000000000 : ℝ)^256 := by
      have hnat : (13707 : ℕ)^1055*50000000000000000000^256 ≤ 241435767693196123^256*50000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13707 50000 241435767693196123 50000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13707/50000 : ℝ)) (X := (241435767693196123/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000281849083587/50000000000000000000 : ℝ) ≤ (2500000003419591/2500000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50000000281849083587/50000000000000000000 : ℝ)^256 ≤ (2500000003419591/2500000000000000 : ℝ)^1055 := by
      have hnat : (50000000281849083587 : ℕ)^256*2500000000000000^1055 ≤ 2500000003419591^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000281849083587 50000000000000000000 2500000003419591 2500000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000003419591/2500000000000000 : ℝ)) (X := (50000000281849083587/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100482871817235475833/100000000000000000000 : ℝ) ≤ (5005847857414109/5000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (100482871817235475833/100000000000000000000 : ℝ)^256 ≤ (5005847857414109/5000000000000000 : ℝ)^1055 := by
      have hnat : (100482871817235475833 : ℕ)^256*5000000000000000^1055 ≤ 5005847857414109^1055*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100482871817235475833 100000000000000000000 5005847857414109 5000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005847857414109/5000000000000000 : ℝ)) (X := (100482871817235475833/100000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25241435767693196123/25000000000000000000 : ℝ) ≤ (1252923926997259/1250000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (25241435767693196123/25000000000000000000 : ℝ)^256 ≤ (1252923926997259/1250000000000000 : ℝ)^1055 := by
      have hnat : (25241435767693196123 : ℕ)^256*1250000000000000^1055 ≤ 1252923926997259^1055*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25241435767693196123 25000000000000000000 1252923926997259 1250000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252923926997259/1250000000000000 : ℝ)) (X := (25241435767693196123/25000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(281849083587/100000000000000000000 : ℝ) ≤ ((33212538100340641759/33215000000000000000 : ℝ)+2*(5847850574927/1328600000000000 : ℝ)*(421/50000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (33212538100340641759/33215000000000000000 : ℝ)+2*(5847850574927/1328600000000000 : ℝ)*(421/50000 : ℝ)=(2500000003419591/2500000000000000 : ℝ) by norm_num, show 1+2*(281849083587/100000000000000000000 : ℝ)=(50000000281849083587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(241435767693196123/50000000000000000000 : ℝ)+(281849083587/100000000000000000000 : ℝ) ≤ ((33212538100340641759/33215000000000000000 : ℝ)+(5847850574927/1328600000000000 : ℝ)*((13707/50000 : ℝ)+(421/50000 : ℝ)))^(1055/256 : ℝ) := by
    rw [show (33212538100340641759/33215000000000000000 : ℝ)+(5847850574927/1328600000000000 : ℝ)*((13707/50000 : ℝ)+(421/50000 : ℝ))=(5005847857414109/5000000000000000 : ℝ) by norm_num, show 1+(241435767693196123/50000000000000000000 : ℝ)+(281849083587/100000000000000000000 : ℝ)=(100482871817235475833/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(241435767693196123/50000000000000000000 : ℝ) ≤ ((33212538100340641759/33215000000000000000 : ℝ)+2*(5847850574927/1328600000000000 : ℝ)*(13707/50000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (33212538100340641759/33215000000000000000 : ℝ)+2*(5847850574927/1328600000000000 : ℝ)*(13707/50000 : ℝ)=(1252923926997259/1250000000000000 : ℝ) by norm_num, show 1+2*(241435767693196123/50000000000000000000 : ℝ)=(25241435767693196123/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33212538100340641759/33215000000000000000 : ℝ)*(X 1 0+X 2 0)+(5847850574927/1328600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (421/50000 : ℝ)) (hi := (13707/50000 : ℝ)) (c := (33212538100340641759/33215000000000000000 : ℝ)) (alpha := (5847850574927/1328600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33212538100340641759/33215000000000000000 : ℝ)*(X 0 1+X 2 1)+(5847850574927/1328600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (421/50000 : ℝ)) (hi := (13707/50000 : ℝ)) (c := (33212538100340641759/33215000000000000000 : ℝ)) (alpha := (5847850574927/1328600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33212538100340641759/33215000000000000000 : ℝ)*(X 0 2+X 1 2)+(5847850574927/1328600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (421/50000 : ℝ)) (hi := (13707/50000 : ℝ)) (c := (33212538100340641759/33215000000000000000 : ℝ)) (alpha := (5847850574927/1328600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-32120023/156250000 : ℝ)*X 0 0+(5674108757/10000000000 : ℝ)*X 0 1+(1004738319/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5413334349/10000000000 : ℝ)*X 1 0+(-2404848697/10000000000 : ℝ)*X 1 1+(5023691857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((84583353/156250000 : ℝ)*X 2 0+(2511845841/5000000000 : ℝ)*X 2 1+(-2404848603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308332901/10000000000 : ℝ)*X 0 0+(3696517769/10000000000 : ℝ)*X 0 1+(2508732099/5000000000 : ℝ)*X 0 2+(4308332901/10000000000 : ℝ)*X 1 0+(3696517769/10000000000 : ℝ)*X 1 1+(2508732099/5000000000 : ℝ)*X 1 2+(4308332901/10000000000 : ℝ)*X 2 0+(3696517769/10000000000 : ℝ)*X 2 1+(2508732099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-257043821/1250000000 : ℝ)*X 0 0+(5032215479/10000000000 : ℝ)*X 0 1+(5665423223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049144021/2000000000 : ℝ)*X 1 0+(-220389631/1250000000 : ℝ)*X 1 1+(2832711729/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2622860017/5000000000 : ℝ)*X 2 0+(708177909/1250000000 : ℝ)*X 2 1+(-1763117419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538711463/1250000000 : ℝ)*X 0 0+(1000030599/2000000000 : ℝ)*X 0 1+(3714157813/10000000000 : ℝ)*X 0 2+(538711463/1250000000 : ℝ)*X 1 0+(1000030599/2000000000 : ℝ)*X 1 1+(3714157813/10000000000 : ℝ)*X 1 2+(538711463/1250000000 : ℝ)*X 2 0+(1000030599/2000000000 : ℝ)*X 2 1+(3714157813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6267844608337903162020507657/830375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18028779/25000000000000 : ℝ)*(base1) + (1673359023/100000000000000 : ℝ)*(base19) + (348475153/20000000000000 : ℝ)*(base23) + (177171589/100000000000000 : ℝ)*(upper3) + (230196483/100000000000000 : ℝ)*(upper5) + (1147268802774441/100000000000000 : ℝ)*(major0) + (1147268802774441/100000000000000 : ℝ)*(major1) + (1147268802774441/100000000000000 : ℝ)*(major2) + (1537484111620357/100000000000000 : ℝ)*(sp0) + (1537492644545107/100000000000000 : ℝ)*(sp1) + (307498515105673/20000000000000 : ℝ)*(sp2) + (757037984891537/100000000000000 : ℝ)*(sp3) + (10278398889/100000000000000 : ℝ)*(sp4) + (4979031107/100000000000000 : ℝ)*(sp7) + (1182879743809/156250000000 : ℝ)*(f.failure) + (153749431790413/10000000000000 : ℝ)*(f.sum) + (29067118558063/66430000000000000000000000000 : ℝ)*base66 + (9077023275924343281/3321500000000000000000000000000000 : ℝ)*base68 + (13478590314565843281/3321500000000000000000000000000000 : ℝ)*base70 + (13259356464139343281/3321500000000000000000000000000000 : ℝ)*base72 + (224039841493963/66430000000000000000000000000 : ℝ)*base74 + (10872192779961343281/3321500000000000000000000000000000 : ℝ)*base76 + (927694286415156719/3321500000000000000000000000000000 : ℝ)*base77 + (16816752184199343281/3321500000000000000000000000000000 : ℝ)*base80 + (309860518216653/66430000000000000000000000000 : ℝ)*base82 + (5291/7812500000000000000 : ℝ)*base89 + (5291/7812500000000000000 : ℝ)*base91 + (5291/7812500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (163031396749977378797007921/15968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45501513/50000000000000 : ℝ)*(base1) + (2047489649/100000000000000 : ℝ)*(base19) + (3201743/160000000000 : ℝ)*(base23) + (62251479/25000000000000 : ℝ)*(upper3) + (113664307/50000000000000 : ℝ)*(upper5) + (147304278126583/12500000000000 : ℝ)*(major0) + (147304278126583/12500000000000 : ℝ)*(major1) + (147304278126583/12500000000000 : ℝ)*(major2) + (1944893127/20000000000000 : ℝ)*(sp1) + (8941248601/100000000000000 : ℝ)*(sp2) + (789630089772951/50000000000000 : ℝ)*(sp4) + (1579248316587593/100000000000000 : ℝ)*(sp5) + (1579249146204901/100000000000000 : ℝ)*(sp6) + (388803965083001/50000000000000 : ℝ)*(sp7) + (777608021169027/100000000000000 : ℝ)*(f.failure) + (1579260088542877/100000000000000 : ℝ)*(f.sum) + (20615770394679/8303750000000000000000000000 : ℝ)*base66 + (5993593297695503/415187500000000000000000000000000 : ℝ)*base68 + (97526960518445503/415187500000000000000000000000000 : ℝ)*base70 + (1878907826942695503/415187500000000000000000000000000 : ℝ)*base72 + (70645185684599/33215000000000000000000000000 : ℝ)*base73 + (4803473267734008003/415187500000000000000000000000000 : ℝ)*base76 + (2917017137010070503/415187500000000000000000000000000 : ℝ)*base78 + (1213473391868195503/415187500000000000000000000000000 : ℝ)*base80 + (10722801058601/8303750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (283511/156250000000000000000 : ℝ)*base90 + (283511/156250000000000000000 : ℝ)*base92 + (283511/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1248_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13707/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (421/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3111/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9987/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1248_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1248_s2_0 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-420685167/2000000000 : ℝ)*x 0 + (5491784159/10000000000 : ℝ)*x 1 + (1293890539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420685167/2000000000 : ℝ)^8441 ≤ (12765172090769/100000000000000 : ℝ)^6393 := by
    have hnat : (420685167 : ℕ)^8441*100000000000000^6393 ≤ 12765172090769^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420685167 2000000000 12765172090769 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491784159/10000000000 : ℝ)^8441 ≤ (4532424382499/10000000000000 : ℝ)^6393 := by
    have hnat : (5491784159 : ℕ)^8441*10000000000000^6393 ≤ 4532424382499^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491784159 10000000000 4532424382499 10000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293890539/2500000000 : ℝ)^8441 ≤ (1047764601861/2500000000000 : ℝ)^6393 := by
    have hnat : (1293890539 : ℕ)^8441*2500000000000^6393 ≤ 1047764601861^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293890539 2500000000 1047764601861 2500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420685167/2000000000 : ℝ), (5491784159/10000000000 : ℝ), (1293890539/2500000000 : ℝ)] ![(12765172090769/100000000000000 : ℝ), (4532424382499/10000000000000 : ℝ), (1047764601861/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420685167/2000000000 : ℝ)|^8441 ≤ (12765172090769/100000000000000 : ℝ)^6393
        have hw : |(-420685167/2000000000 : ℝ)|=(420685167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491784159/10000000000 : ℝ)|^8441 ≤ (4532424382499/10000000000000 : ℝ)^6393
        have hw : |(5491784159/10000000000 : ℝ)|=(5491784159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293890539/2500000000 : ℝ)|^8441 ≤ (1047764601861/2500000000000 : ℝ)^6393
        have hw : |(1293890539/2500000000 : ℝ)|=(1293890539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s2_1 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369446359/10000000000 : ℝ)*x 0 + (-1133596467/5000000000 : ℝ)*x 1 + (5175562217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369446359/10000000000 : ℝ)^8441 ≤ (70393458849/160000000000 : ℝ)^6393 := by
    have hnat : (5369446359 : ℕ)^8441*160000000000^6393 ≤ 70393458849^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369446359 10000000000 70393458849 160000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133596467/5000000000 : ℝ)^8441 ≤ (7046751734881/50000000000000 : ℝ)^6393 := by
    have hnat : (1133596467 : ℕ)^8441*50000000000000^6393 ≤ 7046751734881^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133596467 5000000000 7046751734881 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175562217/10000000000 : ℝ)^8441 ≤ (41910584726647/100000000000000 : ℝ)^6393 := by
    have hnat : (5175562217 : ℕ)^8441*100000000000000^6393 ≤ 41910584726647^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175562217 10000000000 41910584726647 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369446359/10000000000 : ℝ), (-1133596467/5000000000 : ℝ), (5175562217/10000000000 : ℝ)] ![(70393458849/160000000000 : ℝ), (7046751734881/50000000000000 : ℝ), (41910584726647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369446359/10000000000 : ℝ)|^8441 ≤ (70393458849/160000000000 : ℝ)^6393
        have hw : |(5369446359/10000000000 : ℝ)|=(5369446359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133596467/5000000000 : ℝ)|^8441 ≤ (7046751734881/50000000000000 : ℝ)^6393
        have hw : |(-1133596467/5000000000 : ℝ)|=(1133596467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175562217/10000000000 : ℝ)|^8441 ≤ (41910584726647/100000000000000 : ℝ)^6393
        have hw : |(5175562217/10000000000 : ℝ)|=(5175562217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s2_2 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369446233/10000000000 : ℝ)*x 0 + (2587781153/5000000000 : ℝ)*x 1 + (-453438597/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369446233/10000000000 : ℝ)^8441 ≤ (43995910417479/100000000000000 : ℝ)^6393 := by
    have hnat : (5369446233 : ℕ)^8441*100000000000000^6393 ≤ 43995910417479^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369446233 10000000000 43995910417479 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587781153/5000000000 : ℝ)^8441 ≤ (41910585678227/100000000000000 : ℝ)^6393 := by
    have hnat : (2587781153 : ℕ)^8441*100000000000000^6393 ≤ 41910585678227^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587781153 5000000000 41910585678227 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453438597/2000000000 : ℝ)^8441 ≤ (14093503888353/100000000000000 : ℝ)^6393 := by
    have hnat : (453438597 : ℕ)^8441*100000000000000^6393 ≤ 14093503888353^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453438597 2000000000 14093503888353 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369446233/10000000000 : ℝ), (2587781153/5000000000 : ℝ), (-453438597/2000000000 : ℝ)] ![(43995910417479/100000000000000 : ℝ), (41910585678227/100000000000000 : ℝ), (14093503888353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369446233/10000000000 : ℝ)|^8441 ≤ (43995910417479/100000000000000 : ℝ)^6393
        have hw : |(5369446233/10000000000 : ℝ)|=(5369446233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587781153/5000000000 : ℝ)|^8441 ≤ (41910585678227/100000000000000 : ℝ)^6393
        have hw : |(2587781153/5000000000 : ℝ)|=(2587781153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-453438597/2000000000 : ℝ)|^8441 ≤ (14093503888353/100000000000000 : ℝ)^6393
        have hw : |(-453438597/2000000000 : ℝ)|=(453438597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s2_3 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4341323853/10000000000 : ℝ)*x 0 + (2015850087/5000000000 : ℝ)*x 1 + (934784373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341323853/10000000000 : ℝ)^8441 ≤ (16615151923747/50000000000000 : ℝ)^6393 := by
    have hnat : (4341323853 : ℕ)^8441*50000000000000^6393 ≤ 16615151923747^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341323853 10000000000 16615151923747 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015850087/5000000000 : ℝ)^8441 ≤ (1506871552759/5000000000000 : ℝ)^6393 := by
    have hnat : (2015850087 : ℕ)^8441*5000000000000^6393 ≤ 1506871552759^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015850087 5000000000 1506871552759 5000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934784373/2000000000 : ℝ)^8441 ≤ (18316132539119/50000000000000 : ℝ)^6393 := by
    have hnat : (934784373 : ℕ)^8441*50000000000000^6393 ≤ 18316132539119^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934784373 2000000000 18316132539119 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341323853/10000000000 : ℝ), (2015850087/5000000000 : ℝ), (934784373/2000000000 : ℝ)] ![(16615151923747/50000000000000 : ℝ), (1506871552759/5000000000000 : ℝ), (18316132539119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341323853/10000000000 : ℝ)|^8441 ≤ (16615151923747/50000000000000 : ℝ)^6393
        have hw : |(4341323853/10000000000 : ℝ)|=(4341323853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015850087/5000000000 : ℝ)|^8441 ≤ (1506871552759/5000000000000 : ℝ)^6393
        have hw : |(2015850087/5000000000 : ℝ)|=(2015850087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(934784373/2000000000 : ℝ)|^8441 ≤ (18316132539119/50000000000000 : ℝ)^6393
        have hw : |(934784373/2000000000 : ℝ)|=(934784373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s2_4 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-420700607/2000000000 : ℝ)*x 0 + (2588793379/5000000000 : ℝ)*x 1 + (1372435161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420700607/2000000000 : ℝ)^8441 ≤ (12765790688781/100000000000000 : ℝ)^6393 := by
    have hnat : (420700607 : ℕ)^8441*100000000000000^6393 ≤ 12765790688781^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420700607 2000000000 12765790688781 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588793379/5000000000 : ℝ)^8441 ≤ (20966116148667/50000000000000 : ℝ)^6393 := by
    have hnat : (2588793379 : ℕ)^8441*50000000000000^6393 ≤ 20966116148667^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588793379 5000000000 20966116148667 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372435161/2500000000 : ℝ)^8441 ≤ (45301977002589/100000000000000 : ℝ)^6393 := by
    have hnat : (1372435161 : ℕ)^8441*100000000000000^6393 ≤ 45301977002589^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372435161 2500000000 45301977002589 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420700607/2000000000 : ℝ), (2588793379/5000000000 : ℝ), (1372435161/2500000000 : ℝ)] ![(12765790688781/100000000000000 : ℝ), (20966116148667/50000000000000 : ℝ), (45301977002589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420700607/2000000000 : ℝ)|^8441 ≤ (12765790688781/100000000000000 : ℝ)^6393
        have hw : |(-420700607/2000000000 : ℝ)|=(420700607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588793379/5000000000 : ℝ)|^8441 ≤ (20966116148667/50000000000000 : ℝ)^6393
        have hw : |(2588793379/5000000000 : ℝ)|=(2588793379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372435161/2500000000 : ℝ)|^8441 ≤ (45301977002589/100000000000000 : ℝ)^6393
        have hw : |(1372435161/2500000000 : ℝ)|=(1372435161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s2_5 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644330797/5000000000 : ℝ)*x 0 + (-195301427/1000000000 : ℝ)*x 1 + (5489740689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644330797/5000000000 : ℝ)^8441 ≤ (43124045227749/100000000000000 : ℝ)^6393 := by
    have hnat : (2644330797 : ℕ)^8441*100000000000000^6393 ≤ 43124045227749^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644330797 5000000000 43124045227749 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195301427/1000000000 : ℝ)^8441 ≤ (5786988632079/50000000000000 : ℝ)^6393 := by
    have hnat : (195301427 : ℕ)^8441*50000000000000^6393 ≤ 5786988632079^6393*1000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195301427 1000000000 5786988632079 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489740689/10000000000 : ℝ)^8441 ≤ (9060395498579/20000000000000 : ℝ)^6393 := by
    have hnat : (5489740689 : ℕ)^8441*20000000000000^6393 ≤ 9060395498579^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489740689 10000000000 9060395498579 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644330797/5000000000 : ℝ), (-195301427/1000000000 : ℝ), (5489740689/10000000000 : ℝ)] ![(43124045227749/100000000000000 : ℝ), (5786988632079/50000000000000 : ℝ), (9060395498579/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644330797/5000000000 : ℝ)|^8441 ≤ (43124045227749/100000000000000 : ℝ)^6393
        have hw : |(2644330797/5000000000 : ℝ)|=(2644330797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-195301427/1000000000 : ℝ)|^8441 ≤ (5786988632079/50000000000000 : ℝ)^6393
        have hw : |(-195301427/1000000000 : ℝ)|=(195301427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489740689/10000000000 : ℝ)|^8441 ≤ (9060395498579/20000000000000 : ℝ)^6393
        have hw : |(5489740689/10000000000 : ℝ)|=(5489740689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s2_6 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (21154647/40000000 : ℝ)*x 0 + (274487039/500000000 : ℝ)*x 1 + (-1953013929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21154647/40000000 : ℝ)^8441 ≤ (21562023453639/50000000000000 : ℝ)^6393 := by
    have hnat : (21154647 : ℕ)^8441*50000000000000^6393 ≤ 21562023453639^6393*40000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21154647 40000000 21562023453639 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274487039/500000000 : ℝ)^8441 ≤ (22650989242201/50000000000000 : ℝ)^6393 := by
    have hnat : (274487039 : ℕ)^8441*50000000000000^6393 ≤ 22650989242201^6393*500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274487039 500000000 22650989242201 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1953013929/10000000000 : ℝ)^8441 ≤ (11573974595943/100000000000000 : ℝ)^6393 := by
    have hnat : (1953013929 : ℕ)^8441*100000000000000^6393 ≤ 11573974595943^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953013929 10000000000 11573974595943 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21154647/40000000 : ℝ), (274487039/500000000 : ℝ), (-1953013929/10000000000 : ℝ)] ![(21562023453639/50000000000000 : ℝ), (22650989242201/50000000000000 : ℝ), (11573974595943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21154647/40000000 : ℝ)|^8441 ≤ (21562023453639/50000000000000 : ℝ)^6393
        have hw : |(21154647/40000000 : ℝ)|=(21154647/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274487039/500000000 : ℝ)|^8441 ≤ (22650989242201/50000000000000 : ℝ)^6393
        have hw : |(274487039/500000000 : ℝ)|=(274487039/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1953013929/10000000000 : ℝ)|^8441 ≤ (11573974595943/100000000000000 : ℝ)^6393
        have hw : |(-1953013929/10000000000 : ℝ)|=(1953013929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s2_7 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (434148013/1000000000 : ℝ)*x 0 + (583726299/1250000000 : ℝ)*x 1 + (807169939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434148013/1000000000 : ℝ)^8441 ≤ (16615941636039/50000000000000 : ℝ)^6393 := by
    have hnat : (434148013 : ℕ)^8441*50000000000000^6393 ≤ 16615941636039^6393*1000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434148013 1000000000 16615941636039 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (583726299/1250000000 : ℝ)^8441 ≤ (3658972407231/10000000000000 : ℝ)^6393 := by
    have hnat : (583726299 : ℕ)^8441*10000000000000^6393 ≤ 3658972407231^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583726299 1250000000 3658972407231 10000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (807169939/2000000000 : ℝ)^8441 ≤ (15089196319401/50000000000000 : ℝ)^6393 := by
    have hnat : (807169939 : ℕ)^8441*50000000000000^6393 ≤ 15089196319401^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807169939 2000000000 15089196319401 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434148013/1000000000 : ℝ), (583726299/1250000000 : ℝ), (807169939/2000000000 : ℝ)] ![(16615941636039/50000000000000 : ℝ), (3658972407231/10000000000000 : ℝ), (15089196319401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434148013/1000000000 : ℝ)|^8441 ≤ (16615941636039/50000000000000 : ℝ)^6393
        have hw : |(434148013/1000000000 : ℝ)|=(434148013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(583726299/1250000000 : ℝ)|^8441 ≤ (3658972407231/10000000000000 : ℝ)^6393
        have hw : |(583726299/1250000000 : ℝ)|=(583726299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(807169939/2000000000 : ℝ)|^8441 ≤ (15089196319401/50000000000000 : ℝ)^6393
        have hw : |(807169939/2000000000 : ℝ)|=(807169939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1248_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9987/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3111/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9523/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1013/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9987/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3111/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9987/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3111/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9987/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3111/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9987/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3111/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9987/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3111/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9987/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3111/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3111/50000 : ℝ) ^ (1055/256 : ℝ) ≤ (535355776624801/50000000000000000000 : ℝ) := by
    have hpowers : (3111/50000 : ℝ)^1055 ≤ (535355776624801/50000000000000000000 : ℝ)^256 := by
      have hnat : (3111 : ℕ)^1055*50000000000000000000^256 ≤ 535355776624801^256*50000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3111 50000 535355776624801 50000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3111/50000 : ℝ)) (X := (535355776624801/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hpowhi : (9987/50000 : ℝ) ^ (1055/256 : ℝ) ≤ (130963680386800261/100000000000000000000 : ℝ) := by
    have hpowers : (9987/50000 : ℝ)^1055 ≤ (130963680386800261/100000000000000000000 : ℝ)^256 := by
      have hnat : (9987 : ℕ)^1055*100000000000000000000^256 ≤ 130963680386800261^256*50000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9987 50000 130963680386800261 100000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9987/50000 : ℝ)) (X := (130963680386800261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000535355776624801/25000000000000000000 : ℝ) ≤ (500002598103649/500000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (25000535355776624801/25000000000000000000 : ℝ)^256 ≤ (500002598103649/500000000000000 : ℝ)^1055 := by
      have hnat : (25000535355776624801 : ℕ)^256*500000000000000^1055 ≤ 500002598103649^1055*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000535355776624801 25000000000000000000 500002598103649 500000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500002598103649/500000000000000 : ℝ)) (X := (25000535355776624801/25000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100132034391940049863/100000000000000000000 : ℝ) ≤ (2500800566770559/2500000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (100132034391940049863/100000000000000000000 : ℝ)^256 ≤ (2500800566770559/2500000000000000 : ℝ)^1055 := by
      have hnat : (100132034391940049863 : ℕ)^256*2500000000000000^1055 ≤ 2500800566770559^1055*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100132034391940049863 100000000000000000000 2500800566770559 2500000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500800566770559/2500000000000000 : ℝ)) (X := (100132034391940049863/100000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50130963680386800261/50000000000000000000 : ℝ) ≤ (2501588143022873/2500000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50130963680386800261/50000000000000000000 : ℝ)^256 ≤ (2501588143022873/2500000000000000 : ℝ)^1055 := by
      have hnat : (50130963680386800261 : ℕ)^256*2500000000000000^1055 ≤ 2501588143022873^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50130963680386800261 50000000000000000000 2501588143022873 2500000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501588143022873/2500000000000000 : ℝ)) (X := (50130963680386800261/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(535355776624801/50000000000000000000 : ℝ) ≤ ((59670795220005399/59687500000000000 : ℝ)+2*(131262708719/57300000000000 : ℝ)*(3111/50000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (59670795220005399/59687500000000000 : ℝ)+2*(131262708719/57300000000000 : ℝ)*(3111/50000 : ℝ)=(500002598103649/500000000000000 : ℝ) by norm_num, show 1+2*(535355776624801/50000000000000000000 : ℝ)=(25000535355776624801/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(130963680386800261/100000000000000000000 : ℝ)+(535355776624801/50000000000000000000 : ℝ) ≤ ((59670795220005399/59687500000000000 : ℝ)+(131262708719/57300000000000 : ℝ)*((9987/50000 : ℝ)+(3111/50000 : ℝ)))^(1055/256 : ℝ) := by
    rw [show (59670795220005399/59687500000000000 : ℝ)+(131262708719/57300000000000 : ℝ)*((9987/50000 : ℝ)+(3111/50000 : ℝ))=(2500800566770559/2500000000000000 : ℝ) by norm_num, show 1+(130963680386800261/100000000000000000000 : ℝ)+(535355776624801/50000000000000000000 : ℝ)=(100132034391940049863/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(130963680386800261/100000000000000000000 : ℝ) ≤ ((59670795220005399/59687500000000000 : ℝ)+2*(131262708719/57300000000000 : ℝ)*(9987/50000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (59670795220005399/59687500000000000 : ℝ)+2*(131262708719/57300000000000 : ℝ)*(9987/50000 : ℝ)=(2501588143022873/2500000000000000 : ℝ) by norm_num, show 1+2*(130963680386800261/100000000000000000000 : ℝ)=(50130963680386800261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59670795220005399/59687500000000000 : ℝ)*(X 1 0+X 2 0)+(131262708719/57300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (3111/50000 : ℝ)) (hi := (9987/50000 : ℝ)) (c := (59670795220005399/59687500000000000 : ℝ)) (alpha := (131262708719/57300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59670795220005399/59687500000000000 : ℝ)*(X 0 1+X 2 1)+(131262708719/57300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (3111/50000 : ℝ)) (hi := (9987/50000 : ℝ)) (c := (59670795220005399/59687500000000000 : ℝ)) (alpha := (131262708719/57300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59670795220005399/59687500000000000 : ℝ)*(X 0 2+X 1 2)+(131262708719/57300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (3111/50000 : ℝ)) (hi := (9987/50000 : ℝ)) (c := (59670795220005399/59687500000000000 : ℝ)) (alpha := (131262708719/57300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-420685167/2000000000 : ℝ)*X 0 0+(5491784159/10000000000 : ℝ)*X 0 1+(1293890539/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369446359/10000000000 : ℝ)*X 1 0+(-1133596467/5000000000 : ℝ)*X 1 1+(5175562217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369446233/10000000000 : ℝ)*X 2 0+(2587781153/5000000000 : ℝ)*X 2 1+(-453438597/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4341323853/10000000000 : ℝ)*X 0 0+(2015850087/5000000000 : ℝ)*X 0 1+(934784373/2000000000 : ℝ)*X 0 2+(4341323853/10000000000 : ℝ)*X 1 0+(2015850087/5000000000 : ℝ)*X 1 1+(934784373/2000000000 : ℝ)*X 1 2+(4341323853/10000000000 : ℝ)*X 2 0+(2015850087/5000000000 : ℝ)*X 2 1+(934784373/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-420700607/2000000000 : ℝ)*X 0 0+(2588793379/5000000000 : ℝ)*X 0 1+(1372435161/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644330797/5000000000 : ℝ)*X 1 0+(-195301427/1000000000 : ℝ)*X 1 1+(5489740689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((21154647/40000000 : ℝ)*X 2 0+(274487039/500000000 : ℝ)*X 2 1+(-1953013929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434148013/1000000000 : ℝ)*X 0 0+(583726299/1250000000 : ℝ)*X 0 1+(807169939/2000000000 : ℝ)*X 0 2+(434148013/1000000000 : ℝ)*X 1 0+(583726299/1250000000 : ℝ)*X 1 1+(807169939/2000000000 : ℝ)*X 1 2+(434148013/1000000000 : ℝ)*X 2 0+(583726299/1250000000 : ℝ)*X 2 1+(807169939/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (915666334370953873959/95500000000000000000000000 : ℝ) := by norm_num
    linear_combination (918298881/50000000000000 : ℝ)*(base19) + (1646148077/100000000000000 : ℝ)*(base23) + (31207501/50000000000000 : ℝ)*(lower2) + (280337741/100000000000000 : ℝ)*(upper3) + (13143689/10000000000000 : ℝ)*(upper5) + (14748415639577/625000000000 : ℝ)*(major0) + (14748415639577/625000000000 : ℝ)*(major1) + (14748415639577/625000000000 : ℝ)*(major2) + (158117881103033/5000000000000 : ℝ)*(sp0) + (790593919716463/25000000000000 : ℝ)*(sp1) + (3162375869315537/100000000000000 : ℝ)*(sp2) + (1557104173330471/100000000000000 : ℝ)*(sp3) + (9946701477/50000000000000 : ℝ)*(sp4) + (2749066561/25000000000000 : ℝ)*(sp7) + (389278792399179/25000000000000 : ℝ)*(f.failure) + (1581188757731807/50000000000000 : ℝ)*(f.sum) + (48560183627/573000000000000000000000000 : ℝ)*base65 + (3105836740848773/895312500000000000000000000000 : ℝ)*base68 + (4086369082486829/1790625000000000000000000000000 : ℝ)*base69 + (8693142515825671/1790625000000000000000000000000 : ℝ)*base72 + (479734917367/286500000000000000000000000 : ℝ)*base73 + (17790257588724329/1790625000000000000000000000000 : ℝ)*base75 + (3125984338255301/447656250000000000000000000000 : ℝ)*base77 + (480235622963449/447656250000000000000000000000 : ℝ)*base80 + (395499271483/286500000000000000000000000 : ℝ)*base81 + (248353/39062500000000000000 : ℝ)*base89 + (248353/39062500000000000000 : ℝ)*base91 + (248353/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39532843567519492217/5000000000000000000000000 : ℝ) := by norm_num
    linear_combination (990018207/50000000000000 : ℝ)*(base19) + (44459611/2000000000000 : ℝ)*(base23) + (14958199/50000000000000 : ℝ)*(upper2) + (53140459/20000000000000 : ℝ)*(upper3) + (38767673/25000000000000 : ℝ)*(upper5) + (1195233138483259/50000000000000 : ℝ)*(major0) + (1195233138483259/50000000000000 : ℝ)*(major1) + (1195233138483259/50000000000000 : ℝ)*(major2) + (20426651963/100000000000000 : ℝ)*(sp1) + (13220947147/50000000000000 : ℝ)*(sp2) + (1601773101553059/50000000000000 : ℝ)*(sp4) + (160176189820887/5000000000000 : ℝ)*(sp5) + (128140701529251/4000000000000 : ℝ)*(sp6) + (78869304363731/5000000000000 : ℝ)*(sp7) + (78869304363731/5000000000000 : ℝ)*(f.failure) + (1601773101553059/50000000000000 : ℝ)*(f.sum) + (132475597/3750000000000000000000000 : ℝ)*base66 + (27797903687957/11718750000000000000000000000 : ℝ)*base67 + (45747382343293/11718750000000000000000000000 : ℝ)*base70 + (245680940079953/46875000000000000000000000000 : ℝ)*base71 + (1372626923/3750000000000000000000000 : ℝ)*base73 + (88817743798703/46875000000000000000000000000 : ℝ)*base75 + (18160260019417/2929687500000000000000000000 : ℝ)*base78 + (27258114956917/2929687500000000000000000000 : ℝ)*base80 + (30503672863/15000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (37733/7812500000000000000 : ℝ)*base90 + (37733/7812500000000000000 : ℝ)*base92 + (37733/7812500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1248_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9987/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3111/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9523/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1013/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1248_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1248_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9523/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1013/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1248_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1248_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1248_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9523/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1013/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1248_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
