-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1170_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:45:08.578753+00:00
-- url     : https://prove2.me/submissions/9b117aae-b319-4ec7-a1de-50b9a5f9df4b

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
theorem support_rectangle_w1170_s6_0 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153541521/10000000000 : ℝ)*x 0 + (1348204643/2500000000 : ℝ)*x 1 + (1316476249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153541521/10000000000 : ℝ)^8363 ≤ (1308850501283/10000000000000 : ℝ)^6315 := by
    have hnat : (2153541521 : ℕ)^8363*10000000000000^6315 ≤ 1308850501283^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153541521 10000000000 1308850501283 10000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348204643/2500000000 : ℝ)^8363 ≤ (22070478496413/50000000000000 : ℝ)^6315 := by
    have hnat : (1348204643 : ℕ)^8363*50000000000000^6315 ≤ 22070478496413^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348204643 2500000000 22070478496413 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316476249/2500000000 : ℝ)^8363 ≤ (21385268992947/50000000000000 : ℝ)^6315 := by
    have hnat : (1316476249 : ℕ)^8363*50000000000000^6315 ≤ 21385268992947^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316476249 2500000000 21385268992947 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153541521/10000000000 : ℝ), (1348204643/2500000000 : ℝ), (1316476249/2500000000 : ℝ)] ![(1308850501283/10000000000000 : ℝ), (22070478496413/50000000000000 : ℝ), (21385268992947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153541521/10000000000 : ℝ)|^8363 ≤ (1308850501283/10000000000000 : ℝ)^6315
        have hw : |(-2153541521/10000000000 : ℝ)|=(2153541521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348204643/2500000000 : ℝ)|^8363 ≤ (22070478496413/50000000000000 : ℝ)^6315
        have hw : |(1348204643/2500000000 : ℝ)|=(1348204643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316476249/2500000000 : ℝ)|^8363 ≤ (21385268992947/50000000000000 : ℝ)^6315
        have hw : |(1316476249/2500000000 : ℝ)|=(1316476249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s6_1 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344722427/10000000000 : ℝ)*x 0 + (-1108955749/5000000000 : ℝ)*x 1 + (658238129/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344722427/10000000000 : ℝ)^8363 ≤ (1744814711621/4000000000000 : ℝ)^6315 := by
    have hnat : (5344722427 : ℕ)^8363*4000000000000^6315 ≤ 1744814711621^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344722427 10000000000 1744814711621 4000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108955749/5000000000 : ℝ)^8363 ≤ (3402273453843/25000000000000 : ℝ)^6315 := by
    have hnat : (1108955749 : ℕ)^8363*25000000000000^6315 ≤ 3402273453843^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108955749 5000000000 3402273453843 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658238129/1250000000 : ℝ)^8363 ≤ (21385269186559/50000000000000 : ℝ)^6315 := by
    have hnat : (658238129 : ℕ)^8363*50000000000000^6315 ≤ 21385269186559^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658238129 1250000000 21385269186559 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344722427/10000000000 : ℝ), (-1108955749/5000000000 : ℝ), (658238129/1250000000 : ℝ)] ![(1744814711621/4000000000000 : ℝ), (3402273453843/25000000000000 : ℝ), (21385269186559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344722427/10000000000 : ℝ)|^8363 ≤ (1744814711621/4000000000000 : ℝ)^6315
        have hw : |(5344722427/10000000000 : ℝ)|=(5344722427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1108955749/5000000000 : ℝ)|^8363 ≤ (3402273453843/25000000000000 : ℝ)^6315
        have hw : |(-1108955749/5000000000 : ℝ)|=(1108955749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658238129/1250000000 : ℝ)|^8363 ≤ (21385269186559/50000000000000 : ℝ)^6315
        have hw : |(658238129/1250000000 : ℝ)|=(658238129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s6_2 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336180631/2500000000 : ℝ)*x 0 + (5265904881/10000000000 : ℝ)*x 1 + (-2217911569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336180631/2500000000 : ℝ)^8363 ≤ (43620368838919/100000000000000 : ℝ)^6315 := by
    have hnat : (1336180631 : ℕ)^8363*100000000000000^6315 ≤ 43620368838919^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336180631 2500000000 43620368838919 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265904881/10000000000 : ℝ)^8363 ≤ (21385268374463/50000000000000 : ℝ)^6315 := by
    have hnat : (5265904881 : ℕ)^8363*50000000000000^6315 ≤ 21385268374463^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265904881 10000000000 21385268374463 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217911569/10000000000 : ℝ)^8363 ≤ (13609094392313/100000000000000 : ℝ)^6315 := by
    have hnat : (2217911569 : ℕ)^8363*100000000000000^6315 ≤ 13609094392313^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217911569 10000000000 13609094392313 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336180631/2500000000 : ℝ), (5265904881/10000000000 : ℝ), (-2217911569/10000000000 : ℝ)] ![(43620368838919/100000000000000 : ℝ), (21385268374463/50000000000000 : ℝ), (13609094392313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336180631/2500000000 : ℝ)|^8363 ≤ (43620368838919/100000000000000 : ℝ)^6315
        have hw : |(1336180631/2500000000 : ℝ)|=(1336180631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265904881/10000000000 : ℝ)|^8363 ≤ (21385268374463/50000000000000 : ℝ)^6315
        have hw : |(5265904881/10000000000 : ℝ)|=(5265904881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2217911569/10000000000 : ℝ)|^8363 ≤ (13609094392313/100000000000000 : ℝ)^6315
        have hw : |(-2217911569/10000000000 : ℝ)|=(2217911569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s6_3 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360729109/10000000000 : ℝ)*x 0 + (4235615821/10000000000 : ℝ)*x 1 + (4489495009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360729109/10000000000 : ℝ)^8363 ≤ (33316972541323/100000000000000 : ℝ)^6315 := by
    have hnat : (4360729109 : ℕ)^8363*100000000000000^6315 ≤ 33316972541323^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360729109 10000000000 33316972541323 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235615821/10000000000 : ℝ)^8363 ≤ (32057002770077/100000000000000 : ℝ)^6315 := by
    have hnat : (4235615821 : ℕ)^8363*100000000000000^6315 ≤ 32057002770077^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235615821 10000000000 32057002770077 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489495009/10000000000 : ℝ)^8363 ≤ (34626024673357/100000000000000 : ℝ)^6315 := by
    have hnat : (4489495009 : ℕ)^8363*100000000000000^6315 ≤ 34626024673357^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489495009 10000000000 34626024673357 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360729109/10000000000 : ℝ), (4235615821/10000000000 : ℝ), (4489495009/10000000000 : ℝ)] ![(33316972541323/100000000000000 : ℝ), (32057002770077/100000000000000 : ℝ), (34626024673357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360729109/10000000000 : ℝ)|^8363 ≤ (33316972541323/100000000000000 : ℝ)^6315
        have hw : |(4360729109/10000000000 : ℝ)|=(4360729109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235615821/10000000000 : ℝ)|^8363 ≤ (32057002770077/100000000000000 : ℝ)^6315
        have hw : |(4235615821/10000000000 : ℝ)|=(4235615821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489495009/10000000000 : ℝ)|^8363 ≤ (34626024673357/100000000000000 : ℝ)^6315
        have hw : |(4489495009/10000000000 : ℝ)|=(4489495009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s6_4 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076773251/5000000000 : ℝ)*x 0 + (1053245097/2000000000 : ℝ)*x 1 + (5392496843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076773251/5000000000 : ℝ)^8363 ≤ (13088545103401/100000000000000 : ℝ)^6315 := by
    have hnat : (1076773251 : ℕ)^8363*100000000000000^6315 ≤ 13088545103401^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076773251 5000000000 13088545103401 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053245097/2000000000 : ℝ)^8363 ≤ (42773985276129/100000000000000 : ℝ)^6315 := by
    have hnat : (1053245097 : ℕ)^8363*100000000000000^6315 ≤ 42773985276129^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053245097 2000000000 42773985276129 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392496843/10000000000 : ℝ)^8363 ≤ (44137469601489/100000000000000 : ℝ)^6315 := by
    have hnat : (5392496843 : ℕ)^8363*100000000000000^6315 ≤ 44137469601489^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392496843 10000000000 44137469601489 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076773251/5000000000 : ℝ), (1053245097/2000000000 : ℝ), (5392496843/10000000000 : ℝ)] ![(13088545103401/100000000000000 : ℝ), (42773985276129/100000000000000 : ℝ), (44137469601489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076773251/5000000000 : ℝ)|^8363 ≤ (13088545103401/100000000000000 : ℝ)^6315
        have hw : |(-1076773251/5000000000 : ℝ)|=(1076773251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053245097/2000000000 : ℝ)|^8363 ≤ (42773985276129/100000000000000 : ℝ)^6315
        have hw : |(1053245097/2000000000 : ℝ)|=(1053245097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392496843/10000000000 : ℝ)|^8363 ≤ (44137469601489/100000000000000 : ℝ)^6315
        have hw : |(5392496843/10000000000 : ℝ)|=(5392496843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s6_5 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531250243/1000000000 : ℝ)*x 0 + (-1045659803/5000000000 : ℝ)*x 1 + (2696248423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531250243/1000000000 : ℝ)^8363 ≤ (865449377319/2000000000000 : ℝ)^6315 := by
    have hnat : (531250243 : ℕ)^8363*2000000000000^6315 ≤ 865449377319^6315*1000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531250243 1000000000 865449377319 2000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045659803/5000000000 : ℝ)^8363 ≤ (786878843049/6250000000000 : ℝ)^6315 := by
    have hnat : (1045659803 : ℕ)^8363*6250000000000^6315 ≤ 786878843049^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045659803 5000000000 786878843049 6250000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696248423/5000000000 : ℝ)^8363 ≤ (44137469634007/100000000000000 : ℝ)^6315 := by
    have hnat : (2696248423 : ℕ)^8363*100000000000000^6315 ≤ 44137469634007^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696248423 5000000000 44137469634007 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531250243/1000000000 : ℝ), (-1045659803/5000000000 : ℝ), (2696248423/5000000000 : ℝ)] ![(865449377319/2000000000000 : ℝ), (786878843049/6250000000000 : ℝ), (44137469634007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531250243/1000000000 : ℝ)|^8363 ≤ (865449377319/2000000000000 : ℝ)^6315
        have hw : |(531250243/1000000000 : ℝ)|=(531250243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1045659803/5000000000 : ℝ)|^8363 ≤ (786878843049/6250000000000 : ℝ)^6315
        have hw : |(-1045659803/5000000000 : ℝ)|=(1045659803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696248423/5000000000 : ℝ)|^8363 ≤ (44137469634007/100000000000000 : ℝ)^6315
        have hw : |(2696248423/5000000000 : ℝ)|=(2696248423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s6_6 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312502431/10000000000 : ℝ)*x 0 + (5392496821/10000000000 : ℝ)*x 1 + (-2091319639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312502431/10000000000 : ℝ)^8363 ≤ (43272468876737/100000000000000 : ℝ)^6315 := by
    have hnat : (5312502431 : ℕ)^8363*100000000000000^6315 ≤ 43272468876737^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312502431 10000000000 43272468876737 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392496821/10000000000 : ℝ)^8363 ≤ (22068734681511/50000000000000 : ℝ)^6315 := by
    have hnat : (5392496821 : ℕ)^8363*50000000000000^6315 ≤ 22068734681511^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392496821 10000000000 22068734681511 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091319639/10000000000 : ℝ)^8363 ≤ (12590061751877/100000000000000 : ℝ)^6315 := by
    have hnat : (2091319639 : ℕ)^8363*100000000000000^6315 ≤ 12590061751877^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091319639 10000000000 12590061751877 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312502431/10000000000 : ℝ), (5392496821/10000000000 : ℝ), (-2091319639/10000000000 : ℝ)] ![(43272468876737/100000000000000 : ℝ), (22068734681511/50000000000000 : ℝ), (12590061751877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312502431/10000000000 : ℝ)|^8363 ≤ (43272468876737/100000000000000 : ℝ)^6315
        have hw : |(5312502431/10000000000 : ℝ)|=(5312502431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392496821/10000000000 : ℝ)|^8363 ≤ (22068734681511/50000000000000 : ℝ)^6315
        have hw : |(5392496821/10000000000 : ℝ)|=(5392496821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091319639/10000000000 : ℝ)|^8363 ≤ (12590061751877/100000000000000 : ℝ)^6315
        have hw : |(-2091319639/10000000000 : ℝ)|=(2091319639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s6_7 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180369349/5000000000 : ℝ)*x 0 + (280553353/625000000 : ℝ)*x 1 + (2118129847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180369349/5000000000 : ℝ)^8363 ≤ (4164633695371/12500000000000 : ℝ)^6315 := by
    have hnat : (2180369349 : ℕ)^8363*12500000000000^6315 ≤ 4164633695371^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180369349 5000000000 4164633695371 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280553353/625000000 : ℝ)^8363 ≤ (34619473993581/100000000000000 : ℝ)^6315 := by
    have hnat : (280553353 : ℕ)^8363*100000000000000^6315 ≤ 34619473993581^6315*625000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280553353 625000000 34619473993581 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118129847/5000000000 : ℝ)^8363 ≤ (32063456429063/100000000000000 : ℝ)^6315 := by
    have hnat : (2118129847 : ℕ)^8363*100000000000000^6315 ≤ 32063456429063^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118129847 5000000000 32063456429063 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180369349/5000000000 : ℝ), (280553353/625000000 : ℝ), (2118129847/5000000000 : ℝ)] ![(4164633695371/12500000000000 : ℝ), (34619473993581/100000000000000 : ℝ), (32063456429063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180369349/5000000000 : ℝ)|^8363 ≤ (4164633695371/12500000000000 : ℝ)^6315
        have hw : |(2180369349/5000000000 : ℝ)|=(2180369349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280553353/625000000 : ℝ)|^8363 ≤ (34619473993581/100000000000000 : ℝ)^6315
        have hw : |(280553353/625000000 : ℝ)|=(280553353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118129847/5000000000 : ℝ)|^8363 ≤ (32063456429063/100000000000000 : ℝ)^6315
        have hw : |(2118129847/5000000000 : ℝ)|=(2118129847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1170_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11383/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1759/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2839/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2839/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2839/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2839/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2839/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2839/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2839/25000 : ℝ) ^ (4181/1024 : ℝ) ≤ (1388282538455843/10000000000000000000 : ℝ) := by
    have hpowers : (2839/25000 : ℝ)^4181 ≤ (1388282538455843/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2839 : ℕ)^4181*10000000000000000000^1024 ≤ 1388282538455843^1024*25000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2839 25000 1388282538455843 10000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2839/25000 : ℝ)) (X := (1388282538455843/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (141/1000 : ℝ) ^ (4181/1024 : ℝ) ≤ (1679673980059439/5000000000000000000 : ℝ) := by
    have hpowers : (141/1000 : ℝ)^4181 ≤ (1679673980059439/5000000000000000000 : ℝ)^1024 := by
      have hnat : (141 : ℕ)^4181*5000000000000000000^1024 ≤ 1679673980059439^1024*1000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 1000 1679673980059439 5000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/1000 : ℝ)) (X := (1679673980059439/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001388282538455843/5000000000000000000 : ℝ) ≤ (5000339979029343/5000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (5001388282538455843/5000000000000000000 : ℝ)^1024 ≤ (5000339979029343/5000000000000000 : ℝ)^4181 := by
      have hnat : (5001388282538455843 : ℕ)^1024*5000000000000000^4181 ≤ 5000339979029343^4181*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001388282538455843 5000000000000000000 5000339979029343 5000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000339979029343/5000000000000000 : ℝ)) (X := (5001388282538455843/5000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004747630498574721/10000000000000000000 : ℝ) ≤ (1000116256935451/1000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (10004747630498574721/10000000000000000000 : ℝ)^1024 ≤ (1000116256935451/1000000000000000 : ℝ)^4181 := by
      have hnat : (10004747630498574721 : ℕ)^1024*1000000000000000^4181 ≤ 1000116256935451^4181*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004747630498574721 10000000000000000000 1000116256935451 1000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000116256935451/1000000000000000 : ℝ)) (X := (10004747630498574721/10000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501679673980059439/2500000000000000000 : ℝ) ≤ (5000822590325167/5000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (2501679673980059439/2500000000000000000 : ℝ)^1024 ≤ (5000822590325167/5000000000000000 : ℝ)^4181 := by
      have hnat : (2501679673980059439 : ℕ)^1024*5000000000000000^4181 ≤ 5000822590325167^4181*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501679673980059439 2500000000000000000 5000822590325167 5000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000822590325167/5000000000000000 : ℝ)) (X := (2501679673980059439/2500000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1388282538455843/10000000000000000000 : ℝ) ≤ ((244918792296091783/245000000000000000 : ℝ)+2*(4309029427/2450000000000 : ℝ)*(2839/25000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (244918792296091783/245000000000000000 : ℝ)+2*(4309029427/2450000000000 : ℝ)*(2839/25000 : ℝ)=(5000339979029343/5000000000000000 : ℝ) by norm_num, show 1+2*(1388282538455843/10000000000000000000 : ℝ)=(5001388282538455843/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1679673980059439/5000000000000000000 : ℝ)+(1388282538455843/10000000000000000000 : ℝ) ≤ ((244918792296091783/245000000000000000 : ℝ)+(4309029427/2450000000000 : ℝ)*((141/1000 : ℝ)+(2839/25000 : ℝ)))^(4181/1024 : ℝ) := by
    rw [show (244918792296091783/245000000000000000 : ℝ)+(4309029427/2450000000000 : ℝ)*((141/1000 : ℝ)+(2839/25000 : ℝ))=(1000116256935451/1000000000000000 : ℝ) by norm_num, show 1+(1679673980059439/5000000000000000000 : ℝ)+(1388282538455843/10000000000000000000 : ℝ)=(10004747630498574721/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1679673980059439/5000000000000000000 : ℝ) ≤ ((244918792296091783/245000000000000000 : ℝ)+2*(4309029427/2450000000000 : ℝ)*(141/1000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (244918792296091783/245000000000000000 : ℝ)+2*(4309029427/2450000000000 : ℝ)*(141/1000 : ℝ)=(5000822590325167/5000000000000000 : ℝ) by norm_num, show 1+2*(1679673980059439/5000000000000000000 : ℝ)=(2501679673980059439/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (244918792296091783/245000000000000000 : ℝ)*(X 1 0+X 2 0)+(4309029427/2450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (2839/25000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (244918792296091783/245000000000000000 : ℝ)) (alpha := (4309029427/2450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (244918792296091783/245000000000000000 : ℝ)*(X 0 1+X 2 1)+(4309029427/2450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (2839/25000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (244918792296091783/245000000000000000 : ℝ)) (alpha := (4309029427/2450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (244918792296091783/245000000000000000 : ℝ)*(X 0 2+X 1 2)+(4309029427/2450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (2839/25000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (244918792296091783/245000000000000000 : ℝ)) (alpha := (4309029427/2450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2153541521/10000000000 : ℝ)*X 0 0+(1348204643/2500000000 : ℝ)*X 0 1+(1316476249/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344722427/10000000000 : ℝ)*X 1 0+(-1108955749/5000000000 : ℝ)*X 1 1+(658238129/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336180631/2500000000 : ℝ)*X 2 0+(5265904881/10000000000 : ℝ)*X 2 1+(-2217911569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360729109/10000000000 : ℝ)*X 0 0+(4235615821/10000000000 : ℝ)*X 0 1+(4489495009/10000000000 : ℝ)*X 0 2+(4360729109/10000000000 : ℝ)*X 1 0+(4235615821/10000000000 : ℝ)*X 1 1+(4489495009/10000000000 : ℝ)*X 1 2+(4360729109/10000000000 : ℝ)*X 2 0+(4235615821/10000000000 : ℝ)*X 2 1+(4489495009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1076773251/5000000000 : ℝ)*X 0 0+(1053245097/2000000000 : ℝ)*X 0 1+(5392496843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531250243/1000000000 : ℝ)*X 1 0+(-1045659803/5000000000 : ℝ)*X 1 1+(2696248423/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312502431/10000000000 : ℝ)*X 2 0+(5392496821/10000000000 : ℝ)*X 2 1+(-2091319639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180369349/5000000000 : ℝ)*X 0 0+(280553353/625000000 : ℝ)*X 0 1+(2118129847/5000000000 : ℝ)*X 0 2+(2180369349/5000000000 : ℝ)*X 1 0+(280553353/625000000 : ℝ)*X 1 1+(2118129847/5000000000 : ℝ)*X 1 2+(2180369349/5000000000 : ℝ)*X 2 0+(280553353/625000000 : ℝ)*X 2 1+(2118129847/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26740382095624871072841483/3062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95641333/6250000000000 : ℝ)*(base19) + (10362591/781250000000 : ℝ)*(base23) + (46345667/25000000000000 : ℝ)*(lower2) + (344728139/100000000000000 : ℝ)*(upper3) + (310413/50000000000000 : ℝ)*(upper5) + (1477297306463511/25000000000000 : ℝ)*(major0) + (1477297306463511/25000000000000 : ℝ)*(major1) + (1477297306463511/25000000000000 : ℝ)*(major2) + (1575883980579751/20000000000000 : ℝ)*(sp0) + (984931326046649/12500000000000 : ℝ)*(sp1) + (984931351527859/12500000000000 : ℝ)*(sp2) + (1969449417422813/50000000000000 : ℝ)*(sp3) + (8058933941/25000000000000 : ℝ)*(sp4) + (13593588077/50000000000000 : ℝ)*(sp7) + (196946301101089/5000000000000 : ℝ)*(f.failure) + (196986303465863/2500000000000 : ℝ)*(f.sum) + (1988622849041/245000000000000000000000000 : ℝ)*base65 + (55451148620880113/6125000000000000000000000000000 : ℝ)*base67 + (106677534646380113/6125000000000000000000000000000 : ℝ)*base69 + (101969729992380113/6125000000000000000000000000000 : ℝ)*base71 + (765473305343/122500000000000000000000000 : ℝ)*base73 + (14203331335380113/6125000000000000000000000000000 : ℝ)*base75 + (70007079335380113/6125000000000000000000000000000 : ℝ)*base77 + (22240082774880113/6125000000000000000000000000000 : ℝ)*base79 + (275790063393/122500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (275393/100000000000000000000 : ℝ)*base90 + (275393/100000000000000000000 : ℝ)*base92 + (275393/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16487759035773673800157623/1531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (957717261/50000000000000 : ℝ)*(base19) + (2013409123/100000000000000 : ℝ)*(base23) + (204284373/100000000000000 : ℝ)*(upper3) + (26070899/50000000000000 : ℝ)*(lower4) + (228420127/100000000000000 : ℝ)*(upper5) + (742398388625577/12500000000000 : ℝ)*(major0) + (742398388625577/12500000000000 : ℝ)*(major1) + (742398388625577/12500000000000 : ℝ)*(major2) + (17204993/32000000000 : ℝ)*(sp1) + (53490858983/100000000000000 : ℝ)*(sp2) + (3959725978205983/50000000000000 : ℝ)*(sp4) + (7919396275374319/100000000000000 : ℝ)*(sp5) + (395969822607193/5000000000000 : ℝ)*(sp6) + (1979460951340029/50000000000000 : ℝ)*(sp7) + (1979460951340029/50000000000000 : ℝ)*(f.failure) + (3959725978205983/50000000000000 : ℝ)*(f.sum) + (3535984057/7656250000000000000000000 : ℝ)*base65 + (4403940899141209/3062500000000000000000000000000 : ℝ)*base68 + (33117636168141209/3062500000000000000000000000000 : ℝ)*base70 + (16601566112421291/3062500000000000000000000000000 : ℝ)*base71 + (16584193791/61250000000000000000000000 : ℝ)*base73 + (23522515997141209/3062500000000000000000000000000 : ℝ)*base76 + (5136554665983791/3062500000000000000000000000000 : ℝ)*base77 + (24735607591453709/3062500000000000000000000000000 : ℝ)*base80 + (1132722469261/245000000000000000000000000 : ℝ)*base82 + (4537827/1000000000000000000000 : ℝ)*base89 + (4537827/1000000000000000000000 : ℝ)*base91 + (4537827/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1170_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1170_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1170_s7_0 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076782207/5000000000 : ℝ)*x 0 + (539254477/1000000000 : ℝ)*x 1 + (1053232757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076782207/5000000000 : ℝ)^8363 ≤ (261773785439/2000000000000 : ℝ)^6315 := by
    have hnat : (1076782207 : ℕ)^8363*2000000000000^6315 ≤ 261773785439^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076782207 5000000000 261773785439 2000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539254477/1000000000 : ℝ)^8363 ≤ (22068994551697/50000000000000 : ℝ)^6315 := by
    have hnat : (539254477 : ℕ)^8363*50000000000000^6315 ≤ 22068994551697^6315*1000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539254477 1000000000 22068994551697 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053232757/2000000000 : ℝ)^8363 ≤ (21386660802179/50000000000000 : ℝ)^6315 := by
    have hnat : (1053232757 : ℕ)^8363*50000000000000^6315 ≤ 21386660802179^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053232757 2000000000 21386660802179 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076782207/5000000000 : ℝ), (539254477/1000000000 : ℝ), (1053232757/2000000000 : ℝ)] ![(261773785439/2000000000000 : ℝ), (22068994551697/50000000000000 : ℝ), (21386660802179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076782207/5000000000 : ℝ)|^8363 ≤ (261773785439/2000000000000 : ℝ)^6315
        have hw : |(-1076782207/5000000000 : ℝ)|=(1076782207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539254477/1000000000 : ℝ)|^8363 ≤ (22068994551697/50000000000000 : ℝ)^6315
        have hw : |(539254477/1000000000 : ℝ)|=(539254477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053232757/2000000000 : ℝ)|^8363 ≤ (21386660802179/50000000000000 : ℝ)^6315
        have hw : |(1053232757/2000000000 : ℝ)|=(1053232757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s7_1 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534465373/1000000000 : ℝ)*x 0 + (-1108830163/5000000000 : ℝ)*x 1 + (5266163807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534465373/1000000000 : ℝ)^8363 ≤ (10904906325487/25000000000000 : ℝ)^6315 := by
    have hnat : (534465373 : ℕ)^8363*25000000000000^6315 ≤ 10904906325487^6315*1000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534465373 1000000000 10904906325487 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108830163/5000000000 : ℝ)^8363 ≤ (6803526421829/50000000000000 : ℝ)^6315 := by
    have hnat : (1108830163 : ℕ)^8363*50000000000000^6315 ≤ 6803526421829^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108830163 5000000000 6803526421829 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266163807/10000000000 : ℝ)^8363 ≤ (42773321840999/100000000000000 : ℝ)^6315 := by
    have hnat : (5266163807 : ℕ)^8363*100000000000000^6315 ≤ 42773321840999^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266163807 10000000000 42773321840999 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534465373/1000000000 : ℝ), (-1108830163/5000000000 : ℝ), (5266163807/10000000000 : ℝ)] ![(10904906325487/25000000000000 : ℝ), (6803526421829/50000000000000 : ℝ), (42773321840999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534465373/1000000000 : ℝ)|^8363 ≤ (10904906325487/25000000000000 : ℝ)^6315
        have hw : |(534465373/1000000000 : ℝ)|=(534465373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1108830163/5000000000 : ℝ)|^8363 ≤ (6803526421829/50000000000000 : ℝ)^6315
        have hw : |(-1108830163/5000000000 : ℝ)|=(1108830163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266163807/10000000000 : ℝ)|^8363 ≤ (42773321840999/100000000000000 : ℝ)^6315
        have hw : |(5266163807/10000000000 : ℝ)|=(5266163807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s7_2 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672326871/5000000000 : ℝ)*x 0 + (5266163803/10000000000 : ℝ)*x 1 + (-554415079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672326871/5000000000 : ℝ)^8363 ≤ (21809812715823/50000000000000 : ℝ)^6315 := by
    have hnat : (2672326871 : ℕ)^8363*50000000000000^6315 ≤ 21809812715823^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672326871 5000000000 21809812715823 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266163803/10000000000 : ℝ)^8363 ≤ (42773321797973/100000000000000 : ℝ)^6315 := by
    have hnat : (5266163803 : ℕ)^8363*100000000000000^6315 ≤ 42773321797973^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266163803 10000000000 42773321797973 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554415079/2500000000 : ℝ)^8363 ≤ (13607052762401/100000000000000 : ℝ)^6315 := by
    have hnat : (554415079 : ℕ)^8363*100000000000000^6315 ≤ 13607052762401^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554415079 2500000000 13607052762401 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672326871/5000000000 : ℝ), (5266163803/10000000000 : ℝ), (-554415079/2500000000 : ℝ)] ![(21809812715823/50000000000000 : ℝ), (42773321797973/100000000000000 : ℝ), (13607052762401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672326871/5000000000 : ℝ)|^8363 ≤ (21809812715823/50000000000000 : ℝ)^6315
        have hw : |(2672326871/5000000000 : ℝ)|=(2672326871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266163803/10000000000 : ℝ)|^8363 ≤ (42773321797973/100000000000000 : ℝ)^6315
        have hw : |(5266163803/10000000000 : ℝ)|=(5266163803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554415079/2500000000 : ℝ)|^8363 ≤ (13607052762401/100000000000000 : ℝ)^6315
        have hw : |(-554415079/2500000000 : ℝ)|=(554415079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s7_3 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360742531/10000000000 : ℝ)*x 0 + (1059036773/2500000000 : ℝ)*x 1 + (4488960357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360742531/10000000000 : ℝ)^8363 ≤ (33317108345339/100000000000000 : ℝ)^6315 := by
    have hnat : (4360742531 : ℕ)^8363*100000000000000^6315 ≤ 33317108345339^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360742531 10000000000 33317108345339 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059036773/2500000000 : ℝ)^8363 ≤ (16031163887647/50000000000000 : ℝ)^6315 := by
    have hnat : (1059036773 : ℕ)^8363*50000000000000^6315 ≤ 16031163887647^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059036773 2500000000 16031163887647 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488960357/10000000000 : ℝ)^8363 ≤ (6924112773613/20000000000000 : ℝ)^6315 := by
    have hnat : (4488960357 : ℕ)^8363*20000000000000^6315 ≤ 6924112773613^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488960357 10000000000 6924112773613 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360742531/10000000000 : ℝ), (1059036773/2500000000 : ℝ), (4488960357/10000000000 : ℝ)] ![(33317108345339/100000000000000 : ℝ), (16031163887647/50000000000000 : ℝ), (6924112773613/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360742531/10000000000 : ℝ)|^8363 ≤ (33317108345339/100000000000000 : ℝ)^6315
        have hw : |(4360742531/10000000000 : ℝ)|=(4360742531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059036773/2500000000 : ℝ)|^8363 ≤ (16031163887647/50000000000000 : ℝ)^6315
        have hw : |(1059036773/2500000000 : ℝ)|=(1059036773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488960357/10000000000 : ℝ)|^8363 ≤ (6924112773613/20000000000000 : ℝ)^6315
        have hw : |(4488960357/10000000000 : ℝ)|=(4488960357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s7_4 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076784619/5000000000 : ℝ)*x 0 + (2633240867/5000000000 : ℝ)*x 1 + (5392225669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076784619/5000000000 : ℝ)^8363 ≤ (13088728099009/100000000000000 : ℝ)^6315 := by
    have hnat : (1076784619 : ℕ)^8363*100000000000000^6315 ≤ 13088728099009^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076784619 5000000000 13088728099009 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633240867/5000000000 : ℝ)^8363 ≤ (21388370813857/50000000000000 : ℝ)^6315 := by
    have hnat : (2633240867 : ℕ)^8363*50000000000000^6315 ≤ 21388370813857^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633240867 5000000000 21388370813857 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392225669/10000000000 : ℝ)^8363 ≤ (22067265127513/50000000000000 : ℝ)^6315 := by
    have hnat : (5392225669 : ℕ)^8363*50000000000000^6315 ≤ 22067265127513^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392225669 10000000000 22067265127513 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076784619/5000000000 : ℝ), (2633240867/5000000000 : ℝ), (5392225669/10000000000 : ℝ)] ![(13088728099009/100000000000000 : ℝ), (21388370813857/50000000000000 : ℝ), (22067265127513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076784619/5000000000 : ℝ)|^8363 ≤ (13088728099009/100000000000000 : ℝ)^6315
        have hw : |(-1076784619/5000000000 : ℝ)|=(1076784619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633240867/5000000000 : ℝ)|^8363 ≤ (21388370813857/50000000000000 : ℝ)^6315
        have hw : |(2633240867/5000000000 : ℝ)|=(2633240867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392225669/10000000000 : ℝ)|^8363 ≤ (22067265127513/50000000000000 : ℝ)^6315
        have hw : |(5392225669/10000000000 : ℝ)|=(5392225669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s7_5 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312568823/10000000000 : ℝ)*x 0 + (-261449807/1250000000 : ℝ)*x 1 + (5392225669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312568823/10000000000 : ℝ)^8363 ≤ (21636592524837/50000000000000 : ℝ)^6315 := by
    have hnat : (5312568823 : ℕ)^8363*50000000000000^6315 ≤ 21636592524837^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312568823 10000000000 21636592524837 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261449807/1250000000 : ℝ)^8363 ≤ (1574035584619/12500000000000 : ℝ)^6315 := by
    have hnat : (261449807 : ℕ)^8363*12500000000000^6315 ≤ 1574035584619^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261449807 1250000000 1574035584619 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392225669/10000000000 : ℝ)^8363 ≤ (22067265127513/50000000000000 : ℝ)^6315 := by
    have hnat : (5392225669 : ℕ)^8363*50000000000000^6315 ≤ 22067265127513^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392225669 10000000000 22067265127513 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312568823/10000000000 : ℝ), (-261449807/1250000000 : ℝ), (5392225669/10000000000 : ℝ)] ![(21636592524837/50000000000000 : ℝ), (1574035584619/12500000000000 : ℝ), (22067265127513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312568823/10000000000 : ℝ)|^8363 ≤ (21636592524837/50000000000000 : ℝ)^6315
        have hw : |(5312568823/10000000000 : ℝ)|=(5312568823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261449807/1250000000 : ℝ)|^8363 ≤ (1574035584619/12500000000000 : ℝ)^6315
        have hw : |(-261449807/1250000000 : ℝ)|=(261449807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392225669/10000000000 : ℝ)|^8363 ≤ (22067265127513/50000000000000 : ℝ)^6315
        have hw : |(5392225669/10000000000 : ℝ)|=(5392225669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s7_6 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312568823/10000000000 : ℝ)*x 0 + (5392225669/10000000000 : ℝ)*x 1 + (-261449807/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312568823/10000000000 : ℝ)^8363 ≤ (21636592524837/50000000000000 : ℝ)^6315 := by
    have hnat : (5312568823 : ℕ)^8363*50000000000000^6315 ≤ 21636592524837^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312568823 10000000000 21636592524837 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392225669/10000000000 : ℝ)^8363 ≤ (22067265127513/50000000000000 : ℝ)^6315 := by
    have hnat : (5392225669 : ℕ)^8363*50000000000000^6315 ≤ 22067265127513^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392225669 10000000000 22067265127513 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261449807/1250000000 : ℝ)^8363 ≤ (1574035584619/12500000000000 : ℝ)^6315 := by
    have hnat : (261449807 : ℕ)^8363*12500000000000^6315 ≤ 1574035584619^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261449807 1250000000 1574035584619 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312568823/10000000000 : ℝ), (5392225669/10000000000 : ℝ), (-261449807/1250000000 : ℝ)] ![(21636592524837/50000000000000 : ℝ), (22067265127513/50000000000000 : ℝ), (1574035584619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312568823/10000000000 : ℝ)|^8363 ≤ (21636592524837/50000000000000 : ℝ)^6315
        have hw : |(5312568823/10000000000 : ℝ)|=(5312568823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392225669/10000000000 : ℝ)|^8363 ≤ (22067265127513/50000000000000 : ℝ)^6315
        have hw : |(5392225669/10000000000 : ℝ)|=(5392225669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261449807/1250000000 : ℝ)|^8363 ≤ (1574035584619/12500000000000 : ℝ)^6315
        have hw : |(-261449807/1250000000 : ℝ)|=(261449807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s7_7 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360752151/10000000000 : ℝ)*x 0 + (280520273/625000000 : ℝ)*x 1 + (16549943/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360752151/10000000000 : ℝ)^8363 ≤ (33317205680741/100000000000000 : ℝ)^6315 := by
    have hnat : (4360752151 : ℕ)^8363*100000000000000^6315 ≤ 33317205680741^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360752151 10000000000 33317205680741 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280520273/625000000 : ℝ)^8363 ≤ (34614068306023/100000000000000 : ℝ)^6315 := by
    have hnat : (280520273 : ℕ)^8363*100000000000000^6315 ≤ 34614068306023^6315*625000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280520273 625000000 34614068306023 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16549943/39062500 : ℝ)^8363 ≤ (32068725994297/100000000000000 : ℝ)^6315 := by
    have hnat : (16549943 : ℕ)^8363*100000000000000^6315 ≤ 32068725994297^6315*39062500^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16549943 39062500 32068725994297 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360752151/10000000000 : ℝ), (280520273/625000000 : ℝ), (16549943/39062500 : ℝ)] ![(33317205680741/100000000000000 : ℝ), (34614068306023/100000000000000 : ℝ), (32068725994297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360752151/10000000000 : ℝ)|^8363 ≤ (33317205680741/100000000000000 : ℝ)^6315
        have hw : |(4360752151/10000000000 : ℝ)|=(4360752151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280520273/625000000 : ℝ)|^8363 ≤ (34614068306023/100000000000000 : ℝ)^6315
        have hw : |(280520273/625000000 : ℝ)|=(280520273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16549943/39062500 : ℝ)|^8363 ≤ (32068725994297/100000000000000 : ℝ)^6315
        have hw : |(16549943/39062500 : ℝ)|=(16549943/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1170_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7033/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11383/100000 : ℝ) ^ (4181/1024 : ℝ) ≤ (1752261393374811/12500000000000000000 : ℝ) := by
    have hpowers : (11383/100000 : ℝ)^4181 ≤ (1752261393374811/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11383 : ℕ)^4181*12500000000000000000^1024 ≤ 1752261393374811^1024*100000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11383 100000 1752261393374811 12500000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11383/100000 : ℝ)) (X := (1752261393374811/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1759/12500 : ℝ) ^ (4181/1024 : ℝ) ≤ (16660966465623433/50000000000000000000 : ℝ) := by
    have hpowers : (1759/12500 : ℝ)^4181 ≤ (16660966465623433/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1759 : ℕ)^4181*50000000000000000000^1024 ≤ 16660966465623433^1024*12500^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1759 12500 16660966465623433 50000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1759/12500 : ℝ)) (X := (16660966465623433/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251752261393374811/6250000000000000000 : ℝ) ≤ (10000686582453177/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (6251752261393374811/6250000000000000000 : ℝ)^1024 ≤ (10000686582453177/10000000000000000 : ℝ)^4181 := by
      have hnat : (6251752261393374811 : ℕ)^1024*10000000000000000^4181 ≤ 10000686582453177^4181*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251752261393374811 6250000000000000000 10000686582453177 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000686582453177/10000000000000000 : ℝ)) (X := (6251752261393374811/6250000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023670012039122677/50000000000000000000 : ℝ) ≤ (10001159232791137/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (50023670012039122677/50000000000000000000 : ℝ)^1024 ≤ (10001159232791137/10000000000000000 : ℝ)^4181 := by
      have hnat : (50023670012039122677 : ℕ)^1024*10000000000000000^4181 ≤ 10001159232791137^4181*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023670012039122677 50000000000000000000 10001159232791137 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001159232791137/10000000000000000 : ℝ)) (X := (50023670012039122677/50000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016660966465623433/25000000000000000000 : ℝ) ≤ (10001631883129097/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (25016660966465623433/25000000000000000000 : ℝ)^1024 ≤ (10001631883129097/10000000000000000 : ℝ)^4181 := by
      have hnat : (25016660966465623433 : ℕ)^1024*10000000000000000^4181 ≤ 10001631883129097^4181*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016660966465623433 25000000000000000000 10001631883129097 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001631883129097/10000000000000000 : ℝ)) (X := (25016660966465623433/25000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1752261393374811/12500000000000000000 : ℝ) ≤ ((26881085862622595593/26890000000000000000 : ℝ)+2*(11816258449/6722500000000 : ℝ)*(11383/100000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (26881085862622595593/26890000000000000000 : ℝ)+2*(11816258449/6722500000000 : ℝ)*(11383/100000 : ℝ)=(10000686582453177/10000000000000000 : ℝ) by norm_num, show 1+2*(1752261393374811/12500000000000000000 : ℝ)=(6251752261393374811/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16660966465623433/50000000000000000000 : ℝ)+(1752261393374811/12500000000000000000 : ℝ) ≤ ((26881085862622595593/26890000000000000000 : ℝ)+(11816258449/6722500000000 : ℝ)*((1759/12500 : ℝ)+(11383/100000 : ℝ)))^(4181/1024 : ℝ) := by
    rw [show (26881085862622595593/26890000000000000000 : ℝ)+(11816258449/6722500000000 : ℝ)*((1759/12500 : ℝ)+(11383/100000 : ℝ))=(10001159232791137/10000000000000000 : ℝ) by norm_num, show 1+(16660966465623433/50000000000000000000 : ℝ)+(1752261393374811/12500000000000000000 : ℝ)=(50023670012039122677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16660966465623433/50000000000000000000 : ℝ) ≤ ((26881085862622595593/26890000000000000000 : ℝ)+2*(11816258449/6722500000000 : ℝ)*(1759/12500 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (26881085862622595593/26890000000000000000 : ℝ)+2*(11816258449/6722500000000 : ℝ)*(1759/12500 : ℝ)=(10001631883129097/10000000000000000 : ℝ) by norm_num, show 1+2*(16660966465623433/50000000000000000000 : ℝ)=(25016660966465623433/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26881085862622595593/26890000000000000000 : ℝ)*(X 1 0+X 2 0)+(11816258449/6722500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (26881085862622595593/26890000000000000000 : ℝ)) (alpha := (11816258449/6722500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26881085862622595593/26890000000000000000 : ℝ)*(X 0 1+X 2 1)+(11816258449/6722500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (26881085862622595593/26890000000000000000 : ℝ)) (alpha := (11816258449/6722500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26881085862622595593/26890000000000000000 : ℝ)*(X 0 2+X 1 2)+(11816258449/6722500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (26881085862622595593/26890000000000000000 : ℝ)) (alpha := (11816258449/6722500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1076782207/5000000000 : ℝ)*X 0 0+(539254477/1000000000 : ℝ)*X 0 1+(1053232757/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534465373/1000000000 : ℝ)*X 1 0+(-1108830163/5000000000 : ℝ)*X 1 1+(5266163807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672326871/5000000000 : ℝ)*X 2 0+(5266163803/10000000000 : ℝ)*X 2 1+(-554415079/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360742531/10000000000 : ℝ)*X 0 0+(1059036773/2500000000 : ℝ)*X 0 1+(4488960357/10000000000 : ℝ)*X 0 2+(4360742531/10000000000 : ℝ)*X 1 0+(1059036773/2500000000 : ℝ)*X 1 1+(4488960357/10000000000 : ℝ)*X 1 2+(4360742531/10000000000 : ℝ)*X 2 0+(1059036773/2500000000 : ℝ)*X 2 1+(4488960357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1076784619/5000000000 : ℝ)*X 0 0+(2633240867/5000000000 : ℝ)*X 0 1+(5392225669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312568823/10000000000 : ℝ)*X 1 0+(-261449807/1250000000 : ℝ)*X 1 1+(5392225669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312568823/10000000000 : ℝ)*X 2 0+(5392225669/10000000000 : ℝ)*X 2 1+(-261449807/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360752151/10000000000 : ℝ)*X 0 0+(280520273/625000000 : ℝ)*X 0 1+(16549943/39062500 : ℝ)*X 0 2+(4360752151/10000000000 : ℝ)*X 1 0+(280520273/625000000 : ℝ)*X 1 1+(16549943/39062500 : ℝ)*X 1 2+(4360752151/10000000000 : ℝ)*X 2 0+(280520273/625000000 : ℝ)*X 2 1+(16549943/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2461965197251358323372976211/672250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185028203/25000000000000 : ℝ)*(base19) + (685178149/100000000000000 : ℝ)*(base23) + (1554233/4000000000000 : ℝ)*(lower2) + (19137497/20000000000000 : ℝ)*(upper3) + (61918193/100000000000000 : ℝ)*(upper5) + (2967033963939603/50000000000000 : ℝ)*(major0) + (2967033963939603/50000000000000 : ℝ)*(major1) + (2967033963939603/50000000000000 : ℝ)*(major2) + (3956302286709517/50000000000000 : ℝ)*(sp0) + (989078177020501/12500000000000 : ℝ)*(sp1) + (791262547109867/10000000000000 : ℝ)*(sp2) + (988874625455417/25000000000000 : ℝ)*(sp3) + (2697857223/12500000000000 : ℝ)*(sp4) + (11075584037/100000000000000 : ℝ)*(sp7) + (494438697175713/12500000000000 : ℝ)*(f.failure) + (7912626156276819/100000000000000 : ℝ)*(f.sum) + (8628228624051/2689000000000000000000000000 : ℝ)*base66 + (7882709029172030421/1344500000000000000000000000000000 : ℝ)*base68 + (8354650108397030421/1344500000000000000000000000000000 : ℝ)*base70 + (13296812117273530421/1344500000000000000000000000000000 : ℝ)*base72 + (29476069063/5251953125000000000000000 : ℝ)*base73 + (59397136877912030421/1344500000000000000000000000000000 : ℝ)*base76 + (15740808319123530421/1344500000000000000000000000000000 : ℝ)*base78 + (33192346586015030421/1344500000000000000000000000000000 : ℝ)*base80 + (1972522665519/672250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (78081/250000000000000000000 : ℝ)*base90 + (78081/250000000000000000000 : ℝ)*base92 + (78081/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5480124588270100292680179957/672250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1482388291/100000000000000 : ℝ)*(base19) + (322517889/20000000000000 : ℝ)*(base23) + (16367051/10000000000000 : ℝ)*(upper3) + (3702357/6250000000000 : ℝ)*(lower4) + (83251503/50000000000000 : ℝ)*(upper5) + (2982048845641217/50000000000000 : ℝ)*(major0) + (2982048845641217/50000000000000 : ℝ)*(major1) + (2982048845641217/50000000000000 : ℝ)*(major2) + (41200451531/100000000000000 : ℝ)*(sp1) + (885922833/2000000000000 : ℝ)*(sp2) + (3976334201073331/50000000000000 : ℝ)*(sp4) + (198815642982671/2500000000000 : ℝ)*(sp5) + (497038905838473/6250000000000 : ℝ)*(sp6) + (397552670868771/10000000000000 : ℝ)*(sp7) + (397552670868771/10000000000000 : ℝ)*(f.failure) + (3976334201073331/50000000000000 : ℝ)*(f.sum) + (467919250161/1344500000000000000000000000 : ℝ)*base65 + (12998164719429356681/1344500000000000000000000000000000 : ℝ)*base67 + (21889056343464356681/1344500000000000000000000000000000 : ℝ)*base69 + (8154295775424643319/1344500000000000000000000000000000 : ℝ)*base72 + (1470864513801/1344500000000000000000000000 : ℝ)*base73 + (47964090896608856681/1344500000000000000000000000000000 : ℝ)*base75 + (1399770879847643319/1344500000000000000000000000000000 : ℝ)*base78 + (3274151782716356681/1344500000000000000000000000000000 : ℝ)*base79 + (163235349213/67225000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1816573/200000000000000000000 : ℝ)*base89 + (1816573/200000000000000000000 : ℝ)*base91 + (1816573/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1170_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1170_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1170_s8_0 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076784321/5000000000 : ℝ)*x 0 + (5392485947/10000000000 : ℝ)*x 1 + (5266219899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076784321/5000000000 : ℝ)^8363 ≤ (6544361650983/50000000000000 : ℝ)^6315 := by
    have hnat : (1076784321 : ℕ)^8363*50000000000000^6315 ≤ 6544361650983^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076784321 5000000000 6544361650983 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392485947/10000000000 : ℝ)^8363 ≤ (8827470299029/20000000000000 : ℝ)^6315 := by
    have hnat : (5392485947 : ℕ)^8363*20000000000000^6315 ≤ 8827470299029^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392485947 10000000000 8827470299029 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266219899/10000000000 : ℝ)^8363 ≤ (10693481297651/25000000000000 : ℝ)^6315 := by
    have hnat : (5266219899 : ℕ)^8363*25000000000000^6315 ≤ 10693481297651^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266219899 10000000000 10693481297651 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076784321/5000000000 : ℝ), (5392485947/10000000000 : ℝ), (5266219899/10000000000 : ℝ)] ![(6544361650983/50000000000000 : ℝ), (8827470299029/20000000000000 : ℝ), (10693481297651/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076784321/5000000000 : ℝ)|^8363 ≤ (6544361650983/50000000000000 : ℝ)^6315
        have hw : |(-1076784321/5000000000 : ℝ)|=(1076784321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392485947/10000000000 : ℝ)|^8363 ≤ (8827470299029/20000000000000 : ℝ)^6315
        have hw : |(5392485947/10000000000 : ℝ)|=(5392485947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266219899/10000000000 : ℝ)|^8363 ≤ (10693481297651/25000000000000 : ℝ)^6315
        have hw : |(5266219899/10000000000 : ℝ)|=(5266219899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s8_1 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534463917/1000000000 : ℝ)*x 0 + (-277200683/1250000000 : ℝ)*x 1 + (5266219881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534463917/1000000000 : ℝ)^8363 ≤ (872389358709/2000000000000 : ℝ)^6315 := by
    have hnat : (534463917 : ℕ)^8363*2000000000000^6315 ≤ 872389358709^6315*1000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534463917 1000000000 872389358709 2000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277200683/1250000000 : ℝ)^8363 ≤ (1360660705637/10000000000000 : ℝ)^6315 := by
    have hnat : (277200683 : ℕ)^8363*10000000000000^6315 ≤ 1360660705637^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277200683 1250000000 1360660705637 10000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266219881/10000000000 : ℝ)^8363 ≤ (10693481249247/25000000000000 : ℝ)^6315 := by
    have hnat : (5266219881 : ℕ)^8363*25000000000000^6315 ≤ 10693481249247^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266219881 10000000000 10693481249247 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534463917/1000000000 : ℝ), (-277200683/1250000000 : ℝ), (5266219881/10000000000 : ℝ)] ![(872389358709/2000000000000 : ℝ), (1360660705637/10000000000000 : ℝ), (10693481249247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534463917/1000000000 : ℝ)|^8363 ≤ (872389358709/2000000000000 : ℝ)^6315
        have hw : |(534463917/1000000000 : ℝ)|=(534463917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277200683/1250000000 : ℝ)|^8363 ≤ (1360660705637/10000000000000 : ℝ)^6315
        have hw : |(-277200683/1250000000 : ℝ)|=(277200683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266219881/10000000000 : ℝ)|^8363 ≤ (10693481249247/25000000000000 : ℝ)^6315
        have hw : |(5266219881/10000000000 : ℝ)|=(5266219881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s8_2 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672319579/5000000000 : ℝ)*x 0 + (5266219891/10000000000 : ℝ)*x 1 + (-2217605467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672319579/5000000000 : ℝ)^8363 ≤ (5452433475719/12500000000000 : ℝ)^6315 := by
    have hnat : (2672319579 : ℕ)^8363*12500000000000^6315 ≤ 5452433475719^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672319579 5000000000 5452433475719 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266219891/10000000000 : ℝ)^8363 ≤ (5346740638069/12500000000000 : ℝ)^6315 := by
    have hnat : (5266219891 : ℕ)^8363*12500000000000^6315 ≤ 5346740638069^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266219891 10000000000 5346740638069 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217605467/10000000000 : ℝ)^8363 ≤ (13606607080747/100000000000000 : ℝ)^6315 := by
    have hnat : (2217605467 : ℕ)^8363*100000000000000^6315 ≤ 13606607080747^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217605467 10000000000 13606607080747 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672319579/5000000000 : ℝ), (5266219891/10000000000 : ℝ), (-2217605467/10000000000 : ℝ)] ![(5452433475719/12500000000000 : ℝ), (5346740638069/12500000000000 : ℝ), (13606607080747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672319579/5000000000 : ℝ)|^8363 ≤ (5452433475719/12500000000000 : ℝ)^6315
        have hw : |(2672319579/5000000000 : ℝ)|=(2672319579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266219891/10000000000 : ℝ)|^8363 ≤ (5346740638069/12500000000000 : ℝ)^6315
        have hw : |(5266219891/10000000000 : ℝ)|=(5266219891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2217605467/10000000000 : ℝ)|^8363 ≤ (13606607080747/100000000000000 : ℝ)^6315
        have hw : |(-2217605467/10000000000 : ℝ)|=(2217605467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s8_3 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360745409/10000000000 : ℝ)*x 0 + (1059065411/2500000000 : ℝ)*x 1 + (897769017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360745409/10000000000 : ℝ)^8363 ≤ (2082321091563/6250000000000 : ℝ)^6315 := by
    have hnat : (4360745409 : ℕ)^8363*6250000000000^6315 ≤ 2082321091563^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360745409 10000000000 2082321091563 6250000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059065411/2500000000 : ℝ)^8363 ≤ (32063475974759/100000000000000 : ℝ)^6315 := by
    have hnat : (1059065411 : ℕ)^8363*100000000000000^6315 ≤ 32063475974759^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059065411 2500000000 32063475974759 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897769017/2000000000 : ℝ)^8363 ≤ (4327423316947/12500000000000 : ℝ)^6315 := by
    have hnat : (897769017 : ℕ)^8363*12500000000000^6315 ≤ 4327423316947^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897769017 2000000000 4327423316947 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360745409/10000000000 : ℝ), (1059065411/2500000000 : ℝ), (897769017/2000000000 : ℝ)] ![(2082321091563/6250000000000 : ℝ), (32063475974759/100000000000000 : ℝ), (4327423316947/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360745409/10000000000 : ℝ)|^8363 ≤ (2082321091563/6250000000000 : ℝ)^6315
        have hw : |(4360745409/10000000000 : ℝ)|=(4360745409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059065411/2500000000 : ℝ)|^8363 ≤ (32063475974759/100000000000000 : ℝ)^6315
        have hw : |(1059065411/2500000000 : ℝ)|=(1059065411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897769017/2000000000 : ℝ)|^8363 ≤ (4327423316947/12500000000000 : ℝ)^6315
        have hw : |(897769017/2000000000 : ℝ)|=(897769017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s8_4 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153573507/10000000000 : ℝ)*x 0 + (2633268723/5000000000 : ℝ)*x 1 + (1348041803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153573507/10000000000 : ℝ)^8363 ≤ (13088762459047/100000000000000 : ℝ)^6315 := by
    have hnat : (2153573507 : ℕ)^8363*100000000000000^6315 ≤ 13088762459047^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153573507 10000000000 13088762459047 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633268723/5000000000 : ℝ)^8363 ≤ (21388670450801/50000000000000 : ℝ)^6315 := by
    have hnat : (2633268723 : ℕ)^8363*50000000000000^6315 ≤ 21388670450801^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633268723 5000000000 21388670450801 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348041803/2500000000 : ℝ)^8363 ≤ (11033474156541/25000000000000 : ℝ)^6315 := by
    have hnat : (1348041803 : ℕ)^8363*25000000000000^6315 ≤ 11033474156541^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348041803 2500000000 11033474156541 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153573507/10000000000 : ℝ), (2633268723/5000000000 : ℝ), (1348041803/2500000000 : ℝ)] ![(13088762459047/100000000000000 : ℝ), (21388670450801/50000000000000 : ℝ), (11033474156541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153573507/10000000000 : ℝ)|^8363 ≤ (13088762459047/100000000000000 : ℝ)^6315
        have hw : |(-2153573507/10000000000 : ℝ)|=(2153573507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633268723/5000000000 : ℝ)|^8363 ≤ (21388670450801/50000000000000 : ℝ)^6315
        have hw : |(2633268723/5000000000 : ℝ)|=(2633268723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348041803/2500000000 : ℝ)|^8363 ≤ (11033474156541/25000000000000 : ℝ)^6315
        have hw : |(1348041803/2500000000 : ℝ)|=(1348041803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s8_5 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328145881/2500000000 : ℝ)*x 0 + (-2091657727/10000000000 : ℝ)*x 1 + (2696083721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328145881/2500000000 : ℝ)^8363 ≤ (43273343630293/100000000000000 : ℝ)^6315 := by
    have hnat : (1328145881 : ℕ)^8363*100000000000000^6315 ≤ 43273343630293^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328145881 2500000000 43273343630293 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091657727/10000000000 : ℝ)^8363 ≤ (6296378619703/50000000000000 : ℝ)^6315 := by
    have hnat : (2091657727 : ℕ)^8363*50000000000000^6315 ≤ 6296378619703^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091657727 10000000000 6296378619703 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696083721/5000000000 : ℝ)^8363 ≤ (44133899119183/100000000000000 : ℝ)^6315 := by
    have hnat : (2696083721 : ℕ)^8363*100000000000000^6315 ≤ 44133899119183^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696083721 5000000000 44133899119183 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328145881/2500000000 : ℝ), (-2091657727/10000000000 : ℝ), (2696083721/5000000000 : ℝ)] ![(43273343630293/100000000000000 : ℝ), (6296378619703/50000000000000 : ℝ), (44133899119183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328145881/2500000000 : ℝ)|^8363 ≤ (43273343630293/100000000000000 : ℝ)^6315
        have hw : |(1328145881/2500000000 : ℝ)|=(1328145881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091657727/10000000000 : ℝ)|^8363 ≤ (6296378619703/50000000000000 : ℝ)^6315
        have hw : |(-2091657727/10000000000 : ℝ)|=(2091657727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696083721/5000000000 : ℝ)|^8363 ≤ (44133899119183/100000000000000 : ℝ)^6315
        have hw : |(2696083721/5000000000 : ℝ)|=(2696083721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s8_6 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062516707/2000000000 : ℝ)*x 0 + (107843347/200000000 : ℝ)*x 1 + (-522914459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062516707/2000000000 : ℝ)^8363 ≤ (865466874979/2000000000000 : ℝ)^6315 := by
    have hnat : (1062516707 : ℕ)^8363*2000000000000^6315 ≤ 865466874979^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062516707 2000000000 865466874979 2000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107843347/200000000 : ℝ)^8363 ≤ (1765355924879/4000000000000 : ℝ)^6315 := by
    have hnat : (107843347 : ℕ)^8363*4000000000000^6315 ≤ 1765355924879^6315*200000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107843347 200000000 1765355924879 4000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522914459/2500000000 : ℝ)^8363 ≤ (12592758108457/100000000000000 : ℝ)^6315 := by
    have hnat : (522914459 : ℕ)^8363*100000000000000^6315 ≤ 12592758108457^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522914459 2500000000 12592758108457 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062516707/2000000000 : ℝ), (107843347/200000000 : ℝ), (-522914459/2500000000 : ℝ)] ![(865466874979/2000000000000 : ℝ), (1765355924879/4000000000000 : ℝ), (12592758108457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062516707/2000000000 : ℝ)|^8363 ≤ (865466874979/2000000000000 : ℝ)^6315
        have hw : |(1062516707/2000000000 : ℝ)|=(1062516707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107843347/200000000 : ℝ)|^8363 ≤ (1765355924879/4000000000000 : ℝ)^6315
        have hw : |(107843347/200000000 : ℝ)|=(107843347/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522914459/2500000000 : ℝ)|^8363 ≤ (12592758108457/100000000000000 : ℝ)^6315
        have hw : |(-522914459/2500000000 : ℝ)|=(522914459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s8_7 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (43607549/100000000 : ℝ)*x 0 + (897642049/2000000000 : ℝ)*x 1 + (423689891/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43607549/100000000 : ℝ)^8363 ≤ (6663446699041/20000000000000 : ℝ)^6315 := by
    have hnat : (43607549 : ℕ)^8363*20000000000000^6315 ≤ 6663446699041^6315*100000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43607549 100000000 6663446699041 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897642049/2000000000 : ℝ)^8363 ≤ (4326612845297/12500000000000 : ℝ)^6315 := by
    have hnat : (897642049 : ℕ)^8363*12500000000000^6315 ≤ 4326612845297^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897642049 2000000000 4326612845297 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423689891/1000000000 : ℝ)^8363 ≤ (8017465931187/25000000000000 : ℝ)^6315 := by
    have hnat : (423689891 : ℕ)^8363*25000000000000^6315 ≤ 8017465931187^6315*1000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423689891 1000000000 8017465931187 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43607549/100000000 : ℝ), (897642049/2000000000 : ℝ), (423689891/1000000000 : ℝ)] ![(6663446699041/20000000000000 : ℝ), (4326612845297/12500000000000 : ℝ), (8017465931187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43607549/100000000 : ℝ)|^8363 ≤ (6663446699041/20000000000000 : ℝ)^6315
        have hw : |(43607549/100000000 : ℝ)|=(43607549/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897642049/2000000000 : ℝ)|^8363 ≤ (4326612845297/12500000000000 : ℝ)^6315
        have hw : |(897642049/2000000000 : ℝ)|=(897642049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423689891/1000000000 : ℝ)|^8363 ≤ (8017465931187/25000000000000 : ℝ)^6315
        have hw : |(423689891/1000000000 : ℝ)|=(423689891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1170_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1139/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2813/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11389/100000 : ℝ) ^ (4181/1024 : ℝ) ≤ (7024142428092547/50000000000000000000 : ℝ) := by
    have hpowers : (11389/100000 : ℝ)^4181 ≤ (7024142428092547/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11389 : ℕ)^4181*50000000000000000000^1024 ≤ 7024142428092547^1024*100000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11389 100000 7024142428092547 50000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11389/100000 : ℝ)) (X := (7024142428092547/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7033/50000 : ℝ) ^ (4181/1024 : ℝ) ≤ (16631980326686579/50000000000000000000 : ℝ) := by
    have hpowers : (7033/50000 : ℝ)^4181 ≤ (16631980326686579/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7033 : ℕ)^4181*50000000000000000000^1024 ≤ 16631980326686579^1024*50000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7033 50000 16631980326686579 50000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7033/50000 : ℝ)) (X := (16631980326686579/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007024142428092547/25000000000000000000 : ℝ) ≤ (2500172015283319/2500000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (25007024142428092547/25000000000000000000 : ℝ)^1024 ≤ (2500172015283319/2500000000000000 : ℝ)^4181 := by
      have hnat : (25007024142428092547 : ℕ)^1024*2500000000000000^4181 ≤ 2500172015283319^4181*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007024142428092547 25000000000000000000 2500172015283319 2500000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500172015283319/2500000000000000 : ℝ)) (X := (25007024142428092547/25000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011828061377389563/25000000000000000000 : ℝ) ≤ (10001158552688443/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (25011828061377389563/25000000000000000000 : ℝ)^1024 ≤ (10001158552688443/10000000000000000 : ℝ)^4181 := by
      have hnat : (25011828061377389563 : ℕ)^1024*10000000000000000^4181 ≤ 10001158552688443^4181*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011828061377389563 25000000000000000000 10001158552688443 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001158552688443/10000000000000000 : ℝ)) (X := (25011828061377389563/25000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016631980326686579/25000000000000000000 : ℝ) ≤ (1000162904424361/1000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (25016631980326686579/25000000000000000000 : ℝ)^1024 ≤ (1000162904424361/1000000000000000 : ℝ)^4181 := by
      have hnat : (25016631980326686579 : ℕ)^1024*1000000000000000^4181 ≤ 1000162904424361^4181*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016631980326686579 25000000000000000000 1000162904424361 1000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000162904424361/1000000000000000 : ℝ)) (X := (25016631980326686579/25000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7024142428092547/50000000000000000000 : ℝ) ≤ ((13380562541505092963/13385000000000000000 : ℝ)+2*(470491555167/267700000000000 : ℝ)*(11389/100000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (13380562541505092963/13385000000000000000 : ℝ)+2*(470491555167/267700000000000 : ℝ)*(11389/100000 : ℝ)=(2500172015283319/2500000000000000 : ℝ) by norm_num, show 1+2*(7024142428092547/50000000000000000000 : ℝ)=(25007024142428092547/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16631980326686579/50000000000000000000 : ℝ)+(7024142428092547/50000000000000000000 : ℝ) ≤ ((13380562541505092963/13385000000000000000 : ℝ)+(470491555167/267700000000000 : ℝ)*((7033/50000 : ℝ)+(11389/100000 : ℝ)))^(4181/1024 : ℝ) := by
    rw [show (13380562541505092963/13385000000000000000 : ℝ)+(470491555167/267700000000000 : ℝ)*((7033/50000 : ℝ)+(11389/100000 : ℝ))=(10001158552688443/10000000000000000 : ℝ) by norm_num, show 1+(16631980326686579/50000000000000000000 : ℝ)+(7024142428092547/50000000000000000000 : ℝ)=(25011828061377389563/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16631980326686579/50000000000000000000 : ℝ) ≤ ((13380562541505092963/13385000000000000000 : ℝ)+2*(470491555167/267700000000000 : ℝ)*(7033/50000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (13380562541505092963/13385000000000000000 : ℝ)+2*(470491555167/267700000000000 : ℝ)*(7033/50000 : ℝ)=(1000162904424361/1000000000000000 : ℝ) by norm_num, show 1+2*(16631980326686579/50000000000000000000 : ℝ)=(25016631980326686579/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13380562541505092963/13385000000000000000 : ℝ)*(X 1 0+X 2 0)+(470491555167/267700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (13380562541505092963/13385000000000000000 : ℝ)) (alpha := (470491555167/267700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13380562541505092963/13385000000000000000 : ℝ)*(X 0 1+X 2 1)+(470491555167/267700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (13380562541505092963/13385000000000000000 : ℝ)) (alpha := (470491555167/267700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13380562541505092963/13385000000000000000 : ℝ)*(X 0 2+X 1 2)+(470491555167/267700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (13380562541505092963/13385000000000000000 : ℝ)) (alpha := (470491555167/267700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1076784321/5000000000 : ℝ)*X 0 0+(5392485947/10000000000 : ℝ)*X 0 1+(5266219899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534463917/1000000000 : ℝ)*X 1 0+(-277200683/1250000000 : ℝ)*X 1 1+(5266219881/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672319579/5000000000 : ℝ)*X 2 0+(5266219891/10000000000 : ℝ)*X 2 1+(-2217605467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360745409/10000000000 : ℝ)*X 0 0+(1059065411/2500000000 : ℝ)*X 0 1+(897769017/2000000000 : ℝ)*X 0 2+(4360745409/10000000000 : ℝ)*X 1 0+(1059065411/2500000000 : ℝ)*X 1 1+(897769017/2000000000 : ℝ)*X 1 2+(4360745409/10000000000 : ℝ)*X 2 0+(1059065411/2500000000 : ℝ)*X 2 1+(897769017/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2153573507/10000000000 : ℝ)*X 0 0+(2633268723/5000000000 : ℝ)*X 0 1+(1348041803/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328145881/2500000000 : ℝ)*X 1 0+(-2091657727/10000000000 : ℝ)*X 1 1+(2696083721/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062516707/2000000000 : ℝ)*X 2 0+(107843347/200000000 : ℝ)*X 2 1+(-522914459/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43607549/100000000 : ℝ)*X 0 0+(897642049/2000000000 : ℝ)*X 0 1+(423689891/1000000000 : ℝ)*X 0 2+(43607549/100000000 : ℝ)*X 1 0+(897642049/2000000000 : ℝ)*X 1 1+(423689891/1000000000 : ℝ)*X 1 2+(43607549/100000000 : ℝ)*X 2 0+(897642049/2000000000 : ℝ)*X 2 1+(423689891/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1850448428651346606677368107/334625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109350311/10000000000000 : ℝ)*(base19) + (199926379/20000000000000 : ℝ)*(base23) + (10166741/25000000000000 : ℝ)*(lower2) + (70172857/50000000000000 : ℝ)*(upper3) + (38126141/50000000000000 : ℝ)*(upper5) + (5939481786282963/100000000000000 : ℝ)*(major0) + (5939481786282963/100000000000000 : ℝ)*(major1) + (5939481786282963/100000000000000 : ℝ)*(major2) + (7919816235975199/100000000000000 : ℝ)*(sp0) + (989980495891971/12500000000000 : ℝ)*(sp1) + (3959922030503491/50000000000000 : ℝ)*(sp2) + (1979551087195413/50000000000000 : ℝ)*(sp3) + (28824663679/100000000000000 : ℝ)*(sp4) + (323064113/2000000000000 : ℝ)*(sp7) + (1979559163798237/50000000000000 : ℝ)*(f.failure) + (7919845060638877/100000000000000 : ℝ)*(f.sum) + (28736914598017/6692500000000000000000000000 : ℝ)*base66 + (5293418869289360631/1338500000000000000000000000000000 : ℝ)*base68 + (13121227981192360631/1338500000000000000000000000000000 : ℝ)*base70 + (7624043061339860631/1338500000000000000000000000000000 : ℝ)*base72 + (9935908324651/13385000000000000000000000000 : ℝ)*base73 + (3206189859613860631/1338500000000000000000000000000000 : ℝ)*base76 + (5680231327085860631/1338500000000000000000000000000000 : ℝ)*base78 + (13658902326223139369/1338500000000000000000000000000000 : ℝ)*base79 + (140205447317839/13385000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (7763069/1000000000000000000000 : ℝ)*base90 + (7763069/1000000000000000000000 : ℝ)*base92 + (7763069/1000000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123162474760042927999119/13385000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224210571/10000000000000 : ℝ)*(base19) + (234456527/10000000000000 : ℝ)*(base23) + (453010299/50000000000000 : ℝ)*(lower1) + (180371/625000000000 : ℝ)*(upper2) + (15508991/5000000000000 : ℝ)*(upper3) + (22685629/50000000000000 : ℝ)*(upper5) + (5969454418551341/100000000000000 : ℝ)*(major0) + (5969454418551341/100000000000000 : ℝ)*(major1) + (5969454418551341/100000000000000 : ℝ)*(major2) + (524630157/10000000000000 : ℝ)*(sp2) + (3979905576886079/50000000000000 : ℝ)*(sp4) + (497488056979153/6250000000000 : ℝ)*(sp5) + (7959803562905319/100000000000000 : ℝ)*(sp6) + (795819475322571/20000000000000 : ℝ)*(sp7) + (795819475322571/20000000000000 : ℝ)*(f.failure) + (3979905576886079/50000000000000 : ℝ)*(f.sum) + (1115874970257/13385000000000000000000000000 : ℝ)*base65 + (1901671134735163383/1338500000000000000000000000000000 : ℝ)*base67 + (94333336472119663383/1338500000000000000000000000000000 : ℝ)*base69 + (14232493167861336617/1338500000000000000000000000000000 : ℝ)*base72 + (4114660784121/1673125000000000000000000000 : ℝ)*base74 + (5228713950900336617/1338500000000000000000000000000000 : ℝ)*base76 + (10422851754721836617/1338500000000000000000000000000000 : ℝ)*base78 + (1751176817633163383/1338500000000000000000000000000000 : ℝ)*base79 + (241976891598187/13385000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1605973/400000000000000000000 : ℝ)*base89 + (1605973/400000000000000000000 : ℝ)*base91 + (1605973/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1170_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1170_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1170_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1170_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1170_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1170_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1170_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
