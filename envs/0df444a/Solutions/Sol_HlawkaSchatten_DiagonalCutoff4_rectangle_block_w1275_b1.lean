-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1275_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:37.138559+00:00
-- url     : https://prove2.me/submissions/bdb8c674-6a86-4206-a6e6-bb38ff89a29b

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
theorem support_rectangle_w1275_s3_0 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050352093/5000000000 : ℝ)*x 0 + (1359169909/2500000000 : ℝ)*x 1 + (2611744711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050352093/5000000000 : ℝ)^4235 ≤ (99782537629/781250000000 : ℝ)^3211 := by
    have hnat : (1050352093 : ℕ)^4235*781250000000^3211 ≤ 99782537629^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050352093 5000000000 99782537629 781250000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359169909/2500000000 : ℝ)^4235 ≤ (8952836866499/20000000000000 : ℝ)^3211 := by
    have hnat : (1359169909 : ℕ)^4235*20000000000000^3211 ≤ 8952836866499^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359169909 2500000000 8952836866499 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611744711/5000000000 : ℝ)^4235 ≤ (42463650843371/100000000000000 : ℝ)^3211 := by
    have hnat : (2611744711 : ℕ)^4235*100000000000000^3211 ≤ 42463650843371^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611744711 5000000000 42463650843371 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050352093/5000000000 : ℝ), (1359169909/2500000000 : ℝ), (2611744711/5000000000 : ℝ)] ![(99782537629/781250000000 : ℝ), (8952836866499/20000000000000 : ℝ), (42463650843371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050352093/5000000000 : ℝ)|^4235 ≤ (99782537629/781250000000 : ℝ)^3211
        have hw : |(-1050352093/5000000000 : ℝ)|=(1050352093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359169909/2500000000 : ℝ)|^4235 ≤ (8952836866499/20000000000000 : ℝ)^3211
        have hw : |(1359169909/2500000000 : ℝ)|=(1359169909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2611744711/5000000000 : ℝ)|^4235 ≤ (42463650843371/100000000000000 : ℝ)^3211
        have hw : |(2611744711/5000000000 : ℝ)|=(2611744711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s3_1 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355213339/10000000000 : ℝ)*x 0 + (-138116913/625000000 : ℝ)*x 1 + (130587241/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355213339/10000000000 : ℝ)^4235 ≤ (43881621674319/100000000000000 : ℝ)^3211 := by
    have hnat : (5355213339 : ℕ)^4235*100000000000000^3211 ≤ 43881621674319^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355213339 10000000000 43881621674319 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138116913/625000000 : ℝ)^4235 ≤ (13654725128501/100000000000000 : ℝ)^3211 := by
    have hnat : (138116913 : ℕ)^4235*100000000000000^3211 ≤ 13654725128501^3211*625000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138116913 625000000 13654725128501 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130587241/250000000 : ℝ)^4235 ≤ (21231826590367/50000000000000 : ℝ)^3211 := by
    have hnat : (130587241 : ℕ)^4235*50000000000000^3211 ≤ 21231826590367^3211*250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130587241 250000000 21231826590367 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355213339/10000000000 : ℝ), (-138116913/625000000 : ℝ), (130587241/250000000 : ℝ)] ![(43881621674319/100000000000000 : ℝ), (13654725128501/100000000000000 : ℝ), (21231826590367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355213339/10000000000 : ℝ)|^4235 ≤ (43881621674319/100000000000000 : ℝ)^3211
        have hw : |(5355213339/10000000000 : ℝ)|=(5355213339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138116913/625000000 : ℝ)|^4235 ≤ (13654725128501/100000000000000 : ℝ)^3211
        have hw : |(-138116913/625000000 : ℝ)|=(138116913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130587241/250000000 : ℝ)|^4235 ≤ (21231826590367/50000000000000 : ℝ)^3211
        have hw : |(130587241/250000000 : ℝ)|=(130587241/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s3_2 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669401669/1250000000 : ℝ)*x 0 + (261174467/500000000 : ℝ)*x 1 + (-441974197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669401669/1250000000 : ℝ)^4235 ≤ (21940810907407/50000000000000 : ℝ)^3211 := by
    have hnat : (669401669 : ℕ)^4235*50000000000000^3211 ≤ 21940810907407^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669401669 1250000000 21940810907407 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261174467/500000000 : ℝ)^4235 ≤ (2123182498209/5000000000000 : ℝ)^3211 := by
    have hnat : (261174467 : ℕ)^4235*5000000000000^3211 ≤ 2123182498209^3211*500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261174467 500000000 2123182498209 5000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441974197/2000000000 : ℝ)^4235 ≤ (273094564017/2000000000000 : ℝ)^3211 := by
    have hnat : (441974197 : ℕ)^4235*2000000000000^3211 ≤ 273094564017^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441974197 2000000000 273094564017 2000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669401669/1250000000 : ℝ), (261174467/500000000 : ℝ), (-441974197/2000000000 : ℝ)] ![(21940810907407/50000000000000 : ℝ), (2123182498209/5000000000000 : ℝ), (273094564017/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669401669/1250000000 : ℝ)|^4235 ≤ (21940810907407/50000000000000 : ℝ)^3211
        have hw : |(669401669/1250000000 : ℝ)|=(669401669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261174467/500000000 : ℝ)|^4235 ≤ (2123182498209/5000000000000 : ℝ)^3211
        have hw : |(261174467/500000000 : ℝ)|=(261174467/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441974197/2000000000 : ℝ)|^4235 ≤ (273094564017/2000000000000 : ℝ)^3211
        have hw : |(-441974197/2000000000 : ℝ)|=(441974197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s3_3 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (217144319/500000000 : ℝ)*x 0 + (2065239849/5000000000 : ℝ)*x 1 + (4565792191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217144319/500000000 : ℝ)^4235 ≤ (33286233518903/100000000000000 : ℝ)^3211 := by
    have hnat : (217144319 : ℕ)^4235*100000000000000^3211 ≤ 33286233518903^3211*500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217144319 500000000 33286233518903 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065239849/5000000000 : ℝ)^4235 ≤ (7788998323819/25000000000000 : ℝ)^3211 := by
    have hnat : (2065239849 : ℕ)^4235*25000000000000^3211 ≤ 7788998323819^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065239849 5000000000 7788998323819 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4565792191/10000000000 : ℝ)^4235 ≤ (3555777318097/10000000000000 : ℝ)^3211 := by
    have hnat : (4565792191 : ℕ)^4235*10000000000000^3211 ≤ 3555777318097^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4565792191 10000000000 3555777318097 10000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217144319/500000000 : ℝ), (2065239849/5000000000 : ℝ), (4565792191/10000000000 : ℝ)] ![(33286233518903/100000000000000 : ℝ), (7788998323819/25000000000000 : ℝ), (3555777318097/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217144319/500000000 : ℝ)|^4235 ≤ (33286233518903/100000000000000 : ℝ)^3211
        have hw : |(217144319/500000000 : ℝ)|=(217144319/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065239849/5000000000 : ℝ)|^4235 ≤ (7788998323819/25000000000000 : ℝ)^3211
        have hw : |(2065239849/5000000000 : ℝ)|=(2065239849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4565792191/10000000000 : ℝ)|^4235 ≤ (3555777318097/10000000000000 : ℝ)^3211
        have hw : |(4565792191/10000000000 : ℝ)|=(4565792191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s3_4 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-210072823/1000000000 : ℝ)*x 0 + (5224419011/10000000000 : ℝ)*x 1 + (679468003/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210072823/1000000000 : ℝ)^4235 ≤ (6386178811187/50000000000000 : ℝ)^3211 := by
    have hnat : (210072823 : ℕ)^4235*50000000000000^3211 ≤ 6386178811187^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210072823 1000000000 6386178811187 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5224419011/10000000000 : ℝ)^4235 ≤ (21236809019919/50000000000000 : ℝ)^3211 := by
    have hnat : (5224419011 : ℕ)^4235*50000000000000^3211 ≤ 21236809019919^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224419011 10000000000 21236809019919 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679468003/1250000000 : ℝ)^4235 ≤ (22377012163911/50000000000000 : ℝ)^3211 := by
    have hnat : (679468003 : ℕ)^4235*50000000000000^3211 ≤ 22377012163911^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679468003 1250000000 22377012163911 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210072823/1000000000 : ℝ), (5224419011/10000000000 : ℝ), (679468003/1250000000 : ℝ)] ![(6386178811187/50000000000000 : ℝ), (21236809019919/50000000000000 : ℝ), (22377012163911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210072823/1000000000 : ℝ)|^4235 ≤ (6386178811187/50000000000000 : ℝ)^3211
        have hw : |(-210072823/1000000000 : ℝ)|=(210072823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5224419011/10000000000 : ℝ)|^4235 ≤ (21236809019919/50000000000000 : ℝ)^3211
        have hw : |(5224419011/10000000000 : ℝ)|=(5224419011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679468003/1250000000 : ℝ)|^4235 ≤ (22377012163911/50000000000000 : ℝ)^3211
        have hw : |(679468003/1250000000 : ℝ)|=(679468003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s3_5 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325186363/2500000000 : ℝ)*x 0 + (-199761557/1000000000 : ℝ)*x 1 + (5435743733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325186363/2500000000 : ℝ)^4235 ≤ (43293925330793/100000000000000 : ℝ)^3211 := by
    have hnat : (1325186363 : ℕ)^4235*100000000000000^3211 ≤ 43293925330793^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325186363 2500000000 43293925330793 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199761557/1000000000 : ℝ)^4235 ≤ (1494006685841/12500000000000 : ℝ)^3211 := by
    have hnat : (199761557 : ℕ)^4235*12500000000000^3211 ≤ 1494006685841^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199761557 1000000000 1494006685841 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435743733/10000000000 : ℝ)^4235 ≤ (1118850529197/2500000000000 : ℝ)^3211 := by
    have hnat : (5435743733 : ℕ)^4235*2500000000000^3211 ≤ 1118850529197^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435743733 10000000000 1118850529197 2500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325186363/2500000000 : ℝ), (-199761557/1000000000 : ℝ), (5435743733/10000000000 : ℝ)] ![(43293925330793/100000000000000 : ℝ), (1494006685841/12500000000000 : ℝ), (1118850529197/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325186363/2500000000 : ℝ)|^4235 ≤ (43293925330793/100000000000000 : ℝ)^3211
        have hw : |(1325186363/2500000000 : ℝ)|=(1325186363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199761557/1000000000 : ℝ)|^4235 ≤ (1494006685841/12500000000000 : ℝ)^3211
        have hw : |(-199761557/1000000000 : ℝ)|=(199761557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435743733/10000000000 : ℝ)|^4235 ≤ (1118850529197/2500000000000 : ℝ)^3211
        have hw : |(5435743733/10000000000 : ℝ)|=(5435743733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s3_6 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21202979/40000000 : ℝ)*x 0 + (679468013/1250000000 : ℝ)*x 1 + (-998808009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21202979/40000000 : ℝ)^4235 ≤ (43293917768731/100000000000000 : ℝ)^3211 := by
    have hnat : (21202979 : ℕ)^4235*100000000000000^3211 ≤ 43293917768731^3211*40000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21202979 40000000 43293917768731 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679468013/1250000000 : ℝ)^4235 ≤ (8950805039307/20000000000000 : ℝ)^3211 := by
    have hnat : (679468013 : ℕ)^4235*20000000000000^3211 ≤ 8950805039307^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679468013 1250000000 8950805039307 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998808009/5000000000 : ℝ)^4235 ≤ (11952057021991/100000000000000 : ℝ)^3211 := by
    have hnat : (998808009 : ℕ)^4235*100000000000000^3211 ≤ 11952057021991^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998808009 5000000000 11952057021991 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21202979/40000000 : ℝ), (679468013/1250000000 : ℝ), (-998808009/5000000000 : ℝ)] ![(43293917768731/100000000000000 : ℝ), (8950805039307/20000000000000 : ℝ), (11952057021991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21202979/40000000 : ℝ)|^4235 ≤ (43293917768731/100000000000000 : ℝ)^3211
        have hw : |(21202979/40000000 : ℝ)|=(21202979/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679468013/1250000000 : ℝ)|^4235 ≤ (8950805039307/20000000000000 : ℝ)^3211
        have hw : |(679468013/1250000000 : ℝ)|=(679468013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-998808009/5000000000 : ℝ)|^4235 ≤ (11952057021991/100000000000000 : ℝ)^3211
        have hw : |(-998808009/5000000000 : ℝ)|=(998808009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s3_7 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342934531/10000000000 : ℝ)*x 0 + (142621669/312500000 : ℝ)*x 1 + (2066195467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342934531/10000000000 : ℝ)^4235 ≤ (33286720268249/100000000000000 : ℝ)^3211 := by
    have hnat : (4342934531 : ℕ)^4235*100000000000000^3211 ≤ 33286720268249^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342934531 10000000000 33286720268249 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142621669/312500000 : ℝ)^4235 ≤ (35538271230199/100000000000000 : ℝ)^3211 := by
    have hnat : (142621669 : ℕ)^4235*100000000000000^3211 ≤ 35538271230199^3211*312500000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142621669 312500000 35538271230199 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066195467/5000000000 : ℝ)^4235 ≤ (31175008481113/100000000000000 : ℝ)^3211 := by
    have hnat : (2066195467 : ℕ)^4235*100000000000000^3211 ≤ 31175008481113^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066195467 5000000000 31175008481113 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342934531/10000000000 : ℝ), (142621669/312500000 : ℝ), (2066195467/5000000000 : ℝ)] ![(33286720268249/100000000000000 : ℝ), (35538271230199/100000000000000 : ℝ), (31175008481113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342934531/10000000000 : ℝ)|^4235 ≤ (33286720268249/100000000000000 : ℝ)^3211
        have hw : |(4342934531/10000000000 : ℝ)|=(4342934531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142621669/312500000 : ℝ)|^4235 ≤ (35538271230199/100000000000000 : ℝ)^3211
        have hw : |(142621669/312500000 : ℝ)|=(142621669/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066195467/5000000000 : ℝ)|^4235 ≤ (31175008481113/100000000000000 : ℝ)^3211
        have hw : |(2066195467/5000000000 : ℝ)|=(2066195467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1275_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (529/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1509/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16397/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16397/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16397/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16397/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16397/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16397/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9377/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (2809928178681497/50000000000000000000 : ℝ) := by
    have hpowers : (9377/100000 : ℝ)^2117 ≤ (2809928178681497/50000000000000000000 : ℝ)^512 := by
      have hnat : (9377 : ℕ)^2117*50000000000000000000^512 ≤ 2809928178681497^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9377 100000 2809928178681497 50000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9377/100000 : ℝ)) (X := (2809928178681497/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16397/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (3540909582636089/6250000000000000000 : ℝ) := by
    have hpowers : (16397/100000 : ℝ)^2117 ≤ (3540909582636089/6250000000000000000 : ℝ)^512 := by
      have hnat : (16397 : ℕ)^2117*6250000000000000000^512 ≤ 3540909582636089^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16397 100000 3540909582636089 6250000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16397/100000 : ℝ)) (X := (3540909582636089/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002809928178681497/25000000000000000000 : ℝ) ≤ (5000135911377777/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (25002809928178681497/25000000000000000000 : ℝ)^512 ≤ (5000135911377777/5000000000000000 : ℝ)^2117 := by
      have hnat : (25002809928178681497 : ℕ)^512*5000000000000000^2117 ≤ 5000135911377777^2117*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002809928178681497 25000000000000000000 5000135911377777 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000135911377777/5000000000000000 : ℝ)) (X := (25002809928178681497/25000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50031137204839770209/50000000000000000000 : ℝ) ≤ (5000752880813643/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50031137204839770209/50000000000000000000 : ℝ)^512 ≤ (5000752880813643/5000000000000000 : ℝ)^2117 := by
      have hnat : (50031137204839770209 : ℕ)^512*5000000000000000^2117 ≤ 5000752880813643^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031137204839770209 50000000000000000000 5000752880813643 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000752880813643/5000000000000000 : ℝ)) (X := (50031137204839770209/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3128540909582636089/3125000000000000000 : ℝ) ≤ (5001369850249509/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (3128540909582636089/3125000000000000000 : ℝ)^512 ≤ (5001369850249509/5000000000000000 : ℝ)^2117 := by
      have hnat : (3128540909582636089 : ℕ)^512*5000000000000000^2117 ≤ 5001369850249509^2117*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3128540909582636089 3125000000000000000 5001369850249509 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001369850249509/5000000000000000 : ℝ)) (X := (3128540909582636089/3125000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2809928178681497/50000000000000000000 : ℝ) ≤ ((1462057643877990149/1462500000000000000 : ℝ)+2*(102828239311/58500000000000 : ℝ)*(9377/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (1462057643877990149/1462500000000000000 : ℝ)+2*(102828239311/58500000000000 : ℝ)*(9377/100000 : ℝ)=(5000135911377777/5000000000000000 : ℝ) by norm_num, show 1+2*(2809928178681497/50000000000000000000 : ℝ)=(25002809928178681497/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3540909582636089/6250000000000000000 : ℝ)+(2809928178681497/50000000000000000000 : ℝ) ≤ ((1462057643877990149/1462500000000000000 : ℝ)+(102828239311/58500000000000 : ℝ)*((16397/100000 : ℝ)+(9377/100000 : ℝ)))^(2117/512 : ℝ) := by
    rw [show (1462057643877990149/1462500000000000000 : ℝ)+(102828239311/58500000000000 : ℝ)*((16397/100000 : ℝ)+(9377/100000 : ℝ))=(5000752880813643/5000000000000000 : ℝ) by norm_num, show 1+(3540909582636089/6250000000000000000 : ℝ)+(2809928178681497/50000000000000000000 : ℝ)=(50031137204839770209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3540909582636089/6250000000000000000 : ℝ) ≤ ((1462057643877990149/1462500000000000000 : ℝ)+2*(102828239311/58500000000000 : ℝ)*(16397/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (1462057643877990149/1462500000000000000 : ℝ)+2*(102828239311/58500000000000 : ℝ)*(16397/100000 : ℝ)=(5001369850249509/5000000000000000 : ℝ) by norm_num, show 1+2*(3540909582636089/6250000000000000000 : ℝ)=(3128540909582636089/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1462057643877990149/1462500000000000000 : ℝ)*(X 1 0+X 2 0)+(102828239311/58500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (9377/100000 : ℝ)) (hi := (16397/100000 : ℝ)) (c := (1462057643877990149/1462500000000000000 : ℝ)) (alpha := (102828239311/58500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1462057643877990149/1462500000000000000 : ℝ)*(X 0 1+X 2 1)+(102828239311/58500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (9377/100000 : ℝ)) (hi := (16397/100000 : ℝ)) (c := (1462057643877990149/1462500000000000000 : ℝ)) (alpha := (102828239311/58500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1462057643877990149/1462500000000000000 : ℝ)*(X 0 2+X 1 2)+(102828239311/58500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (9377/100000 : ℝ)) (hi := (16397/100000 : ℝ)) (c := (1462057643877990149/1462500000000000000 : ℝ)) (alpha := (102828239311/58500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1050352093/5000000000 : ℝ)*X 0 0+(1359169909/2500000000 : ℝ)*X 0 1+(2611744711/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355213339/10000000000 : ℝ)*X 1 0+(-138116913/625000000 : ℝ)*X 1 1+(130587241/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669401669/1250000000 : ℝ)*X 2 0+(261174467/500000000 : ℝ)*X 2 1+(-441974197/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217144319/500000000 : ℝ)*X 0 0+(2065239849/5000000000 : ℝ)*X 0 1+(4565792191/10000000000 : ℝ)*X 0 2+(217144319/500000000 : ℝ)*X 1 0+(2065239849/5000000000 : ℝ)*X 1 1+(4565792191/10000000000 : ℝ)*X 1 2+(217144319/500000000 : ℝ)*X 2 0+(2065239849/5000000000 : ℝ)*X 2 1+(4565792191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-210072823/1000000000 : ℝ)*X 0 0+(5224419011/10000000000 : ℝ)*X 0 1+(679468003/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325186363/2500000000 : ℝ)*X 1 0+(-199761557/1000000000 : ℝ)*X 1 1+(5435743733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((21202979/40000000 : ℝ)*X 2 0+(679468013/1250000000 : ℝ)*X 2 1+(-998808009/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342934531/10000000000 : ℝ)*X 0 0+(142621669/312500000 : ℝ)*X 0 1+(2066195467/5000000000 : ℝ)*X 0 2+(4342934531/10000000000 : ℝ)*X 1 0+(142621669/312500000 : ℝ)*X 1 1+(2066195467/5000000000 : ℝ)*X 1 2+(4342934531/10000000000 : ℝ)*X 2 0+(142621669/312500000 : ℝ)*X 2 1+(2066195467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5257749628499357060089/487500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1792438531/100000000000000 : ℝ)*(base19) + (1559741479/100000000000000 : ℝ)*(base23) + (75776543/50000000000000 : ℝ)*(lower2) + (559638221/100000000000000 : ℝ)*(upper3) + (1302559/6250000000000 : ℝ)*(lower4) + (1746981872447449/50000000000000 : ℝ)*(major0) + (1746981872447449/50000000000000 : ℝ)*(major1) + (1746981872447449/50000000000000 : ℝ)*(major2) + (938135976559979/20000000000000 : ℝ)*(sp0) + (4690696878134493/100000000000000 : ℝ)*(sp1) + (938139422166309/20000000000000 : ℝ)*(sp2) + (459442101430659/20000000000000 : ℝ)*(sp3) + (18787773129/100000000000000 : ℝ)*(sp4) + (2244069903/12500000000000 : ℝ)*(sp7) + (1148614229856259/50000000000000 : ℝ)*(f.failure) + (146584333455407/3125000000000 : ℝ)*(f.sum) + (1480022383039/1462500000000000000000000000 : ℝ)*base65 + (66379901167490033/24375000000000000000000000000000 : ℝ)*base68 + (6619752686259967/24375000000000000000000000000000 : ℝ)*base69 + (67331739476259967/24375000000000000000000000000000 : ℝ)*base71 + (564394668359/365625000000000000000000000 : ℝ)*base74 + (120310883954990033/24375000000000000000000000000000 : ℝ)*base76 + (85437813346884967/24375000000000000000000000000000 : ℝ)*base77 + (30578794779365033/24375000000000000000000000000000 : ℝ)*base80 + (539951658761/1462500000000000000000000000 : ℝ)*base82 + (3824663/625000000000000000000 : ℝ)*base90 + (3824663/625000000000000000000 : ℝ)*base92 + (3824663/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2141265840768552496588979/312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (582148277/25000000000000 : ℝ)*(base19) + (421237423/25000000000000 : ℝ)*(base23) + (73178141/100000000000000 : ℝ)*(upper2) + (18147459/20000000000000 : ℝ)*(upper3) + (146811667/50000000000000 : ℝ)*(upper5) + (1762381603915777/50000000000000 : ℝ)*(major0) + (1762381603915777/50000000000000 : ℝ)*(major1) + (1762381603915777/50000000000000 : ℝ)*(major2) + (7862177621/20000000000000 : ℝ)*(sp1) + (24225073579/100000000000000 : ℝ)*(sp2) + (2366023772621831/50000000000000 : ℝ)*(sp4) + (4732005905762449/100000000000000 : ℝ)*(sp5) + (473202163522039/10000000000000 : ℝ)*(sp6) + (289684830252217/12500000000000 : ℝ)*(sp7) + (289684830252217/12500000000000 : ℝ)*(f.failure) + (2366023772621831/50000000000000 : ℝ)*(f.sum) + (191856273769/112500000000000000000000000 : ℝ)*base65 + (13994270393374507/1875000000000000000000000000000 : ℝ)*base67 + (30543322752124507/1875000000000000000000000000000 : ℝ)*base69 + (21437900788999507/1875000000000000000000000000000 : ℝ)*base71 + (90360482011/28125000000000000000000000 : ℝ)*base73 + (28546750697749507/1875000000000000000000000000000 : ℝ)*base75 + (19812060604624507/1875000000000000000000000000000 : ℝ)*base77 + (44134576384624507/1875000000000000000000000000000 : ℝ)*base79 + (885388402613/225000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3119069/156250000000000000000 : ℝ)*base90 + (3119069/156250000000000000000 : ℝ)*base92 + (3119069/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1275_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (529/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1509/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1275_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1275_s4_0 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-52570261/250000000 : ℝ)*x 0 + (42345881/78125000 : ℝ)*x 1 + (209540661/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52570261/250000000 : ℝ)^4235 ≤ (12789057275613/100000000000000 : ℝ)^3211 := by
    have hnat : (52570261 : ℕ)^4235*100000000000000^3211 ≤ 12789057275613^3211*250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52570261 250000000 12789057275613 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42345881/78125000 : ℝ)^4235 ≤ (1393315614247/3125000000000 : ℝ)^3211 := by
    have hnat : (42345881 : ℕ)^4235*3125000000000^3211 ≤ 1393315614247^3211*78125000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42345881 78125000 1393315614247 3125000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209540661/400000000 : ℝ)^4235 ≤ (852496860887/2000000000000 : ℝ)^3211 := by
    have hnat : (209540661 : ℕ)^4235*2000000000000^3211 ≤ 852496860887^3211*400000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209540661 400000000 852496860887 2000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52570261/250000000 : ℝ), (42345881/78125000 : ℝ), (209540661/400000000 : ℝ)] ![(12789057275613/100000000000000 : ℝ), (1393315614247/3125000000000 : ℝ), (852496860887/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52570261/250000000 : ℝ)|^4235 ≤ (12789057275613/100000000000000 : ℝ)^3211
        have hw : |(-52570261/250000000 : ℝ)|=(52570261/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42345881/78125000 : ℝ)|^4235 ≤ (1393315614247/3125000000000 : ℝ)^3211
        have hw : |(42345881/78125000 : ℝ)|=(42345881/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209540661/400000000 : ℝ)|^4235 ≤ (852496860887/2000000000000 : ℝ)^3211
        have hw : |(209540661/400000000 : ℝ)|=(209540661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s4_1 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351079463/10000000000 : ℝ)*x 0 + (-2195558557/10000000000 : ℝ)*x 1 + (654814517/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351079463/10000000000 : ℝ)^4235 ≤ (43836950951683/100000000000000 : ℝ)^3211 := by
    have hnat : (5351079463 : ℕ)^4235*100000000000000^3211 ≤ 43836950951683^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351079463 10000000000 43836950951683 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195558557/10000000000 : ℝ)^4235 ≤ (3384552540077/25000000000000 : ℝ)^3211 := by
    have hnat : (2195558557 : ℕ)^4235*25000000000000^3211 ≤ 3384552540077^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195558557 10000000000 3384552540077 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654814517/1250000000 : ℝ)^4235 ≤ (1332026214679/3125000000000 : ℝ)^3211 := by
    have hnat : (654814517 : ℕ)^4235*3125000000000^3211 ≤ 1332026214679^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654814517 1250000000 1332026214679 3125000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351079463/10000000000 : ℝ), (-2195558557/10000000000 : ℝ), (654814517/1250000000 : ℝ)] ![(43836950951683/100000000000000 : ℝ), (3384552540077/25000000000000 : ℝ), (1332026214679/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351079463/10000000000 : ℝ)|^4235 ≤ (43836950951683/100000000000000 : ℝ)^3211
        have hw : |(5351079463/10000000000 : ℝ)|=(5351079463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195558557/10000000000 : ℝ)|^4235 ≤ (3384552540077/25000000000000 : ℝ)^3211
        have hw : |(-2195558557/10000000000 : ℝ)|=(2195558557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654814517/1250000000 : ℝ)|^4235 ≤ (1332026214679/3125000000000 : ℝ)^3211
        have hw : |(654814517/1250000000 : ℝ)|=(654814517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s4_2 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337769783/2500000000 : ℝ)*x 0 + (5238516283/10000000000 : ℝ)*x 1 + (-2195558803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337769783/2500000000 : ℝ)^4235 ≤ (43836947375333/100000000000000 : ℝ)^3211 := by
    have hnat : (1337769783 : ℕ)^4235*100000000000000^3211 ≤ 43836947375333^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337769783 2500000000 43836947375333 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238516283/10000000000 : ℝ)^4235 ≤ (10656210111821/25000000000000 : ℝ)^3211 := by
    have hnat : (5238516283 : ℕ)^4235*25000000000000^3211 ≤ 10656210111821^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238516283 10000000000 10656210111821 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195558803/10000000000 : ℝ)^4235 ≤ (13538212160927/100000000000000 : ℝ)^3211 := by
    have hnat : (2195558803 : ℕ)^4235*100000000000000^3211 ≤ 13538212160927^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195558803 10000000000 13538212160927 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337769783/2500000000 : ℝ), (5238516283/10000000000 : ℝ), (-2195558803/10000000000 : ℝ)] ![(43836947375333/100000000000000 : ℝ), (10656210111821/25000000000000 : ℝ), (13538212160927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337769783/2500000000 : ℝ)|^4235 ≤ (43836947375333/100000000000000 : ℝ)^3211
        have hw : |(1337769783/2500000000 : ℝ)|=(1337769783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238516283/10000000000 : ℝ)|^4235 ≤ (10656210111821/25000000000000 : ℝ)^3211
        have hw : |(5238516283/10000000000 : ℝ)|=(5238516283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2195558803/10000000000 : ℝ)|^4235 ≤ (13538212160927/100000000000000 : ℝ)^3211
        have hw : |(-2195558803/10000000000 : ℝ)|=(2195558803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s4_3 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (868831501/2000000000 : ℝ)*x 0 + (1040602883/2500000000 : ℝ)*x 1 + (2266769533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868831501/2000000000 : ℝ)^4235 ≤ (266392669263/800000000000 : ℝ)^3211 := by
    have hnat : (868831501 : ℕ)^4235*800000000000^3211 ≤ 266392669263^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868831501 2000000000 266392669263 800000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040602883/2500000000 : ℝ)^4235 ≤ (31474055574047/100000000000000 : ℝ)^3211 := by
    have hnat : (1040602883 : ℕ)^4235*100000000000000^3211 ≤ 31474055574047^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040602883 2500000000 31474055574047 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266769533/5000000000 : ℝ)^4235 ≤ (35226860752617/100000000000000 : ℝ)^3211 := by
    have hnat : (2266769533 : ℕ)^4235*100000000000000^3211 ≤ 35226860752617^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266769533 5000000000 35226860752617 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868831501/2000000000 : ℝ), (1040602883/2500000000 : ℝ), (2266769533/5000000000 : ℝ)] ![(266392669263/800000000000 : ℝ), (31474055574047/100000000000000 : ℝ), (35226860752617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868831501/2000000000 : ℝ)|^4235 ≤ (266392669263/800000000000 : ℝ)^3211
        have hw : |(868831501/2000000000 : ℝ)|=(868831501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040602883/2500000000 : ℝ)|^4235 ≤ (31474055574047/100000000000000 : ℝ)^3211
        have hw : |(1040602883/2500000000 : ℝ)|=(1040602883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2266769533/5000000000 : ℝ)|^4235 ≤ (35226860752617/100000000000000 : ℝ)^3211
        have hw : |(2266769533/5000000000 : ℝ)|=(2266769533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s4_4 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051412821/5000000000 : ℝ)*x 0 + (5239192791/10000000000 : ℝ)*x 1 + (677449069/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051412821/5000000000 : ℝ)^4235 ≤ (6394589608727/50000000000000 : ℝ)^3211 := by
    have hnat : (1051412821 : ℕ)^4235*50000000000000^3211 ≤ 6394589608727^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051412821 5000000000 6394589608727 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239192791/10000000000 : ℝ)^4235 ≤ (42632100661861/100000000000000 : ℝ)^3211 := by
    have hnat : (5239192791 : ℕ)^4235*100000000000000^3211 ≤ 42632100661861^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239192791 10000000000 42632100661861 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677449069/1250000000 : ℝ)^4235 ≤ (4457872011063/10000000000000 : ℝ)^3211 := by
    have hnat : (677449069 : ℕ)^4235*10000000000000^3211 ≤ 4457872011063^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677449069 1250000000 4457872011063 10000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051412821/5000000000 : ℝ), (5239192791/10000000000 : ℝ), (677449069/1250000000 : ℝ)] ![(6394589608727/50000000000000 : ℝ), (42632100661861/100000000000000 : ℝ), (4457872011063/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051412821/5000000000 : ℝ)|^4235 ≤ (6394589608727/50000000000000 : ℝ)^3211
        have hw : |(-1051412821/5000000000 : ℝ)|=(1051412821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239192791/10000000000 : ℝ)|^4235 ≤ (42632100661861/100000000000000 : ℝ)^3211
        have hw : |(5239192791/10000000000 : ℝ)|=(5239192791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677449069/1250000000 : ℝ)|^4235 ≤ (4457872011063/10000000000000 : ℝ)^3211
        have hw : |(677449069/1250000000 : ℝ)|=(677449069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s4_5 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652322981/5000000000 : ℝ)*x 0 + (-40289647/200000000 : ℝ)*x 1 + (2709796321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652322981/5000000000 : ℝ)^4235 ≤ (43335947209417/100000000000000 : ℝ)^3211 := by
    have hnat : (2652322981 : ℕ)^4235*100000000000000^3211 ≤ 43335947209417^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652322981 5000000000 43335947209417 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40289647/200000000 : ℝ)^4235 ≤ (6042665839869/50000000000000 : ℝ)^3211 := by
    have hnat : (40289647 : ℕ)^4235*50000000000000^3211 ≤ 6042665839869^3211*200000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40289647 200000000 6042665839869 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709796321/5000000000 : ℝ)^4235 ≤ (11144680271751/25000000000000 : ℝ)^3211 := by
    have hnat : (2709796321 : ℕ)^4235*25000000000000^3211 ≤ 11144680271751^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709796321 5000000000 11144680271751 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652322981/5000000000 : ℝ), (-40289647/200000000 : ℝ), (2709796321/5000000000 : ℝ)] ![(43335947209417/100000000000000 : ℝ), (6042665839869/50000000000000 : ℝ), (11144680271751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652322981/5000000000 : ℝ)|^4235 ≤ (43335947209417/100000000000000 : ℝ)^3211
        have hw : |(2652322981/5000000000 : ℝ)|=(2652322981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40289647/200000000 : ℝ)|^4235 ≤ (6042665839869/50000000000000 : ℝ)^3211
        have hw : |(-40289647/200000000 : ℝ)|=(40289647/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709796321/5000000000 : ℝ)|^4235 ≤ (11144680271751/25000000000000 : ℝ)^3211
        have hw : |(2709796321/5000000000 : ℝ)|=(2709796321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s4_6 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530464583/1000000000 : ℝ)*x 0 + (677449061/1250000000 : ℝ)*x 1 + (-1007241371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530464583/1000000000 : ℝ)^4235 ≤ (43335945787157/100000000000000 : ℝ)^3211 := by
    have hnat : (530464583 : ℕ)^4235*100000000000000^3211 ≤ 43335945787157^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530464583 1000000000 43335945787157 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677449061/1250000000 : ℝ)^4235 ≤ (44578719416319/100000000000000 : ℝ)^3211 := by
    have hnat : (677449061 : ℕ)^4235*100000000000000^3211 ≤ 44578719416319^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677449061 1250000000 44578719416319 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007241371/5000000000 : ℝ)^4235 ≤ (6042667390699/50000000000000 : ℝ)^3211 := by
    have hnat : (1007241371 : ℕ)^4235*50000000000000^3211 ≤ 6042667390699^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007241371 5000000000 6042667390699 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530464583/1000000000 : ℝ), (677449061/1250000000 : ℝ), (-1007241371/5000000000 : ℝ)] ![(43335945787157/100000000000000 : ℝ), (44578719416319/100000000000000 : ℝ), (6042667390699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530464583/1000000000 : ℝ)|^4235 ≤ (43335945787157/100000000000000 : ℝ)^3211
        have hw : |(530464583/1000000000 : ℝ)|=(530464583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677449061/1250000000 : ℝ)|^4235 ≤ (44578719416319/100000000000000 : ℝ)^3211
        have hw : |(677449061/1250000000 : ℝ)|=(677449061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1007241371/5000000000 : ℝ)|^4235 ≤ (6042667390699/50000000000000 : ℝ)^3211
        have hw : |(-1007241371/5000000000 : ℝ)|=(1007241371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s4_7 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (868837601/2000000000 : ℝ)*x 0 + (2266078579/5000000000 : ℝ)*x 1 + (832760107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868837601/2000000000 : ℝ)^4235 ≤ (16649696002589/50000000000000 : ℝ)^3211 := by
    have hnat : (868837601 : ℕ)^4235*50000000000000^3211 ≤ 16649696002589^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868837601 2000000000 16649696002589 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266078579/5000000000 : ℝ)^4235 ≤ (35212699303053/100000000000000 : ℝ)^3211 := by
    have hnat : (2266078579 : ℕ)^4235*100000000000000^3211 ≤ 35212699303053^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266078579 5000000000 35212699303053 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832760107/2000000000 : ℝ)^4235 ≤ (15743954338953/50000000000000 : ℝ)^3211 := by
    have hnat : (832760107 : ℕ)^4235*50000000000000^3211 ≤ 15743954338953^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832760107 2000000000 15743954338953 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868837601/2000000000 : ℝ), (2266078579/5000000000 : ℝ), (832760107/2000000000 : ℝ)] ![(16649696002589/50000000000000 : ℝ), (35212699303053/100000000000000 : ℝ), (15743954338953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868837601/2000000000 : ℝ)|^4235 ≤ (16649696002589/50000000000000 : ℝ)^3211
        have hw : |(868837601/2000000000 : ℝ)|=(868837601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2266078579/5000000000 : ℝ)|^4235 ≤ (35212699303053/100000000000000 : ℝ)^3211
        have hw : |(2266078579/5000000000 : ℝ)|=(2266078579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832760107/2000000000 : ℝ)|^4235 ≤ (15743954338953/50000000000000 : ℝ)^3211
        have hw : |(832760107/2000000000 : ℝ)|=(832760107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1275_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1509/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (529/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10901/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14747/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1509/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (529/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1509/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (529/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1509/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (529/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1509/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (529/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1509/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (529/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1509/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (529/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (529/5000 : ℝ) ^ (2117/512 : ℝ) ≤ (9257140858856969/100000000000000000000 : ℝ) := by
    have hpowers : (529/5000 : ℝ)^2117 ≤ (9257140858856969/100000000000000000000 : ℝ)^512 := by
      have hnat : (529 : ℕ)^2117*100000000000000000000^512 ≤ 9257140858856969^512*5000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        529 5000 9257140858856969 100000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (529/5000 : ℝ)) (X := (9257140858856969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1509/10000 : ℝ) ^ (2117/512 : ℝ) ≤ (40185789146211173/100000000000000000000 : ℝ) := by
    have hpowers : (1509/10000 : ℝ)^2117 ≤ (40185789146211173/100000000000000000000 : ℝ)^512 := by
      have hnat : (1509 : ℕ)^2117*100000000000000000000^512 ≤ 40185789146211173^512*10000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1509 10000 40185789146211173 100000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1509/10000 : ℝ)) (X := (40185789146211173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009257140858856969/50000000000000000000 : ℝ) ≤ (5000223869792783/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50009257140858856969/50000000000000000000 : ℝ)^512 ≤ (5000223869792783/5000000000000000 : ℝ)^2117 := by
      have hnat : (50009257140858856969 : ℕ)^512*5000000000000000^2117 ≤ 5000223869792783^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009257140858856969 50000000000000000000 5000223869792783 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000223869792783/5000000000000000 : ℝ)) (X := (50009257140858856969/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024721465002534071/50000000000000000000 : ℝ) ≤ (10001195561497631/10000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50024721465002534071/50000000000000000000 : ℝ)^512 ≤ (10001195561497631/10000000000000000 : ℝ)^2117 := by
      have hnat : (50024721465002534071 : ℕ)^512*10000000000000000^2117 ≤ 10001195561497631^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024721465002534071 50000000000000000000 10001195561497631 10000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001195561497631/10000000000000000 : ℝ)) (X := (50024721465002534071/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040185789146211173/50000000000000000000 : ℝ) ≤ (312560730731553/312500000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50040185789146211173/50000000000000000000 : ℝ)^512 ≤ (312560730731553/312500000000000 : ℝ)^2117 := by
      have hnat : (50040185789146211173 : ℕ)^512*312500000000000^2117 ≤ 312560730731553^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040185789146211173 50000000000000000000 312560730731553 312500000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312560730731553/312500000000000 : ℝ)) (X := (50040185789146211173/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9257140858856969/100000000000000000000 : ℝ) ≤ ((2254309769693580363/2255000000000000000 : ℝ)+2*(149564382413/90200000000000 : ℝ)*(529/5000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (2254309769693580363/2255000000000000000 : ℝ)+2*(149564382413/90200000000000 : ℝ)*(529/5000 : ℝ)=(5000223869792783/5000000000000000 : ℝ) by norm_num, show 1+2*(9257140858856969/100000000000000000000 : ℝ)=(50009257140858856969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40185789146211173/100000000000000000000 : ℝ)+(9257140858856969/100000000000000000000 : ℝ) ≤ ((2254309769693580363/2255000000000000000 : ℝ)+(149564382413/90200000000000 : ℝ)*((1509/10000 : ℝ)+(529/5000 : ℝ)))^(2117/512 : ℝ) := by
    rw [show (2254309769693580363/2255000000000000000 : ℝ)+(149564382413/90200000000000 : ℝ)*((1509/10000 : ℝ)+(529/5000 : ℝ))=(10001195561497631/10000000000000000 : ℝ) by norm_num, show 1+(40185789146211173/100000000000000000000 : ℝ)+(9257140858856969/100000000000000000000 : ℝ)=(50024721465002534071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40185789146211173/100000000000000000000 : ℝ) ≤ ((2254309769693580363/2255000000000000000 : ℝ)+2*(149564382413/90200000000000 : ℝ)*(1509/10000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (2254309769693580363/2255000000000000000 : ℝ)+2*(149564382413/90200000000000 : ℝ)*(1509/10000 : ℝ)=(312560730731553/312500000000000 : ℝ) by norm_num, show 1+2*(40185789146211173/100000000000000000000 : ℝ)=(50040185789146211173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2254309769693580363/2255000000000000000 : ℝ)*(X 1 0+X 2 0)+(149564382413/90200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (529/5000 : ℝ)) (hi := (1509/10000 : ℝ)) (c := (2254309769693580363/2255000000000000000 : ℝ)) (alpha := (149564382413/90200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2254309769693580363/2255000000000000000 : ℝ)*(X 0 1+X 2 1)+(149564382413/90200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (529/5000 : ℝ)) (hi := (1509/10000 : ℝ)) (c := (2254309769693580363/2255000000000000000 : ℝ)) (alpha := (149564382413/90200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2254309769693580363/2255000000000000000 : ℝ)*(X 0 2+X 1 2)+(149564382413/90200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (529/5000 : ℝ)) (hi := (1509/10000 : ℝ)) (c := (2254309769693580363/2255000000000000000 : ℝ)) (alpha := (149564382413/90200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-52570261/250000000 : ℝ)*X 0 0+(42345881/78125000 : ℝ)*X 0 1+(209540661/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351079463/10000000000 : ℝ)*X 1 0+(-2195558557/10000000000 : ℝ)*X 1 1+(654814517/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337769783/2500000000 : ℝ)*X 2 0+(5238516283/10000000000 : ℝ)*X 2 1+(-2195558803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((868831501/2000000000 : ℝ)*X 0 0+(1040602883/2500000000 : ℝ)*X 0 1+(2266769533/5000000000 : ℝ)*X 0 2+(868831501/2000000000 : ℝ)*X 1 0+(1040602883/2500000000 : ℝ)*X 1 1+(2266769533/5000000000 : ℝ)*X 1 2+(868831501/2000000000 : ℝ)*X 2 0+(1040602883/2500000000 : ℝ)*X 2 1+(2266769533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1051412821/5000000000 : ℝ)*X 0 0+(5239192791/10000000000 : ℝ)*X 0 1+(677449069/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652322981/5000000000 : ℝ)*X 1 0+(-40289647/200000000 : ℝ)*X 1 1+(2709796321/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530464583/1000000000 : ℝ)*X 2 0+(677449061/1250000000 : ℝ)*X 2 1+(-1007241371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((868837601/2000000000 : ℝ)*X 0 0+(2266078579/5000000000 : ℝ)*X 0 1+(832760107/2000000000 : ℝ)*X 0 2+(868837601/2000000000 : ℝ)*X 1 0+(2266078579/5000000000 : ℝ)*X 1 1+(832760107/2000000000 : ℝ)*X 1 2+(868837601/2000000000 : ℝ)*X 2 0+(2266078579/5000000000 : ℝ)*X 2 1+(832760107/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (698119988067359278976725923/56375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (773480377/50000000000000 : ℝ)*(base19) + (1464539219/100000000000000 : ℝ)*(base23) + (1738343/2500000000000 : ℝ)*(lower2) + (148876983/100000000000000 : ℝ)*(upper3) + (207543001/100000000000000 : ℝ)*(lower4) + (2049111539815293/50000000000000 : ℝ)*(major0) + (2049111539815293/50000000000000 : ℝ)*(major1) + (2049111539815293/50000000000000 : ℝ)*(major2) + (2750952626033577/50000000000000 : ℝ)*(sp0) + (2750962170897767/50000000000000 : ℝ)*(sp1) + (5501924424217069/100000000000000 : ℝ)*(sp2) + (538901141342937/20000000000000 : ℝ)*(sp3) + (20636689133/100000000000000 : ℝ)*(sp4) + (14151006753/100000000000000 : ℝ)*(sp7) + (2694519857721439/100000000000000 : ℝ)*(f.failure) + (85967592011817/1562500000000 : ℝ)*(f.sum) + (11799641194711/2255000000000000000000000000 : ℝ)*base66 + (231207543192366359/112750000000000000000000000000000 : ℝ)*base67 + (358038162101866359/112750000000000000000000000000000 : ℝ)*base69 + (835907961160883641/112750000000000000000000000000000 : ℝ)*base72 + (8835123236229/2255000000000000000000000000 : ℝ)*base73 + (1002192514487366359/112750000000000000000000000000000 : ℝ)*base75 + (1831669267552383641/112750000000000000000000000000000 : ℝ)*base78 + (318258204329366359/112750000000000000000000000000000 : ℝ)*base79 + (57225218219/2255000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (11002077/1250000000000000000000 : ℝ)*base89 + (11002077/1250000000000000000000 : ℝ)*base91 + (11002077/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94015977403176107229483699/28187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70582241/50000000000000 : ℝ)*(base19) + (5127209/10000000000000 : ℝ)*(base23) + (73034829/100000000000000 : ℝ)*(upper3) + (13649121/20000000000000 : ℝ)*(lower4) + (124111/400000000000 : ℝ)*(upper5) + (1032251722731491/25000000000000 : ℝ)*(major0) + (1032251722731491/25000000000000 : ℝ)*(major1) + (1032251722731491/25000000000000 : ℝ)*(major2) + (3458078889/50000000000000 : ℝ)*(sp0) + (920873613/10000000000000 : ℝ)*(sp1) + (2771623502603129/50000000000000 : ℝ)*(sp4) + (21653299107279/390625000000 : ℝ)*(sp5) + (5543253870091947/100000000000000 : ℝ)*(sp6) + (678689937327151/25000000000000 : ℝ)*(sp7) + (678689937327151/25000000000000 : ℝ)*(f.failure) + (1385813480341009/25000000000000 : ℝ)*(f.sum) + (2411330408123/1127500000000000000000000000 : ℝ)*base65 + (144959426159636233/56375000000000000000000000000000 : ℝ)*base67 + (183231737610636233/56375000000000000000000000000000 : ℝ)*base69 + (116982731575863767/56375000000000000000000000000000 : ℝ)*base72 + (2884945913239/563750000000000000000000000 : ℝ)*base73 + (65542569629613767/56375000000000000000000000000000 : ℝ)*base76 + (138897888867363767/56375000000000000000000000000000 : ℝ)*base78 + (653537119822113767/56375000000000000000000000000000 : ℝ)*base80 + (195947268199/35234375000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3050707/312500000000000000000 : ℝ)*base90 + (3050707/312500000000000000000 : ℝ)*base92 + (3050707/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1275_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1509/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (529/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1275_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1275_s5_0 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-210321751/1000000000 : ℝ)*x 0 + (5416862767/10000000000 : ℝ)*x 1 + (2620829449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210321751/1000000000 : ℝ)^4235 ≤ (3198080664449/25000000000000 : ℝ)^3211 := by
    have hnat : (210321751 : ℕ)^4235*25000000000000^3211 ≤ 3198080664449^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210321751 1000000000 3198080664449 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416862767/10000000000 : ℝ)^4235 ≤ (1781964324741/4000000000000 : ℝ)^3211 := by
    have hnat : (5416862767 : ℕ)^4235*4000000000000^3211 ≤ 1781964324741^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416862767 10000000000 1781964324741 4000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620829449/5000000000 : ℝ)^4235 ≤ (53323211501/125000000000 : ℝ)^3211 := by
    have hnat : (2620829449 : ℕ)^4235*125000000000^3211 ≤ 53323211501^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620829449 5000000000 53323211501 125000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210321751/1000000000 : ℝ), (5416862767/10000000000 : ℝ), (2620829449/5000000000 : ℝ)] ![(3198080664449/25000000000000 : ℝ), (1781964324741/4000000000000 : ℝ), (53323211501/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210321751/1000000000 : ℝ)|^4235 ≤ (3198080664449/25000000000000 : ℝ)^3211
        have hw : |(-210321751/1000000000 : ℝ)|=(210321751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416862767/10000000000 : ℝ)|^4235 ≤ (1781964324741/4000000000000 : ℝ)^3211
        have hw : |(5416862767/10000000000 : ℝ)|=(5416862767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620829449/5000000000 : ℝ)|^4235 ≤ (53323211501/125000000000 : ℝ)^3211
        have hw : |(2620829449/5000000000 : ℝ)|=(2620829449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s5_1 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070043311/2000000000 : ℝ)*x 0 + (-1096278367/5000000000 : ℝ)*x 1 + (1048331783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070043311/2000000000 : ℝ)^4235 ≤ (350621021949/800000000000 : ℝ)^3211 := by
    have hnat : (1070043311 : ℕ)^4235*800000000000^3211 ≤ 350621021949^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070043311 2000000000 350621021949 800000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096278367/5000000000 : ℝ)^4235 ≤ (1689225357827/12500000000000 : ℝ)^3211 := by
    have hnat : (1096278367 : ℕ)^4235*12500000000000^3211 ≤ 1689225357827^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096278367 5000000000 1689225357827 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048331783/2000000000 : ℝ)^4235 ≤ (21329284691637/50000000000000 : ℝ)^3211 := by
    have hnat : (1048331783 : ℕ)^4235*50000000000000^3211 ≤ 21329284691637^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048331783 2000000000 21329284691637 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070043311/2000000000 : ℝ), (-1096278367/5000000000 : ℝ), (1048331783/2000000000 : ℝ)] ![(350621021949/800000000000 : ℝ), (1689225357827/12500000000000 : ℝ), (21329284691637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070043311/2000000000 : ℝ)|^4235 ≤ (350621021949/800000000000 : ℝ)^3211
        have hw : |(1070043311/2000000000 : ℝ)|=(1070043311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096278367/5000000000 : ℝ)|^4235 ≤ (1689225357827/12500000000000 : ℝ)^3211
        have hw : |(-1096278367/5000000000 : ℝ)|=(1096278367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048331783/2000000000 : ℝ)|^4235 ≤ (21329284691637/50000000000000 : ℝ)^3211
        have hw : |(1048331783/2000000000 : ℝ)|=(1048331783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s5_2 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350216613/10000000000 : ℝ)*x 0 + (5241658917/10000000000 : ℝ)*x 1 + (-2192556653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350216613/10000000000 : ℝ)^4235 ≤ (5478453546283/12500000000000 : ℝ)^3211 := by
    have hnat : (5350216613 : ℕ)^4235*12500000000000^3211 ≤ 5478453546283^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350216613 10000000000 5478453546283 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241658917/10000000000 : ℝ)^4235 ≤ (42658569404741/100000000000000 : ℝ)^3211 := by
    have hnat : (5241658917 : ℕ)^4235*100000000000000^3211 ≤ 42658569404741^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241658917 10000000000 42658569404741 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2192556653/10000000000 : ℝ)^4235 ≤ (13513802204163/100000000000000 : ℝ)^3211 := by
    have hnat : (2192556653 : ℕ)^4235*100000000000000^3211 ≤ 13513802204163^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192556653 10000000000 13513802204163 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350216613/10000000000 : ℝ), (5241658917/10000000000 : ℝ), (-2192556653/10000000000 : ℝ)] ![(5478453546283/12500000000000 : ℝ), (42658569404741/100000000000000 : ℝ), (13513802204163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350216613/10000000000 : ℝ)|^4235 ≤ (5478453546283/12500000000000 : ℝ)^3211
        have hw : |(5350216613/10000000000 : ℝ)|=(5350216613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241658917/10000000000 : ℝ)|^4235 ≤ (42658569404741/100000000000000 : ℝ)^3211
        have hw : |(5241658917/10000000000 : ℝ)|=(5241658917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2192556653/10000000000 : ℝ)|^4235 ≤ (13513802204163/100000000000000 : ℝ)^3211
        have hw : |(-2192556653/10000000000 : ℝ)|=(2192556653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s5_3 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4344397839/10000000000 : ℝ)*x 0 + (833814081/2000000000 : ℝ)*x 1 + (141463087/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344397839/10000000000 : ℝ)^4235 ≤ (16650756696339/50000000000000 : ℝ)^3211 := by
    have hnat : (4344397839 : ℕ)^4235*50000000000000^3211 ≤ 16650756696339^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344397839 10000000000 16650756696339 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833814081/2000000000 : ℝ)^4235 ≤ (15770240340327/50000000000000 : ℝ)^3211 := by
    have hnat : (833814081 : ℕ)^4235*50000000000000^3211 ≤ 15770240340327^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833814081 2000000000 15770240340327 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141463087/312500000 : ℝ)^4235 ≤ (439475073877/1250000000000 : ℝ)^3211 := by
    have hnat : (141463087 : ℕ)^4235*1250000000000^3211 ≤ 439475073877^3211*312500000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141463087 312500000 439475073877 1250000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344397839/10000000000 : ℝ), (833814081/2000000000 : ℝ), (141463087/312500000 : ℝ)] ![(16650756696339/50000000000000 : ℝ), (15770240340327/50000000000000 : ℝ), (439475073877/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344397839/10000000000 : ℝ)|^4235 ≤ (16650756696339/50000000000000 : ℝ)^3211
        have hw : |(4344397839/10000000000 : ℝ)|=(4344397839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833814081/2000000000 : ℝ)|^4235 ≤ (15770240340327/50000000000000 : ℝ)^3211
        have hw : |(833814081/2000000000 : ℝ)|=(833814081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141463087/312500000 : ℝ)|^4235 ≤ (439475073877/1250000000000 : ℝ)^3211
        have hw : |(141463087/312500000 : ℝ)|=(141463087/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s5_4 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103230601/10000000000 : ℝ)*x 0 + (5242287817/10000000000 : ℝ)*x 1 + (338514419/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103230601/10000000000 : ℝ)^4235 ≤ (2558485534571/20000000000000 : ℝ)^3211 := by
    have hnat : (2103230601 : ℕ)^4235*20000000000000^3211 ≤ 2558485534571^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103230601 10000000000 2558485534571 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242287817/10000000000 : ℝ)^4235 ≤ (42665319976243/100000000000000 : ℝ)^3211 := by
    have hnat : (5242287817 : ℕ)^4235*100000000000000^3211 ≤ 42665319976243^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242287817 10000000000 42665319976243 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338514419/625000000 : ℝ)^4235 ≤ (44542252343189/100000000000000 : ℝ)^3211 := by
    have hnat : (338514419 : ℕ)^4235*100000000000000^3211 ≤ 44542252343189^3211*625000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338514419 625000000 44542252343189 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103230601/10000000000 : ℝ), (5242287817/10000000000 : ℝ), (338514419/625000000 : ℝ)] ![(2558485534571/20000000000000 : ℝ), (42665319976243/100000000000000 : ℝ), (44542252343189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103230601/10000000000 : ℝ)|^4235 ≤ (2558485534571/20000000000000 : ℝ)^3211
        have hw : |(-2103230601/10000000000 : ℝ)|=(2103230601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242287817/10000000000 : ℝ)|^4235 ≤ (42665319976243/100000000000000 : ℝ)^3211
        have hw : |(5242287817/10000000000 : ℝ)|=(5242287817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338514419/625000000 : ℝ)|^4235 ≤ (44542252343189/100000000000000 : ℝ)^3211
        have hw : |(338514419/625000000 : ℝ)|=(338514419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s5_5 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305456917/10000000000 : ℝ)*x 0 + (-504496239/2500000000 : ℝ)*x 1 + (5416231537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305456917/10000000000 : ℝ)^4235 ≤ (21672342607729/50000000000000 : ℝ)^3211 := by
    have hnat : (5305456917 : ℕ)^4235*50000000000000^3211 ≤ 21672342607729^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305456917 10000000000 21672342607729 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504496239/2500000000 : ℝ)^4235 ≤ (12113053378749/100000000000000 : ℝ)^3211 := by
    have hnat : (504496239 : ℕ)^4235*100000000000000^3211 ≤ 12113053378749^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504496239 2500000000 12113053378749 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416231537/10000000000 : ℝ)^4235 ≤ (11135565344573/25000000000000 : ℝ)^3211 := by
    have hnat : (5416231537 : ℕ)^4235*25000000000000^3211 ≤ 11135565344573^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416231537 10000000000 11135565344573 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305456917/10000000000 : ℝ), (-504496239/2500000000 : ℝ), (5416231537/10000000000 : ℝ)] ![(21672342607729/50000000000000 : ℝ), (12113053378749/100000000000000 : ℝ), (11135565344573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305456917/10000000000 : ℝ)|^4235 ≤ (21672342607729/50000000000000 : ℝ)^3211
        have hw : |(5305456917/10000000000 : ℝ)|=(5305456917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-504496239/2500000000 : ℝ)|^4235 ≤ (12113053378749/100000000000000 : ℝ)^3211
        have hw : |(-504496239/2500000000 : ℝ)|=(504496239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416231537/10000000000 : ℝ)|^4235 ≤ (11135565344573/25000000000000 : ℝ)^3211
        have hw : |(5416231537/10000000000 : ℝ)|=(5416231537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s5_6 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652728821/5000000000 : ℝ)*x 0 + (2708115487/5000000000 : ℝ)*x 1 + (-1008992371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652728821/5000000000 : ℝ)^4235 ≤ (43344693027493/100000000000000 : ℝ)^3211 := by
    have hnat : (2652728821 : ℕ)^4235*100000000000000^3211 ≤ 43344693027493^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652728821 5000000000 43344693027493 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708115487/5000000000 : ℝ)^4235 ≤ (22271127635867/50000000000000 : ℝ)^3211 := by
    have hnat : (2708115487 : ℕ)^4235*50000000000000^3211 ≤ 22271127635867^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708115487 5000000000 22271127635867 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008992371/5000000000 : ℝ)^4235 ≤ (12113051684557/100000000000000 : ℝ)^3211 := by
    have hnat : (1008992371 : ℕ)^4235*100000000000000^3211 ≤ 12113051684557^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008992371 5000000000 12113051684557 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652728821/5000000000 : ℝ), (2708115487/5000000000 : ℝ), (-1008992371/5000000000 : ℝ)] ![(43344693027493/100000000000000 : ℝ), (22271127635867/50000000000000 : ℝ), (12113051684557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652728821/5000000000 : ℝ)|^4235 ≤ (43344693027493/100000000000000 : ℝ)^3211
        have hw : |(2652728821/5000000000 : ℝ)|=(2652728821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708115487/5000000000 : ℝ)|^4235 ≤ (22271127635867/50000000000000 : ℝ)^3211
        have hw : |(2708115487/5000000000 : ℝ)|=(2708115487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008992371/5000000000 : ℝ)|^4235 ≤ (12113051684557/100000000000000 : ℝ)^3211
        have hw : |(-1008992371/5000000000 : ℝ)|=(1008992371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s5_7 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434442449/1000000000 : ℝ)*x 0 + (1131383677/2500000000 : ℝ)*x 1 + (4170361513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434442449/1000000000 : ℝ)^4235 ≤ (33301782832277/100000000000000 : ℝ)^3211 := by
    have hnat : (434442449 : ℕ)^4235*100000000000000^3211 ≤ 33301782832277^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434442449 1000000000 33301782832277 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131383677/2500000000 : ℝ)^4235 ≤ (219655332487/625000000000 : ℝ)^3211 := by
    have hnat : (1131383677 : ℕ)^4235*625000000000^3211 ≤ 219655332487^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131383677 2500000000 219655332487 625000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170361513/10000000000 : ℝ)^4235 ≤ (1577668197673/5000000000000 : ℝ)^3211 := by
    have hnat : (4170361513 : ℕ)^4235*5000000000000^3211 ≤ 1577668197673^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170361513 10000000000 1577668197673 5000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434442449/1000000000 : ℝ), (1131383677/2500000000 : ℝ), (4170361513/10000000000 : ℝ)] ![(33301782832277/100000000000000 : ℝ), (219655332487/625000000000 : ℝ), (1577668197673/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434442449/1000000000 : ℝ)|^4235 ≤ (33301782832277/100000000000000 : ℝ)^3211
        have hw : |(434442449/1000000000 : ℝ)|=(434442449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131383677/2500000000 : ℝ)|^4235 ≤ (219655332487/625000000000 : ℝ)^3211
        have hw : |(1131383677/2500000000 : ℝ)|=(1131383677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170361513/10000000000 : ℝ)|^4235 ≤ (1577668197673/5000000000000 : ℝ)^3211
        have hw : |(4170361513/10000000000 : ℝ)|=(4170361513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1275_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10969/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3669/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10901/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (10474876426820813/100000000000000000000 : ℝ) := by
    have hpowers : (10901/100000 : ℝ)^2117 ≤ (10474876426820813/100000000000000000000 : ℝ)^512 := by
      have hnat : (10901 : ℕ)^2117*100000000000000000000^512 ≤ 10474876426820813^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10901 100000 10474876426820813 100000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10901/100000 : ℝ)) (X := (10474876426820813/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14747/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (36541347040148519/100000000000000000000 : ℝ) := by
    have hpowers : (14747/100000 : ℝ)^2117 ≤ (36541347040148519/100000000000000000000 : ℝ)^512 := by
      have hnat : (14747 : ℕ)^2117*100000000000000000000^512 ≤ 36541347040148519^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14747 100000 36541347040148519 100000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14747/100000 : ℝ)) (X := (36541347040148519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010474876426820813/50000000000000000000 : ℝ) ≤ (5000253316526631/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50010474876426820813/50000000000000000000 : ℝ)^512 ≤ (5000253316526631/5000000000000000 : ℝ)^2117 := by
      have hnat : (50010474876426820813 : ℕ)^512*5000000000000000^2117 ≤ 5000253316526631^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010474876426820813 50000000000000000000 5000253316526631 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000253316526631/5000000000000000 : ℝ)) (X := (50010474876426820813/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011754055866742333/25000000000000000000 : ℝ) ≤ (10001136892644187/10000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (25011754055866742333/25000000000000000000 : ℝ)^512 ≤ (10001136892644187/10000000000000000 : ℝ)^2117 := by
      have hnat : (25011754055866742333 : ℕ)^512*10000000000000000^2117 ≤ 10001136892644187^2117*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011754055866742333 25000000000000000000 10001136892644187 10000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001136892644187/10000000000000000 : ℝ)) (X := (25011754055866742333/25000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036541347040148519/50000000000000000000 : ℝ) ≤ (1250220894029389/1250000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50036541347040148519/50000000000000000000 : ℝ)^512 ≤ (1250220894029389/1250000000000000 : ℝ)^2117 := by
      have hnat : (50036541347040148519 : ℕ)^512*1250000000000000^2117 ≤ 1250220894029389^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036541347040148519 50000000000000000000 1250220894029389 1250000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250220894029389/1250000000000000 : ℝ)) (X := (50036541347040148519/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10474876426820813/100000000000000000000 : ℝ) ≤ ((19224103795560749401/19230000000000000000 : ℝ)+2*(25210383637/15384000000000 : ℝ)*(10901/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (19224103795560749401/19230000000000000000 : ℝ)+2*(25210383637/15384000000000 : ℝ)*(10901/100000 : ℝ)=(5000253316526631/5000000000000000 : ℝ) by norm_num, show 1+2*(10474876426820813/100000000000000000000 : ℝ)=(50010474876426820813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36541347040148519/100000000000000000000 : ℝ)+(10474876426820813/100000000000000000000 : ℝ) ≤ ((19224103795560749401/19230000000000000000 : ℝ)+(25210383637/15384000000000 : ℝ)*((14747/100000 : ℝ)+(10901/100000 : ℝ)))^(2117/512 : ℝ) := by
    rw [show (19224103795560749401/19230000000000000000 : ℝ)+(25210383637/15384000000000 : ℝ)*((14747/100000 : ℝ)+(10901/100000 : ℝ))=(10001136892644187/10000000000000000 : ℝ) by norm_num, show 1+(36541347040148519/100000000000000000000 : ℝ)+(10474876426820813/100000000000000000000 : ℝ)=(25011754055866742333/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36541347040148519/100000000000000000000 : ℝ) ≤ ((19224103795560749401/19230000000000000000 : ℝ)+2*(25210383637/15384000000000 : ℝ)*(14747/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (19224103795560749401/19230000000000000000 : ℝ)+2*(25210383637/15384000000000 : ℝ)*(14747/100000 : ℝ)=(1250220894029389/1250000000000000 : ℝ) by norm_num, show 1+2*(36541347040148519/100000000000000000000 : ℝ)=(50036541347040148519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19224103795560749401/19230000000000000000 : ℝ)*(X 1 0+X 2 0)+(25210383637/15384000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (10901/100000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (19224103795560749401/19230000000000000000 : ℝ)) (alpha := (25210383637/15384000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19224103795560749401/19230000000000000000 : ℝ)*(X 0 1+X 2 1)+(25210383637/15384000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (10901/100000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (19224103795560749401/19230000000000000000 : ℝ)) (alpha := (25210383637/15384000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19224103795560749401/19230000000000000000 : ℝ)*(X 0 2+X 1 2)+(25210383637/15384000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (10901/100000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (19224103795560749401/19230000000000000000 : ℝ)) (alpha := (25210383637/15384000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-210321751/1000000000 : ℝ)*X 0 0+(5416862767/10000000000 : ℝ)*X 0 1+(2620829449/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070043311/2000000000 : ℝ)*X 1 0+(-1096278367/5000000000 : ℝ)*X 1 1+(1048331783/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350216613/10000000000 : ℝ)*X 2 0+(5241658917/10000000000 : ℝ)*X 2 1+(-2192556653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4344397839/10000000000 : ℝ)*X 0 0+(833814081/2000000000 : ℝ)*X 0 1+(141463087/312500000 : ℝ)*X 0 2+(4344397839/10000000000 : ℝ)*X 1 0+(833814081/2000000000 : ℝ)*X 1 1+(141463087/312500000 : ℝ)*X 1 2+(4344397839/10000000000 : ℝ)*X 2 0+(833814081/2000000000 : ℝ)*X 2 1+(141463087/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2103230601/10000000000 : ℝ)*X 0 0+(5242287817/10000000000 : ℝ)*X 0 1+(338514419/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305456917/10000000000 : ℝ)*X 1 0+(-504496239/2500000000 : ℝ)*X 1 1+(5416231537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652728821/5000000000 : ℝ)*X 2 0+(2708115487/5000000000 : ℝ)*X 2 1+(-1008992371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434442449/1000000000 : ℝ)*X 0 0+(1131383677/2500000000 : ℝ)*X 0 1+(4170361513/10000000000 : ℝ)*X 0 2+(434442449/1000000000 : ℝ)*X 1 0+(1131383677/2500000000 : ℝ)*X 1 1+(4170361513/10000000000 : ℝ)*X 1 2+(434442449/1000000000 : ℝ)*X 2 0+(1131383677/2500000000 : ℝ)*X 2 1+(4170361513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14485712949666487015616703/10015625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (486854679/100000000000000 : ℝ)*(base19) + (524099111/100000000000000 : ℝ)*(base23) + (2635557/20000000000000 : ℝ)*(lower2) + (92865233/100000000000000 : ℝ)*(upper3) + (90242347/50000000000000 : ℝ)*(upper5) + (66429067278687/1562500000000 : ℝ)*(major0) + (66429067278687/1562500000000 : ℝ)*(major1) + (66429067278687/1562500000000 : ℝ)*(major2) + (1426910258601091/25000000000000 : ℝ)*(sp0) + (2853824527034231/50000000000000 : ℝ)*(sp1) + (570764901682403/10000000000000 : ℝ)*(sp2) + (698816582656959/25000000000000 : ℝ)*(sp3) + (8506518777/100000000000000 : ℝ)*(sp4) + (4691910567/100000000000000 : ℝ)*(sp7) + (698817755634601/25000000000000 : ℝ)*(f.failure) + (5707649540923141/100000000000000 : ℝ)*(f.sum) + (2057695741183/641000000000000000000000000 : ℝ)*base65 + (26385546429935713/1251953125000000000000000000000 : ℝ)*base67 + (31485496853789727/5007812500000000000000000000000 : ℝ)*base69 + (165827641807126329/10015625000000000000000000000000 : ℝ)*base71 + (1214939777163/160250000000000000000000000 : ℝ)*base73 + (45709300993887051/2503906250000000000000000000000 : ℝ)*base75 + (2494612288688829/10015625000000000000000000000000 : ℝ)*base77 + (63387750363970079/10015625000000000000000000000000 : ℝ)*base79 + (66983226369/25640000000000000000000000 : ℝ)*base82 + (420357/312500000000000000000 : ℝ)*base90 + (420357/312500000000000000000 : ℝ)*base92 + (420357/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56650321642256351203858451/8012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69708193/100000000000000 : ℝ)*(base23) + (50504073/25000000000000 : ℝ)*(lower2) + (191571503/100000000000000 : ℝ)*(upper3) + (42939493/25000000000000 : ℝ)*(upper4) + (121062381/100000000000000 : ℝ)*(upper5) + (107056992025517/2500000000000 : ℝ)*(major0) + (107056992025517/2500000000000 : ℝ)*(major1) + (107056992025517/2500000000000 : ℝ)*(major2) + (16458609797/100000000000000 : ℝ)*(sp1) + (15107919529/100000000000000 : ℝ)*(sp2) + (5749024829520219/100000000000000 : ℝ)*(sp4) + (2874504185455211/50000000000000 : ℝ)*(sp5) + (5749009651892497/100000000000000 : ℝ)*(sp6) + (1407767148423183/50000000000000 : ℝ)*(sp7) + (1407767148423183/50000000000000 : ℝ)*(f.failure) + (5749024829520219/100000000000000 : ℝ)*(f.sum) + (36297666983417/1923000000000000000000000000 : ℝ)*base65 + (248886132527036561/16025000000000000000000000000000 : ℝ)*base68 + (384732827977111561/16025000000000000000000000000000 : ℝ)*base70 + (19234078559986561/16025000000000000000000000000000 : ℝ)*base72 + (3482469468677/961500000000000000000000000 : ℝ)*base74 + (164439792182436561/16025000000000000000000000000000 : ℝ)*base76 + (206921587458036561/16025000000000000000000000000000 : ℝ)*base78 + (95879757001236561/16025000000000000000000000000000 : ℝ)*base80 + (5715096439019/1923000000000000000000000000 : ℝ)*base81 + (2756269/625000000000000000000 : ℝ)*base89 + (2756269/625000000000000000000 : ℝ)*base91 + (2756269/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1275_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1275_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1275_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1275_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1275_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1275_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1275_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
