-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1156_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:37:57.570989+00:00
-- url     : https://prove2.me/submissions/7dd57c3c-64d3-4719-a744-c4c11acc6bad

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
theorem support_rectangle_w1156_s9_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344692509/10000000000 : ℝ)*x 0 + (329125789/625000000 : ℝ)*x 1 + (-222448021/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344692509/10000000000 : ℝ)^8349 ≤ (43600357809799/100000000000000 : ℝ)^6301 := by
    have hnat : (5344692509 : ℕ)^8349*100000000000000^6301 ≤ 43600357809799^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344692509 10000000000 43600357809799 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329125789/625000000 : ℝ)^8349 ≤ (42751935049847/100000000000000 : ℝ)^6301 := by
    have hnat : (329125789 : ℕ)^8349*100000000000000^6301 ≤ 42751935049847^6301*625000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329125789 625000000 42751935049847 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222448021/1000000000 : ℝ)^8349 ≤ (13647707132047/100000000000000 : ℝ)^6301 := by
    have hnat : (222448021 : ℕ)^8349*100000000000000^6301 ≤ 13647707132047^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222448021 1000000000 13647707132047 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344692509/10000000000 : ℝ), (329125789/625000000 : ℝ), (-222448021/1000000000 : ℝ)] ![(43600357809799/100000000000000 : ℝ), (42751935049847/100000000000000 : ℝ), (13647707132047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344692509/10000000000 : ℝ)|^8349 ≤ (43600357809799/100000000000000 : ℝ)^6301
        have hw : |(5344692509/10000000000 : ℝ)|=(5344692509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329125789/625000000 : ℝ)|^8349 ≤ (42751935049847/100000000000000 : ℝ)^6301
        have hw : |(329125789/625000000 : ℝ)|=(329125789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222448021/1000000000 : ℝ)|^8349 ≤ (13647707132047/100000000000000 : ℝ)^6301
        have hw : |(-222448021/1000000000 : ℝ)|=(222448021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s9_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181353529/5000000000 : ℝ)*x 0 + (4238127001/10000000000 : ℝ)*x 1 + (2245459679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181353529/5000000000 : ℝ)^8349 ≤ (33317067163881/100000000000000 : ℝ)^6301 := by
    have hnat : (2181353529 : ℕ)^8349*100000000000000^6301 ≤ 33317067163881^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181353529 5000000000 33317067163881 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238127001/10000000000 : ℝ)^8349 ≤ (3206233528429/10000000000000 : ℝ)^6301 := by
    have hnat : (4238127001 : ℕ)^8349*10000000000000^6301 ≤ 3206233528429^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238127001 10000000000 3206233528429 10000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245459679/5000000000 : ℝ)^8349 ≤ (2163787345513/6250000000000 : ℝ)^6301 := by
    have hnat : (2245459679 : ℕ)^8349*6250000000000^6301 ≤ 2163787345513^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245459679 5000000000 2163787345513 6250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181353529/5000000000 : ℝ), (4238127001/10000000000 : ℝ), (2245459679/5000000000 : ℝ)] ![(33317067163881/100000000000000 : ℝ), (3206233528429/10000000000000 : ℝ), (2163787345513/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181353529/5000000000 : ℝ)|^8349 ≤ (33317067163881/100000000000000 : ℝ)^6301
        have hw : |(2181353529/5000000000 : ℝ)|=(2181353529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238127001/10000000000 : ℝ)|^8349 ≤ (3206233528429/10000000000000 : ℝ)^6301
        have hw : |(4238127001/10000000000 : ℝ)|=(4238127001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245459679/5000000000 : ℝ)|^8349 ≤ (2163787345513/6250000000000 : ℝ)^6301
        have hw : |(2245459679/5000000000 : ℝ)|=(2245459679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s9_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160216031/10000000000 : ℝ)*x 0 + (1053266229/2000000000 : ℝ)*x 1 + (84256403/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160216031/10000000000 : ℝ)^8349 ≤ (13127749662609/100000000000000 : ℝ)^6301 := by
    have hnat : (2160216031 : ℕ)^8349*100000000000000^6301 ≤ 13127749662609^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160216031 10000000000 13127749662609 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053266229/2000000000 : ℝ)^8349 ≤ (42755361474623/100000000000000 : ℝ)^6301 := by
    have hnat : (1053266229 : ℕ)^8349*100000000000000^6301 ≤ 42755361474623^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053266229 2000000000 42755361474623 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84256403/156250000 : ℝ)^8349 ≤ (44116888853851/100000000000000 : ℝ)^6301 := by
    have hnat : (84256403 : ℕ)^8349*100000000000000^6301 ≤ 44116888853851^6301*156250000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84256403 156250000 44116888853851 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160216031/10000000000 : ℝ), (1053266229/2000000000 : ℝ), (84256403/156250000 : ℝ)] ![(13127749662609/100000000000000 : ℝ), (42755361474623/100000000000000 : ℝ), (44116888853851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160216031/10000000000 : ℝ)|^8349 ≤ (13127749662609/100000000000000 : ℝ)^6301
        have hw : |(-2160216031/10000000000 : ℝ)|=(2160216031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053266229/2000000000 : ℝ)|^8349 ≤ (42755361474623/100000000000000 : ℝ)^6301
        have hw : |(1053266229/2000000000 : ℝ)|=(1053266229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84256403/156250000 : ℝ)|^8349 ≤ (44116888853851/100000000000000 : ℝ)^6301
        have hw : |(84256403/156250000 : ℝ)|=(84256403/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s9_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328138799/2500000000 : ℝ)*x 0 + (-524520733/2500000000 : ℝ)*x 1 + (2696204881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328138799/2500000000 : ℝ)^8349 ≤ (8650664014547/20000000000000 : ℝ)^6301 := by
    have hnat : (1328138799 : ℕ)^8349*20000000000000^6301 ≤ 8650664014547^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328138799 2500000000 8650664014547 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524520733/2500000000 : ℝ)^8349 ≤ (6314895691599/50000000000000 : ℝ)^6301 := by
    have hnat : (524520733 : ℕ)^8349*50000000000000^6301 ≤ 6314895691599^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524520733 2500000000 6314895691599 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696204881/5000000000 : ℝ)^8349 ≤ (22058444264319/50000000000000 : ℝ)^6301 := by
    have hnat : (2696204881 : ℕ)^8349*50000000000000^6301 ≤ 22058444264319^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696204881 5000000000 22058444264319 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328138799/2500000000 : ℝ), (-524520733/2500000000 : ℝ), (2696204881/5000000000 : ℝ)] ![(8650664014547/20000000000000 : ℝ), (6314895691599/50000000000000 : ℝ), (22058444264319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328138799/2500000000 : ℝ)|^8349 ≤ (8650664014547/20000000000000 : ℝ)^6301
        have hw : |(1328138799/2500000000 : ℝ)|=(1328138799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524520733/2500000000 : ℝ)|^8349 ≤ (6314895691599/50000000000000 : ℝ)^6301
        have hw : |(-524520733/2500000000 : ℝ)|=(524520733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696204881/5000000000 : ℝ)|^8349 ≤ (22058444264319/50000000000000 : ℝ)^6301
        have hw : |(2696204881/5000000000 : ℝ)|=(2696204881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s9_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664069449/1250000000 : ℝ)*x 0 + (5392409861/10000000000 : ℝ)*x 1 + (-1049041131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664069449/1250000000 : ℝ)^8349 ≤ (43253324344783/100000000000000 : ℝ)^6301 := by
    have hnat : (664069449 : ℕ)^8349*100000000000000^6301 ≤ 43253324344783^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664069449 1250000000 43253324344783 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392409861/10000000000 : ℝ)^8349 ≤ (22058444800921/50000000000000 : ℝ)^6301 := by
    have hnat : (5392409861 : ℕ)^8349*50000000000000^6301 ≤ 22058444800921^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392409861 10000000000 22058444800921 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049041131/5000000000 : ℝ)^8349 ≤ (6314893019557/50000000000000 : ℝ)^6301 := by
    have hnat : (1049041131 : ℕ)^8349*50000000000000^6301 ≤ 6314893019557^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049041131 5000000000 6314893019557 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664069449/1250000000 : ℝ), (5392409861/10000000000 : ℝ), (-1049041131/5000000000 : ℝ)] ![(43253324344783/100000000000000 : ℝ), (22058444800921/50000000000000 : ℝ), (6314893019557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664069449/1250000000 : ℝ)|^8349 ≤ (43253324344783/100000000000000 : ℝ)^6301
        have hw : |(664069449/1250000000 : ℝ)|=(664069449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392409861/10000000000 : ℝ)|^8349 ≤ (22058444800921/50000000000000 : ℝ)^6301
        have hw : |(5392409861/10000000000 : ℝ)|=(5392409861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1049041131/5000000000 : ℝ)|^8349 ≤ (6314893019557/50000000000000 : ℝ)^6301
        have hw : |(-1049041131/5000000000 : ℝ)|=(1049041131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s9_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362717123/10000000000 : ℝ)*x 0 + (4490284033/10000000000 : ℝ)*x 1 + (2119382107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362717123/10000000000 : ℝ)^8349 ≤ (4164646126401/12500000000000 : ℝ)^6301 := by
    have hnat : (4362717123 : ℕ)^8349*12500000000000^6301 ≤ 4164646126401^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362717123 10000000000 4164646126401 12500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490284033/10000000000 : ℝ)^8349 ≤ (34614108043043/100000000000000 : ℝ)^6301 := by
    have hnat : (4490284033 : ℕ)^8349*100000000000000^6301 ≤ 34614108043043^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490284033 10000000000 34614108043043 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119382107/5000000000 : ℝ)^8349 ≤ (16034361469299/50000000000000 : ℝ)^6301 := by
    have hnat : (2119382107 : ℕ)^8349*50000000000000^6301 ≤ 16034361469299^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119382107 5000000000 16034361469299 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362717123/10000000000 : ℝ), (4490284033/10000000000 : ℝ), (2119382107/5000000000 : ℝ)] ![(4164646126401/12500000000000 : ℝ), (34614108043043/100000000000000 : ℝ), (16034361469299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362717123/10000000000 : ℝ)|^8349 ≤ (4164646126401/12500000000000 : ℝ)^6301
        have hw : |(4362717123/10000000000 : ℝ)|=(4362717123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490284033/10000000000 : ℝ)|^8349 ≤ (34614108043043/100000000000000 : ℝ)^6301
        have hw : |(4490284033/10000000000 : ℝ)|=(4490284033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119382107/5000000000 : ℝ)|^8349 ≤ (16034361469299/50000000000000 : ℝ)^6301
        have hw : |(2119382107/5000000000 : ℝ)|=(2119382107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2843/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1757/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2843/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2843/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2843/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2843/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2843/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2843/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2843/25000 : ℝ) ^ (2087/512 : ℝ) ≤ (14171921129692633/100000000000000000000 : ℝ) := by
    have hpowers : (2843/25000 : ℝ)^2087 ≤ (14171921129692633/100000000000000000000 : ℝ)^512 := by
      have hnat : (2843 : ℕ)^2087*100000000000000000000^512 ≤ 14171921129692633^512*25000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2843 25000 14171921129692633 100000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2843/25000 : ℝ)) (X := (14171921129692633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14057/100000 : ℝ) ^ (2087/512 : ℝ) ≤ (420314117570203/1250000000000000000 : ℝ) := by
    have hpowers : (14057/100000 : ℝ)^2087 ≤ (420314117570203/1250000000000000000 : ℝ)^512 := by
      have hnat : (14057 : ℕ)^2087*1250000000000000000^512 ≤ 420314117570203^512*100000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14057 100000 420314117570203 1250000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14057/100000 : ℝ)) (X := (420314117570203/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014171921129692633/50000000000000000000 : ℝ) ≤ (250017382002167/250000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (50014171921129692633/50000000000000000000 : ℝ)^512 ≤ (250017382002167/250000000000000 : ℝ)^2087 := by
      have hnat : (50014171921129692633 : ℕ)^512*250000000000000^2087 ≤ 250017382002167^2087*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014171921129692633 50000000000000000000 250017382002167 250000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250017382002167/250000000000000 : ℝ)) (X := (50014171921129692633/50000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047797050535308873/100000000000000000000 : ℝ) ≤ (10001172385118993/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (100047797050535308873/100000000000000000000 : ℝ)^512 ≤ (10001172385118993/10000000000000000 : ℝ)^2087 := by
      have hnat : (100047797050535308873 : ℕ)^512*10000000000000000^2087 ≤ 10001172385118993^2087*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047797050535308873 100000000000000000000 10001172385118993 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001172385118993/10000000000000000 : ℝ)) (X := (100047797050535308873/100000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (625420314117570203/625000000000000000 : ℝ) ≤ (5000824745075653/5000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (625420314117570203/625000000000000000 : ℝ)^512 ≤ (5000824745075653/5000000000000000 : ℝ)^2087 := by
      have hnat : (625420314117570203 : ℕ)^512*5000000000000000^2087 ≤ 5000824745075653^2087*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625420314117570203 625000000000000000 5000824745075653 5000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000824745075653/5000000000000000 : ℝ)) (X := (625420314117570203/625000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14171921129692633/100000000000000000000 : ℝ) ≤ ((279593911981018843/279687500000000000 : ℝ)+2*(159035010771/89500000000000 : ℝ)*(2843/25000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (279593911981018843/279687500000000000 : ℝ)+2*(159035010771/89500000000000 : ℝ)*(2843/25000 : ℝ)=(250017382002167/250000000000000 : ℝ) by norm_num, show 1+2*(14171921129692633/100000000000000000000 : ℝ)=(50014171921129692633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(420314117570203/1250000000000000000 : ℝ)+(14171921129692633/100000000000000000000 : ℝ) ≤ ((279593911981018843/279687500000000000 : ℝ)+(159035010771/89500000000000 : ℝ)*((14057/100000 : ℝ)+(2843/25000 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (279593911981018843/279687500000000000 : ℝ)+(159035010771/89500000000000 : ℝ)*((14057/100000 : ℝ)+(2843/25000 : ℝ))=(10001172385118993/10000000000000000 : ℝ) by norm_num, show 1+(420314117570203/1250000000000000000 : ℝ)+(14171921129692633/100000000000000000000 : ℝ)=(100047797050535308873/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(420314117570203/1250000000000000000 : ℝ) ≤ ((279593911981018843/279687500000000000 : ℝ)+2*(159035010771/89500000000000 : ℝ)*(14057/100000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (279593911981018843/279687500000000000 : ℝ)+2*(159035010771/89500000000000 : ℝ)*(14057/100000 : ℝ)=(5000824745075653/5000000000000000 : ℝ) by norm_num, show 1+2*(420314117570203/1250000000000000000 : ℝ)=(625420314117570203/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (279593911981018843/279687500000000000 : ℝ)*(X 1 0+X 2 0)+(159035010771/89500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (279593911981018843/279687500000000000 : ℝ)) (alpha := (159035010771/89500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (279593911981018843/279687500000000000 : ℝ)*(X 0 1+X 2 1)+(159035010771/89500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (279593911981018843/279687500000000000 : ℝ)) (alpha := (159035010771/89500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (279593911981018843/279687500000000000 : ℝ)*(X 0 2+X 1 2)+(159035010771/89500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (279593911981018843/279687500000000000 : ℝ)) (alpha := (159035010771/89500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5344692509/10000000000 : ℝ)*X 2 0+(329125789/625000000 : ℝ)*X 2 1+(-222448021/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2181353529/5000000000 : ℝ)*X 0 0+(4238127001/10000000000 : ℝ)*X 0 1+(2245459679/5000000000 : ℝ)*X 0 2+(2181353529/5000000000 : ℝ)*X 1 0+(4238127001/10000000000 : ℝ)*X 1 1+(2245459679/5000000000 : ℝ)*X 1 2+(2181353529/5000000000 : ℝ)*X 2 0+(4238127001/10000000000 : ℝ)*X 2 1+(2245459679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s9_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-2160216031/10000000000 : ℝ)*X 0 0+(1053266229/2000000000 : ℝ)*X 0 1+(84256403/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1328138799/2500000000 : ℝ)*X 1 0+(-524520733/2500000000 : ℝ)*X 1 1+(2696204881/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((664069449/1250000000 : ℝ)*X 2 0+(5392409861/10000000000 : ℝ)*X 2 1+(-1049041131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4362717123/10000000000 : ℝ)*X 0 0+(4490284033/10000000000 : ℝ)*X 0 1+(2119382107/5000000000 : ℝ)*X 0 2+(4362717123/10000000000 : ℝ)*X 1 0+(4490284033/10000000000 : ℝ)*X 1 1+(2119382107/5000000000 : ℝ)*X 1 2+(4362717123/10000000000 : ℝ)*X 2 0+(4490284033/10000000000 : ℝ)*X 2 1+(2119382107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7856658129549065863739619/6992187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (10651357/3125000000000 : ℝ)*(base19) + (1629920979/100000000000000 : ℝ)*(base23) + (550561/3125000000000 : ℝ)*(lower2) + (133252017/100000000000000 : ℝ)*(upper3) + (188846159/100000000000000 : ℝ)*(lower4) + (5953697323811401/100000000000000 : ℝ)*(major0) + (5953697323811401/100000000000000 : ℝ)*(major1) + (5953697323811401/100000000000000 : ℝ)*(major2) + (31040909321/50000000000000 : ℝ)*(sp0) + (814835677/50000000000000 : ℝ)*(sp1) + (158631110577381/2000000000000 : ℝ)*(sp2) + (7931555188025627/100000000000000 : ℝ)*(sp3) + (7931491817129429/100000000000000 : ℝ)*(sp4) + (3975837451627931/100000000000000 : ℝ)*(sp5) + (795167816259857/20000000000000 : ℝ)*(f.failure) + (158631110577381/2000000000000 : ℝ)*(f.sum) + (6220317332477/2237500000000000000000000000 : ℝ)*base66 + (52328172761904021/3496093750000000000000000000000 : ℝ)*base67 + (58084929267850459/13984375000000000000000000000000 : ℝ)*base69 + (14553831453886167/6992187500000000000000000000000 : ℝ)*base71 + (807039226187/559375000000000000000000000 : ℝ)*base73 + (21232840350194209/13984375000000000000000000000000 : ℝ)*base75 + (11767082292060271/3496093750000000000000000000000 : ℝ)*base77 + (255994300646600459/13984375000000000000000000000000 : ℝ)*base79 + (4851077452871/4475000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5672277/2000000000000000000000 : ℝ)*base90 + (5672277/2000000000000000000000 : ℝ)*base92 + (5672277/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1156_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1156_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1156_box_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-406756903/2000000000 : ℝ)*x 0 + (5376107257/10000000000 : ℝ)*x 1 + (5376107101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406756903/2000000000 : ℝ)^8349 ≤ (6059751771069/50000000000000 : ℝ)^6301 := by
    have hnat : (406756903 : ℕ)^8349*50000000000000^6301 ≤ 6059751771069^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406756903 2000000000 6059751771069 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376107257/10000000000 : ℝ)^8349 ≤ (43940249064689/100000000000000 : ℝ)^6301 := by
    have hnat : (5376107257 : ℕ)^8349*100000000000000^6301 ≤ 43940249064689^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376107257 10000000000 43940249064689 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376107101/10000000000 : ℝ)^8349 ≤ (43940247375243/100000000000000 : ℝ)^6301 := by
    have hnat : (5376107101 : ℕ)^8349*100000000000000^6301 ≤ 43940247375243^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376107101 10000000000 43940247375243 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-406756903/2000000000 : ℝ), (5376107257/10000000000 : ℝ), (5376107101/10000000000 : ℝ)] ![(6059751771069/50000000000000 : ℝ), (43940249064689/100000000000000 : ℝ), (43940247375243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-406756903/2000000000 : ℝ)|^8349 ≤ (6059751771069/50000000000000 : ℝ)^6301
        have hw : |(-406756903/2000000000 : ℝ)|=(406756903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376107257/10000000000 : ℝ)|^8349 ≤ (43940249064689/100000000000000 : ℝ)^6301
        have hw : |(5376107257/10000000000 : ℝ)|=(5376107257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376107101/10000000000 : ℝ)|^8349 ≤ (43940247375243/100000000000000 : ℝ)^6301
        have hw : |(5376107101/10000000000 : ℝ)|=(5376107101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171986/9765625 : ℝ)*x 0 + (-2142304881/10000000000 : ℝ)*x 1 + (1075221337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171986/9765625 : ℝ)^8349 ≤ (43076038082251/100000000000000 : ℝ)^6301 := by
    have hnat : (5171986 : ℕ)^8349*100000000000000^6301 ≤ 43076038082251^6301*9765625^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171986 9765625 43076038082251 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142304881/10000000000 : ℝ)^8349 ≤ (12983719030407/100000000000000 : ℝ)^6301 := by
    have hnat : (2142304881 : ℕ)^8349*100000000000000^6301 ≤ 12983719030407^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142304881 10000000000 12983719030407 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075221337/2000000000 : ℝ)^8349 ≤ (8788048574011/20000000000000 : ℝ)^6301 := by
    have hnat : (1075221337 : ℕ)^8349*20000000000000^6301 ≤ 8788048574011^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075221337 2000000000 8788048574011 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171986/9765625 : ℝ), (-2142304881/10000000000 : ℝ), (1075221337/2000000000 : ℝ)] ![(43076038082251/100000000000000 : ℝ), (12983719030407/100000000000000 : ℝ), (8788048574011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171986/9765625 : ℝ)|^8349 ≤ (43076038082251/100000000000000 : ℝ)^6301
        have hw : |(5171986/9765625 : ℝ)|=(5171986/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142304881/10000000000 : ℝ)|^8349 ≤ (12983719030407/100000000000000 : ℝ)^6301
        have hw : |(-2142304881/10000000000 : ℝ)|=(2142304881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075221337/2000000000 : ℝ)|^8349 ≤ (8788048574011/20000000000000 : ℝ)^6301
        have hw : |(1075221337/2000000000 : ℝ)|=(1075221337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059222609/2000000000 : ℝ)*x 0 + (2688053523/5000000000 : ℝ)*x 1 + (-85692209/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059222609/2000000000 : ℝ)^8349 ≤ (43076031411203/100000000000000 : ℝ)^6301 := by
    have hnat : (1059222609 : ℕ)^8349*100000000000000^6301 ≤ 43076031411203^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059222609 2000000000 43076031411203 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688053523/5000000000 : ℝ)^8349 ≤ (8788049355921/20000000000000 : ℝ)^6301 := by
    have hnat : (2688053523 : ℕ)^8349*20000000000000^6301 ≤ 8788049355921^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688053523 5000000000 8788049355921 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85692209/400000000 : ℝ)^8349 ≤ (12983721792901/100000000000000 : ℝ)^6301 := by
    have hnat : (85692209 : ℕ)^8349*100000000000000^6301 ≤ 12983721792901^6301*400000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85692209 400000000 12983721792901 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059222609/2000000000 : ℝ), (2688053523/5000000000 : ℝ), (-85692209/400000000 : ℝ)] ![(43076031411203/100000000000000 : ℝ), (8788049355921/20000000000000 : ℝ), (12983721792901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059222609/2000000000 : ℝ)|^8349 ≤ (43076031411203/100000000000000 : ℝ)^6301
        have hw : |(1059222609/2000000000 : ℝ)|=(1059222609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688053523/5000000000 : ℝ)|^8349 ≤ (8788049355921/20000000000000 : ℝ)^6301
        have hw : |(2688053523/5000000000 : ℝ)|=(2688053523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85692209/400000000 : ℝ)|^8349 ≤ (12983721792901/100000000000000 : ℝ)^6301
        have hw : |(-85692209/400000000 : ℝ)|=(85692209/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4470099413/10000000000 : ℝ)*x 0 + (4311108759/10000000000 : ℝ)*x 1 + (134722167/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4470099413/10000000000 : ℝ)^8349 ≤ (34408089083897/100000000000000 : ℝ)^6301 := by
    have hnat : (4470099413 : ℕ)^8349*100000000000000^6301 ≤ 34408089083897^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4470099413 10000000000 34408089083897 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4311108759/10000000000 : ℝ)^8349 ≤ (16397976250881/50000000000000 : ℝ)^6301 := by
    have hnat : (4311108759 : ℕ)^8349*50000000000000^6301 ≤ 16397976250881^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311108759 10000000000 16397976250881 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134722167/312500000 : ℝ)^8349 ≤ (4099494799813/12500000000000 : ℝ)^6301 := by
    have hnat : (134722167 : ℕ)^8349*12500000000000^6301 ≤ 4099494799813^6301*312500000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134722167 312500000 4099494799813 12500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4470099413/10000000000 : ℝ), (4311108759/10000000000 : ℝ), (134722167/312500000 : ℝ)] ![(34408089083897/100000000000000 : ℝ), (16397976250881/50000000000000 : ℝ), (4099494799813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4470099413/10000000000 : ℝ)|^8349 ≤ (34408089083897/100000000000000 : ℝ)^6301
        have hw : |(4470099413/10000000000 : ℝ)|=(4470099413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4311108759/10000000000 : ℝ)|^8349 ≤ (16397976250881/50000000000000 : ℝ)^6301
        have hw : |(4311108759/10000000000 : ℝ)|=(4311108759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134722167/312500000 : ℝ)|^8349 ≤ (4099494799813/12500000000000 : ℝ)^6301
        have hw : |(134722167/312500000 : ℝ)|=(134722167/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-45760551/200000000 : ℝ)*x 0 + (5281318203/10000000000 : ℝ)*x 1 + (2640658879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45760551/200000000 : ℝ)^8349 ≤ (3541672295997/25000000000000 : ℝ)^6301 := by
    have hnat : (45760551 : ℕ)^8349*25000000000000^6301 ≤ 3541672295997^6301*200000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45760551 200000000 3541672295997 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281318203/10000000000 : ℝ)^8349 ≤ (42916657798123/100000000000000 : ℝ)^6301 := by
    have hnat : (5281318203 : ℕ)^8349*100000000000000^6301 ≤ 42916657798123^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281318203 10000000000 42916657798123 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640658879/5000000000 : ℝ)^8349 ≤ (8583330601331/20000000000000 : ℝ)^6301 := by
    have hnat : (2640658879 : ℕ)^8349*20000000000000^6301 ≤ 8583330601331^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640658879 5000000000 8583330601331 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45760551/200000000 : ℝ), (5281318203/10000000000 : ℝ), (2640658879/5000000000 : ℝ)] ![(3541672295997/25000000000000 : ℝ), (42916657798123/100000000000000 : ℝ), (8583330601331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45760551/200000000 : ℝ)|^8349 ≤ (3541672295997/25000000000000 : ℝ)^6301
        have hw : |(-45760551/200000000 : ℝ)|=(45760551/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281318203/10000000000 : ℝ)|^8349 ≤ (42916657798123/100000000000000 : ℝ)^6301
        have hw : |(5281318203/10000000000 : ℝ)|=(5281318203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640658879/5000000000 : ℝ)|^8349 ≤ (8583330601331/20000000000000 : ℝ)^6301
        have hw : |(2640658879/5000000000 : ℝ)|=(2640658879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072612109/2000000000 : ℝ)*x 0 + (-108981691/500000000 : ℝ)*x 1 + (5281317791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072612109/2000000000 : ℝ)^8349 ≤ (43799011819273/100000000000000 : ℝ)^6301 := by
    have hnat : (1072612109 : ℕ)^8349*100000000000000^6301 ≤ 43799011819273^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072612109 2000000000 43799011819273 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108981691/500000000 : ℝ)^8349 ≤ (415135462551/3125000000000 : ℝ)^6301 := by
    have hnat : (108981691 : ℕ)^8349*3125000000000^6301 ≤ 415135462551^6301*500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108981691 500000000 415135462551 3125000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281317791/10000000000 : ℝ)^8349 ≤ (21458326680989/50000000000000 : ℝ)^6301 := by
    have hnat : (5281317791 : ℕ)^8349*50000000000000^6301 ≤ 21458326680989^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281317791 10000000000 21458326680989 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072612109/2000000000 : ℝ), (-108981691/500000000 : ℝ), (5281317791/10000000000 : ℝ)] ![(43799011819273/100000000000000 : ℝ), (415135462551/3125000000000 : ℝ), (21458326680989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072612109/2000000000 : ℝ)|^8349 ≤ (43799011819273/100000000000000 : ℝ)^6301
        have hw : |(1072612109/2000000000 : ℝ)|=(1072612109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108981691/500000000 : ℝ)|^8349 ≤ (415135462551/3125000000000 : ℝ)^6301
        have hw : |(-108981691/500000000 : ℝ)|=(108981691/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281317791/10000000000 : ℝ)|^8349 ≤ (21458326680989/50000000000000 : ℝ)^6301
        have hw : |(5281317791/10000000000 : ℝ)|=(5281317791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_6 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167595641/312500000 : ℝ)*x 0 + (5281318077/10000000000 : ℝ)*x 1 + (-2179633483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167595641/312500000 : ℝ)^8349 ≤ (10949752865543/25000000000000 : ℝ)^6301 := by
    have hnat : (167595641 : ℕ)^8349*25000000000000^6301 ≤ 10949752865543^6301*312500000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167595641 312500000 10949752865543 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281318077/10000000000 : ℝ)^8349 ≤ (21458328220719/50000000000000 : ℝ)^6301 := by
    have hnat : (5281318077 : ℕ)^8349*50000000000000^6301 ≤ 21458328220719^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281318077 10000000000 21458328220719 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179633483/10000000000 : ℝ)^8349 ≤ (6642166040057/50000000000000 : ℝ)^6301 := by
    have hnat : (2179633483 : ℕ)^8349*50000000000000^6301 ≤ 6642166040057^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179633483 10000000000 6642166040057 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167595641/312500000 : ℝ), (5281318077/10000000000 : ℝ), (-2179633483/10000000000 : ℝ)] ![(10949752865543/25000000000000 : ℝ), (21458328220719/50000000000000 : ℝ), (6642166040057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167595641/312500000 : ℝ)|^8349 ≤ (10949752865543/25000000000000 : ℝ)^6301
        have hw : |(167595641/312500000 : ℝ)|=(167595641/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281318077/10000000000 : ℝ)|^8349 ≤ (21458328220719/50000000000000 : ℝ)^6301
        have hw : |(5281318077/10000000000 : ℝ)|=(5281318077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179633483/10000000000 : ℝ)|^8349 ≤ (6642166040057/50000000000000 : ℝ)^6301
        have hw : |(-2179633483/10000000000 : ℝ)|=(2179633483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_7 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (850989431/2000000000 : ℝ)*x 0 + (2209332213/5000000000 : ℝ)*x 1 + (4418664473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850989431/2000000000 : ℝ)^8349 ≤ (16115525571231/50000000000000 : ℝ)^6301 := by
    have hnat : (850989431 : ℕ)^8349*50000000000000^6301 ≤ 16115525571231^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850989431 2000000000 16115525571231 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209332213/5000000000 : ℝ)^8349 ≤ (33884474181171/100000000000000 : ℝ)^6301 := by
    have hnat : (2209332213 : ℕ)^8349*100000000000000^6301 ≤ 33884474181171^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209332213 5000000000 33884474181171 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418664473/10000000000 : ℝ)^8349 ≤ (33884474658737/100000000000000 : ℝ)^6301 := by
    have hnat : (4418664473 : ℕ)^8349*100000000000000^6301 ≤ 33884474658737^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418664473 10000000000 33884474658737 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850989431/2000000000 : ℝ), (2209332213/5000000000 : ℝ), (4418664473/10000000000 : ℝ)] ![(16115525571231/50000000000000 : ℝ), (33884474181171/100000000000000 : ℝ), (33884474658737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850989431/2000000000 : ℝ)|^8349 ≤ (16115525571231/50000000000000 : ℝ)^6301
        have hw : |(850989431/2000000000 : ℝ)|=(850989431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2209332213/5000000000 : ℝ)|^8349 ≤ (33884474181171/100000000000000 : ℝ)^6301
        have hw : |(2209332213/5000000000 : ℝ)|=(2209332213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418664473/10000000000 : ℝ)|^8349 ≤ (33884474658737/100000000000000 : ℝ)^6301
        have hw : |(4418664473/10000000000 : ℝ)|=(4418664473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_8 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1117422731/5000000000 : ℝ)*x 0 + (260841257/500000000 : ℝ)*x 1 + (5385716523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1117422731/5000000000 : ℝ)^8349 ≤ (13732033694651/100000000000000 : ℝ)^6301 := by
    have hnat : (1117422731 : ℕ)^8349*100000000000000^6301 ≤ 13732033694651^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117422731 5000000000 13732033694651 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260841257/500000000 : ℝ)^8349 ≤ (42223620792663/100000000000000 : ℝ)^6301 := by
    have hnat : (260841257 : ℕ)^8349*100000000000000^6301 ≤ 42223620792663^6301*500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260841257 500000000 42223620792663 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385716523/10000000000 : ℝ)^8349 ≤ (22022172751529/50000000000000 : ℝ)^6301 := by
    have hnat : (5385716523 : ℕ)^8349*50000000000000^6301 ≤ 22022172751529^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385716523 10000000000 22022172751529 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1117422731/5000000000 : ℝ), (260841257/500000000 : ℝ), (5385716523/10000000000 : ℝ)] ![(13732033694651/100000000000000 : ℝ), (42223620792663/100000000000000 : ℝ), (22022172751529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1117422731/5000000000 : ℝ)|^8349 ≤ (13732033694651/100000000000000 : ℝ)^6301
        have hw : |(-1117422731/5000000000 : ℝ)|=(1117422731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260841257/500000000 : ℝ)|^8349 ≤ (42223620792663/100000000000000 : ℝ)^6301
        have hw : |(260841257/500000000 : ℝ)|=(260841257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385716523/10000000000 : ℝ)|^8349 ≤ (22022172751529/50000000000000 : ℝ)^6301
        have hw : |(5385716523/10000000000 : ℝ)|=(5385716523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_9 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289322993/10000000000 : ℝ)*x 0 + (-534613009/2500000000 : ℝ)*x 1 + (2692858139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289322993/10000000000 : ℝ)^8349 ≤ (21501434669587/50000000000000 : ℝ)^6301 := by
    have hnat : (5289322993 : ℕ)^8349*50000000000000^6301 ≤ 21501434669587^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289322993 10000000000 21501434669587 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534613009/2500000000 : ℝ)^8349 ≤ (6476393894609/50000000000000 : ℝ)^6301 := by
    have hnat : (534613009 : ℕ)^8349*50000000000000^6301 ≤ 6476393894609^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534613009 2500000000 6476393894609 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692858139/5000000000 : ℝ)^8349 ≤ (44044342848221/100000000000000 : ℝ)^6301 := by
    have hnat : (2692858139 : ℕ)^8349*100000000000000^6301 ≤ 44044342848221^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692858139 5000000000 44044342848221 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289322993/10000000000 : ℝ), (-534613009/2500000000 : ℝ), (2692858139/5000000000 : ℝ)] ![(21501434669587/50000000000000 : ℝ), (6476393894609/50000000000000 : ℝ), (44044342848221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289322993/10000000000 : ℝ)|^8349 ≤ (21501434669587/50000000000000 : ℝ)^6301
        have hw : |(5289322993/10000000000 : ℝ)|=(5289322993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534613009/2500000000 : ℝ)|^8349 ≤ (6476393894609/50000000000000 : ℝ)^6301
        have hw : |(-534613009/2500000000 : ℝ)|=(534613009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692858139/5000000000 : ℝ)|^8349 ≤ (44044342848221/100000000000000 : ℝ)^6301
        have hw : |(2692858139/5000000000 : ℝ)|=(2692858139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_10 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330582661/625000000 : ℝ)*x 0 + (2692858301/5000000000 : ℝ)*x 1 + (-6682663/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330582661/625000000 : ℝ)^8349 ≤ (43002864846981/100000000000000 : ℝ)^6301 := by
    have hnat : (330582661 : ℕ)^8349*100000000000000^6301 ≤ 43002864846981^6301*625000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330582661 625000000 43002864846981 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692858301/5000000000 : ℝ)^8349 ≤ (44044346359107/100000000000000 : ℝ)^6301 := by
    have hnat : (2692858301 : ℕ)^8349*100000000000000^6301 ≤ 44044346359107^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692858301 5000000000 44044346359107 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6682663/31250000 : ℝ)^8349 ≤ (6476394392209/50000000000000 : ℝ)^6301 := by
    have hnat : (6682663 : ℕ)^8349*50000000000000^6301 ≤ 6476394392209^6301*31250000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6682663 31250000 6476394392209 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330582661/625000000 : ℝ), (2692858301/5000000000 : ℝ), (-6682663/31250000 : ℝ)] ![(43002864846981/100000000000000 : ℝ), (44044346359107/100000000000000 : ℝ), (6476394392209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330582661/625000000 : ℝ)|^8349 ≤ (43002864846981/100000000000000 : ℝ)^6301
        have hw : |(330582661/625000000 : ℝ)|=(330582661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692858301/5000000000 : ℝ)|^8349 ≤ (44044346359107/100000000000000 : ℝ)^6301
        have hw : |(2692858301/5000000000 : ℝ)|=(2692858301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6682663/31250000 : ℝ)|^8349 ≤ (6476394392209/50000000000000 : ℝ)^6301
        have hw : |(-6682663/31250000 : ℝ)|=(6682663/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_11 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (35933103/80000000 : ℝ)*x 0 + (4300199179/10000000000 : ℝ)*x 1 + (4300199409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35933103/80000000 : ℝ)^8349 ≤ (17313968566061/50000000000000 : ℝ)^6301 := by
    have hnat : (35933103 : ℕ)^8349*50000000000000^6301 ≤ 17313968566061^6301*80000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35933103 80000000 17313968566061 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4300199179/10000000000 : ℝ)^8349 ≤ (32686030269669/100000000000000 : ℝ)^6301 := by
    have hnat : (4300199179 : ℕ)^8349*100000000000000^6301 ≤ 32686030269669^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300199179 10000000000 32686030269669 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4300199409/10000000000 : ℝ)^8349 ≤ (32686032586137/100000000000000 : ℝ)^6301 := by
    have hnat : (4300199409 : ℕ)^8349*100000000000000^6301 ≤ 32686032586137^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300199409 10000000000 32686032586137 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35933103/80000000 : ℝ), (4300199179/10000000000 : ℝ), (4300199409/10000000000 : ℝ)] ![(17313968566061/50000000000000 : ℝ), (32686030269669/100000000000000 : ℝ), (32686032586137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35933103/80000000 : ℝ)|^8349 ≤ (17313968566061/50000000000000 : ℝ)^6301
        have hw : |(35933103/80000000 : ℝ)|=(35933103/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4300199179/10000000000 : ℝ)|^8349 ≤ (32686030269669/100000000000000 : ℝ)^6301
        have hw : |(4300199179/10000000000 : ℝ)|=(4300199179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4300199409/10000000000 : ℝ)|^8349 ≤ (32686032586137/100000000000000 : ℝ)^6301
        have hw : |(4300199409/10000000000 : ℝ)|=(4300199409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_12 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-417455493/2000000000 : ℝ)*x 0 + (679916613/1250000000 : ℝ)*x 1 + (329579537/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417455493/2000000000 : ℝ)^8349 ≤ (6271838273319/50000000000000 : ℝ)^6301 := by
    have hnat : (417455493 : ℕ)^8349*50000000000000^6301 ≤ 6271838273319^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417455493 2000000000 6271838273319 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679916613/1250000000 : ℝ)^8349 ≤ (22313137016131/50000000000000 : ℝ)^6301 := by
    have hnat : (679916613 : ℕ)^8349*50000000000000^6301 ≤ 22313137016131^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679916613 1250000000 22313137016131 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329579537/625000000 : ℝ)^8349 ≤ (21415024700609/50000000000000 : ℝ)^6301 := by
    have hnat : (329579537 : ℕ)^8349*50000000000000^6301 ≤ 21415024700609^6301*625000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329579537 625000000 21415024700609 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417455493/2000000000 : ℝ), (679916613/1250000000 : ℝ), (329579537/625000000 : ℝ)] ![(6271838273319/50000000000000 : ℝ), (22313137016131/50000000000000 : ℝ), (21415024700609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417455493/2000000000 : ℝ)|^8349 ≤ (6271838273319/50000000000000 : ℝ)^6301
        have hw : |(-417455493/2000000000 : ℝ)|=(417455493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679916613/1250000000 : ℝ)|^8349 ≤ (22313137016131/50000000000000 : ℝ)^6301
        have hw : |(679916613/1250000000 : ℝ)|=(679916613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329579537/625000000 : ℝ)|^8349 ≤ (21415024700609/50000000000000 : ℝ)^6301
        have hw : |(329579537/625000000 : ℝ)|=(329579537/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_13 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368740047/10000000000 : ℝ)*x 0 + (-436548967/2000000000 : ℝ)*x 1 + (5273273027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368740047/10000000000 : ℝ)^8349 ≤ (43860481586659/100000000000000 : ℝ)^6301 := by
    have hnat : (5368740047 : ℕ)^8349*100000000000000^6301 ≤ 43860481586659^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368740047 10000000000 43860481586659 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436548967/2000000000 : ℝ)^8349 ≤ (13309464313639/100000000000000 : ℝ)^6301 := by
    have hnat : (436548967 : ℕ)^8349*100000000000000^6301 ≤ 13309464313639^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436548967 2000000000 13309464313639 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273273027/10000000000 : ℝ)^8349 ≤ (10707513520673/25000000000000 : ℝ)^6301 := by
    have hnat : (5273273027 : ℕ)^8349*25000000000000^6301 ≤ 10707513520673^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273273027 10000000000 10707513520673 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368740047/10000000000 : ℝ), (-436548967/2000000000 : ℝ), (5273273027/10000000000 : ℝ)] ![(43860481586659/100000000000000 : ℝ), (13309464313639/100000000000000 : ℝ), (10707513520673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368740047/10000000000 : ℝ)|^8349 ≤ (43860481586659/100000000000000 : ℝ)^6301
        have hw : |(5368740047/10000000000 : ℝ)|=(5368740047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436548967/2000000000 : ℝ)|^8349 ≤ (13309464313639/100000000000000 : ℝ)^6301
        have hw : |(-436548967/2000000000 : ℝ)|=(436548967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273273027/10000000000 : ℝ)|^8349 ≤ (10707513520673/25000000000000 : ℝ)^6301
        have hw : |(5273273027/10000000000 : ℝ)|=(5273273027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_14 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368740029/10000000000 : ℝ)*x 0 + (5273273283/10000000000 : ℝ)*x 1 + (-1091372259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368740029/10000000000 : ℝ)^8349 ≤ (4386048139181/10000000000000 : ℝ)^6301 := by
    have hnat : (5368740029 : ℕ)^8349*10000000000000^6301 ≤ 4386048139181^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368740029 10000000000 4386048139181 10000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273273283/10000000000 : ℝ)^8349 ≤ (21415028418883/50000000000000 : ℝ)^6301 := by
    have hnat : (5273273283 : ℕ)^8349*50000000000000^6301 ≤ 21415028418883^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273273283 10000000000 21415028418883 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091372259/5000000000 : ℝ)^8349 ≤ (13309461752449/100000000000000 : ℝ)^6301 := by
    have hnat : (1091372259 : ℕ)^8349*100000000000000^6301 ≤ 13309461752449^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091372259 5000000000 13309461752449 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368740029/10000000000 : ℝ), (5273273283/10000000000 : ℝ), (-1091372259/5000000000 : ℝ)] ![(4386048139181/10000000000000 : ℝ), (21415028418883/50000000000000 : ℝ), (13309461752449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368740029/10000000000 : ℝ)|^8349 ≤ (4386048139181/10000000000000 : ℝ)^6301
        have hw : |(5368740029/10000000000 : ℝ)|=(5368740029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273273283/10000000000 : ℝ)|^8349 ≤ (21415028418883/50000000000000 : ℝ)^6301
        have hw : |(5273273283/10000000000 : ℝ)|=(5273273283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091372259/5000000000 : ℝ)|^8349 ≤ (13309461752449/100000000000000 : ℝ)^6301
        have hw : |(-1091372259/5000000000 : ℝ)|=(1091372259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_box_15 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (84729149/200000000 : ℝ)*x 0 + (2213893383/5000000000 : ℝ)*x 1 + (4427787299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84729149/200000000 : ℝ)^8349 ≤ (8011400144937/25000000000000 : ℝ)^6301 := by
    have hnat : (84729149 : ℕ)^8349*25000000000000^6301 ≤ 8011400144937^6301*200000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84729149 200000000 8011400144937 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213893383/5000000000 : ℝ)^8349 ≤ (33977196991183/100000000000000 : ℝ)^6301 := by
    have hnat : (2213893383 : ℕ)^8349*100000000000000^6301 ≤ 33977196991183^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213893383 5000000000 33977196991183 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4427787299/10000000000 : ℝ)^8349 ≤ (16988601205303/50000000000000 : ℝ)^6301 := by
    have hnat : (4427787299 : ℕ)^8349*50000000000000^6301 ≤ 16988601205303^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427787299 10000000000 16988601205303 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84729149/200000000 : ℝ), (2213893383/5000000000 : ℝ), (4427787299/10000000000 : ℝ)] ![(8011400144937/25000000000000 : ℝ), (33977196991183/100000000000000 : ℝ), (16988601205303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84729149/200000000 : ℝ)|^8349 ≤ (8011400144937/25000000000000 : ℝ)^6301
        have hw : |(84729149/200000000 : ℝ)|=(84729149/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2213893383/5000000000 : ℝ)|^8349 ≤ (33977196991183/100000000000000 : ℝ)^6301
        have hw : |(2213893383/5000000000 : ℝ)|=(2213893383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4427787299/10000000000 : ℝ)|^8349 ≤ (16988601205303/50000000000000 : ℝ)^6301
        have hw : |(4427787299/10000000000 : ℝ)|=(4427787299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62233/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59309/100000 : ℝ) ∧ (79851/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20789/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2843/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2843/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2843/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2843/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2843/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2843/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2843/25000 : ℝ) ^ (2087/512 : ℝ) ≤ (14171921129692633/100000000000000000000 : ℝ) := by
    have hpowers : (2843/25000 : ℝ)^2087 ≤ (14171921129692633/100000000000000000000 : ℝ)^512 := by
      have hnat : (2843 : ℕ)^2087*100000000000000000000^512 ≤ 14171921129692633^512*25000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2843 25000 14171921129692633 100000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2843/25000 : ℝ)) (X := (14171921129692633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1757/12500 : ℝ) ^ (2087/512 : ℝ) ≤ (1680769002078087/5000000000000000000 : ℝ) := by
    have hpowers : (1757/12500 : ℝ)^2087 ≤ (1680769002078087/5000000000000000000 : ℝ)^512 := by
      have hnat : (1757 : ℕ)^2087*5000000000000000000^512 ≤ 1680769002078087^512*12500^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1757 12500 1680769002078087 5000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1757/12500 : ℝ)) (X := (1680769002078087/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014171921129692633/50000000000000000000 : ℝ) ≤ (250017382002167/250000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (50014171921129692633/50000000000000000000 : ℝ)^512 ≤ (250017382002167/250000000000000 : ℝ)^2087 := by
      have hnat : (50014171921129692633 : ℕ)^512*250000000000000^2087 ≤ 250017382002167^2087*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014171921129692633 50000000000000000000 250017382002167 250000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250017382002167/250000000000000 : ℝ)) (X := (50014171921129692633/50000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047787301171254373/100000000000000000000 : ℝ) ≤ (625073259126613/625000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (100047787301171254373/100000000000000000000 : ℝ)^512 ≤ (625073259126613/625000000000000 : ℝ)^2087 := by
      have hnat : (100047787301171254373 : ℕ)^512*625000000000000^2087 ≤ 625073259126613^2087*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047787301171254373 100000000000000000000 625073259126613 625000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625073259126613/625000000000000 : ℝ)) (X := (100047787301171254373/100000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501680769002078087/2500000000000000000 : ℝ) ≤ (1250206126495617/1250000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (2501680769002078087/2500000000000000000 : ℝ)^512 ≤ (1250206126495617/1250000000000000 : ℝ)^2087 := by
      have hnat : (2501680769002078087 : ℕ)^512*1250000000000000^2087 ≤ 1250206126495617^2087*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501680769002078087 2500000000000000000 1250206126495617 1250000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250206126495617/1250000000000000 : ℝ)) (X := (2501680769002078087/2500000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14171921129692633/100000000000000000000 : ℝ) ≤ ((838469384151035059/838750000000000000 : ℝ)+2*(59608242391/33550000000000 : ℝ)*(2843/25000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (838469384151035059/838750000000000000 : ℝ)+2*(59608242391/33550000000000 : ℝ)*(2843/25000 : ℝ)=(250017382002167/250000000000000 : ℝ) by norm_num, show 1+2*(14171921129692633/100000000000000000000 : ℝ)=(50014171921129692633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1680769002078087/5000000000000000000 : ℝ)+(14171921129692633/100000000000000000000 : ℝ) ≤ ((838469384151035059/838750000000000000 : ℝ)+(59608242391/33550000000000 : ℝ)*((1757/12500 : ℝ)+(2843/25000 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (838469384151035059/838750000000000000 : ℝ)+(59608242391/33550000000000 : ℝ)*((1757/12500 : ℝ)+(2843/25000 : ℝ))=(625073259126613/625000000000000 : ℝ) by norm_num, show 1+(1680769002078087/5000000000000000000 : ℝ)+(14171921129692633/100000000000000000000 : ℝ)=(100047787301171254373/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1680769002078087/5000000000000000000 : ℝ) ≤ ((838469384151035059/838750000000000000 : ℝ)+2*(59608242391/33550000000000 : ℝ)*(1757/12500 : ℝ))^(2087/512 : ℝ) := by
    rw [show (838469384151035059/838750000000000000 : ℝ)+2*(59608242391/33550000000000 : ℝ)*(1757/12500 : ℝ)=(1250206126495617/1250000000000000 : ℝ) by norm_num, show 1+2*(1680769002078087/5000000000000000000 : ℝ)=(2501680769002078087/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (838469384151035059/838750000000000000 : ℝ)*(X 1 0+X 2 0)+(59608242391/33550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (838469384151035059/838750000000000000 : ℝ)) (alpha := (59608242391/33550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (838469384151035059/838750000000000000 : ℝ)*(X 0 1+X 2 1)+(59608242391/33550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (838469384151035059/838750000000000000 : ℝ)) (alpha := (59608242391/33550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (838469384151035059/838750000000000000 : ℝ)*(X 0 2+X 1 2)+(59608242391/33550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (838469384151035059/838750000000000000 : ℝ)) (alpha := (59608242391/33550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-406756903/2000000000 : ℝ)*X 0 0+(5376107257/10000000000 : ℝ)*X 0 1+(5376107101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5171986/9765625 : ℝ)*X 1 0+(-2142304881/10000000000 : ℝ)*X 1 1+(1075221337/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1059222609/2000000000 : ℝ)*X 2 0+(2688053523/5000000000 : ℝ)*X 2 1+(-85692209/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4470099413/10000000000 : ℝ)*X 0 0+(4311108759/10000000000 : ℝ)*X 0 1+(134722167/312500000 : ℝ)*X 0 2+(4470099413/10000000000 : ℝ)*X 1 0+(4311108759/10000000000 : ℝ)*X 1 1+(134722167/312500000 : ℝ)*X 1 2+(4470099413/10000000000 : ℝ)*X 2 0+(4311108759/10000000000 : ℝ)*X 2 1+(134722167/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-45760551/200000000 : ℝ)*X 0 0+(5281318203/10000000000 : ℝ)*X 0 1+(2640658879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072612109/2000000000 : ℝ)*X 1 0+(-108981691/500000000 : ℝ)*X 1 1+(5281317791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((167595641/312500000 : ℝ)*X 2 0+(5281318077/10000000000 : ℝ)*X 2 1+(-2179633483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((850989431/2000000000 : ℝ)*X 0 0+(2209332213/5000000000 : ℝ)*X 0 1+(4418664473/10000000000 : ℝ)*X 0 2+(850989431/2000000000 : ℝ)*X 1 0+(2209332213/5000000000 : ℝ)*X 1 1+(4418664473/10000000000 : ℝ)*X 1 2+(850989431/2000000000 : ℝ)*X 2 0+(2209332213/5000000000 : ℝ)*X 2 1+(4418664473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1117422731/5000000000 : ℝ)*X 0 0+(260841257/500000000 : ℝ)*X 0 1+(5385716523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289322993/10000000000 : ℝ)*X 1 0+(-534613009/2500000000 : ℝ)*X 1 1+(2692858139/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((330582661/625000000 : ℝ)*X 2 0+(2692858301/5000000000 : ℝ)*X 2 1+(-6682663/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((35933103/80000000 : ℝ)*X 0 0+(4300199179/10000000000 : ℝ)*X 0 1+(4300199409/10000000000 : ℝ)*X 0 2+(35933103/80000000 : ℝ)*X 1 0+(4300199179/10000000000 : ℝ)*X 1 1+(4300199409/10000000000 : ℝ)*X 1 2+(35933103/80000000 : ℝ)*X 2 0+(4300199179/10000000000 : ℝ)*X 2 1+(4300199409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-417455493/2000000000 : ℝ)*X 0 0+(679916613/1250000000 : ℝ)*X 0 1+(329579537/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368740047/10000000000 : ℝ)*X 1 0+(-436548967/2000000000 : ℝ)*X 1 1+(5273273027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368740029/10000000000 : ℝ)*X 2 0+(5273273283/10000000000 : ℝ)*X 2 1+(-1091372259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((84729149/200000000 : ℝ)*X 0 0+(2213893383/5000000000 : ℝ)*X 0 1+(4427787299/10000000000 : ℝ)*X 0 2+(84729149/200000000 : ℝ)*X 1 0+(2213893383/5000000000 : ℝ)*X 1 1+(4427787299/10000000000 : ℝ)*X 1 2+(84729149/200000000 : ℝ)*X 2 0+(2213893383/5000000000 : ℝ)*X 2 1+(4427787299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62233/100000 : ℝ) ≤ (-13048908920183331306761634377223/20968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32816449/50000000000000 : ℝ)*(upper0) + (70710477/50000000000000 : ℝ)*(lower2) + (17951571/50000000000000 : ℝ)*(upper5) + (1966151274136199/50000000000000 : ℝ)*(major0) + (1966151274136199/50000000000000 : ℝ)*(major1) + (1966151274136199/50000000000000 : ℝ)*(major2) + (8172873457/50000000000000 : ℝ)*(sp1) + (1700673141/25000000000000 : ℝ)*(sp3) + (5259366786886899/100000000000000 : ℝ)*(sp4) + (2629683472367401/50000000000000 : ℝ)*(sp5) + (1051859280829081/20000000000000 : ℝ)*(sp6) + (2625958425399609/100000000000000 : ℝ)*(sp7) + (16503594817/100000000000000 : ℝ)*(sp8) + (86886336311/100000000000000 : ℝ)*(sp14) + (1312982614046087/50000000000000 : ℝ)*(f.failure) + (1314845822620429/25000000000000 : ℝ)*(f.sum) + (5069978366929/3355000000000000000000000000 : ℝ)*base66 + (747854249507086759/41937500000000000000000000000000 : ℝ)*base68 + (374601955858600741/41937500000000000000000000000000 : ℝ)*base69 + (223026221846288241/41937500000000000000000000000000 : ℝ)*base71 + (2846714156767/104843750000000000000000000 : ℝ)*base74 + (239870660616788241/41937500000000000000000000000000 : ℝ)*base75 + (157255495885149259/41937500000000000000000000000000 : ℝ)*base78 + (568067196218475741/41937500000000000000000000000000 : ℝ)*base79 + (951308709859/838750000000000000000000000 : ℝ)*base81 + (33177693/5000000000000000000000 : ℝ)*base89 + (33177693/5000000000000000000000 : ℝ)*base91 + (33177693/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59309/100000 : ℝ) ≤ (6218477481180473811090604767651/10484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3144753/12500000000000 : ℝ)*(lower1) + (161159811/100000000000000 : ℝ)*(upper2) + (78839259/50000000000000 : ℝ)*(lower4) + (56899889/100000000000000 : ℝ)*(lower5) + (499585345919281/12500000000000 : ℝ)*(major0) + (499585345919281/12500000000000 : ℝ)*(major1) + (499585345919281/12500000000000 : ℝ)*(major2) + (5304626330818791/100000000000000 : ℝ)*(sp0) + (5304495470357671/100000000000000 : ℝ)*(sp1) + (1060901896777339/20000000000000 : ℝ)*(sp2) + (1334478952973539/50000000000000 : ℝ)*(sp3) + (70769743463/50000000000000 : ℝ)*(sp9) + (63762978951/50000000000000 : ℝ)*(sp10) + (5339512903/50000000000000 : ℝ)*(sp12) + (1334478952973539/50000000000000 : ℝ)*(f.failure) + (5304637009844597/100000000000000 : ℝ)*(f.sum) + (9584488754009/3355000000000000000000000000 : ℝ)*base66 + (3165019962752949/2621093750000000000000000000000 : ℝ)*base68 + (20127816337759727/5242187500000000000000000000000 : ℝ)*base69 + (83460374877535079/10484375000000000000000000000000 : ℝ)*base71 + (10605417454889/3355000000000000000000000000 : ℝ)*base74 + (9377830076665977/5242187500000000000000000000000 : ℝ)*base75 + (4350562905653301/2621093750000000000000000000000 : ℝ)*base77 + (1354307152152421/10484375000000000000000000000000 : ℝ)*base80 + (9287167909301/3355000000000000000000000000 : ℝ)*base81 + (13247121/5000000000000000000000 : ℝ)*base89 + (13247121/5000000000000000000000 : ℝ)*base91 + (13247121/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79851/100000 : ℝ) ≤ (16744278144125590801024479080373/20968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2474491/2500000000000 : ℝ)*(upper0) + (32404221/25000000000000 : ℝ)*(upper1) + (100730869/50000000000000 : ℝ)*(upper2) + (2232232967051601/50000000000000 : ℝ)*(major0) + (2232232967051601/50000000000000 : ℝ)*(major1) + (2232232967051601/50000000000000 : ℝ)*(major2) + (138424135833/100000000000000 : ℝ)*(sp1) + (51337448619/25000000000000 : ℝ)*(sp2) + (10942071417/20000000000000 : ℝ)*(sp3) + (7110569317/50000000000000 : ℝ)*(sp4) + (5920959455367843/100000000000000 : ℝ)*(sp8) + (1480208813092661/25000000000000 : ℝ)*(sp9) + (5920768326712001/100000000000000 : ℝ)*(sp10) + (1490642826100823/50000000000000 : ℝ)*(sp11) + (2981340362558731/100000000000000 : ℝ)*(f.failure) + (5920973676506477/100000000000000 : ℝ)*(f.sum) + (2670025902131/3355000000000000000000000000 : ℝ)*base66 + (73872859472791959/41937500000000000000000000000000 : ℝ)*base67 + (163225817752541959/41937500000000000000000000000000 : ℝ)*base69 + (15260645405208041/41937500000000000000000000000000 : ℝ)*base72 + (18310679642913/419375000000000000000000000 : ℝ)*base73 + (464863208246541959/41937500000000000000000000000000 : ℝ)*base75 + (247646162719708041/41937500000000000000000000000000 : ℝ)*base78 + (1982318865054291959/41937500000000000000000000000000 : ℝ)*base79 + (356524360547/1677500000000000000000000000 : ℝ)*base81 + (25025591/10000000000000000000000 : ℝ)*base90 + (25025591/10000000000000000000000 : ℝ)*base92 + (25025591/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-20789/25000 : ℝ) ≤ (-8718096700883257516149005406639/10484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9844603/50000000000000 : ℝ)*(lower2) + (67827389/100000000000000 : ℝ)*(upper3) + (402154001/100000000000000 : ℝ)*(upper5) + (2249746405982293/50000000000000 : ℝ)*(major0) + (2249746405982293/50000000000000 : ℝ)*(major1) + (2249746405982293/50000000000000 : ℝ)*(major2) + (9550606863/50000000000000 : ℝ)*(sp0) + (202974920617/50000000000000 : ℝ)*(sp5) + (352196387363/100000000000000 : ℝ)*(sp6) + (5767836037/20000000000000 : ℝ)*(sp8) + (1505481087831411/25000000000000 : ℝ)*(sp12) + (6021566341878321/100000000000000 : ℝ)*(sp13) + (6021620095332191/100000000000000 : ℝ)*(sp14) + (751182769078937/25000000000000 : ℝ)*(sp15) + (751182769078937/25000000000000 : ℝ)*(f.failure) + (3010986145859777/50000000000000 : ℝ)*(f.sum) + (265363152081/419375000000000000000000000 : ℝ)*base66 + (39745589449910287/41937500000000000000000000000000 : ℝ)*base67 + (168732322125402213/41937500000000000000000000000000 : ℝ)*base70 + (207728209960152213/41937500000000000000000000000000 : ℝ)*base72 + (8826646327437/3355000000000000000000000000 : ℝ)*base73 + (329228285054902213/41937500000000000000000000000000 : ℝ)*base76 + (174251591275027213/41937500000000000000000000000000 : ℝ)*base78 + (494276610872964713/41937500000000000000000000000000 : ℝ)*base80 + (7838965011423/3355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (15123843/2500000000000000000000 : ℝ)*base89 + (15123843/2500000000000000000000 : ℝ)*base91 + (15123843/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1156_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59309/100000 : ℝ) else (79851/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20789/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1156_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1156_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59309/100000 : ℝ) else (79851/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20789/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1156_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1156_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62233/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59309/100000 : ℝ) else (79851/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20789/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1156_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
