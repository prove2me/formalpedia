-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1114_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:06:32.102982+00:00
-- url     : https://prove2.me/submissions/fd78f5a0-9bfe-4cc1-857f-0d2648228d32

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
theorem support_rectangle_w1114_s3_0 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-136014139/625000000 : ℝ)*x 0 + (5432127049/10000000000 : ℝ)*x 1 + (5229382599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136014139/625000000 : ℝ)^8307 ≤ (13212803006729/100000000000000 : ℝ)^6259 := by
    have hnat : (136014139 : ℕ)^8307*100000000000000^6259 ≤ 13212803006729^6259*625000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136014139 625000000 13212803006729 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432127049/10000000000 : ℝ)^8307 ≤ (111221756013/250000000000 : ℝ)^6259 := by
    have hnat : (5432127049 : ℕ)^8307*250000000000^6259 ≤ 111221756013^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432127049 10000000000 111221756013 250000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229382599/10000000000 : ℝ)^8307 ≤ (5287311822363/12500000000000 : ℝ)^6259 := by
    have hnat : (5229382599 : ℕ)^8307*12500000000000^6259 ≤ 5287311822363^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229382599 10000000000 5287311822363 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136014139/625000000 : ℝ), (5432127049/10000000000 : ℝ), (5229382599/10000000000 : ℝ)] ![(13212803006729/100000000000000 : ℝ), (111221756013/250000000000 : ℝ), (5287311822363/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136014139/625000000 : ℝ)|^8307 ≤ (13212803006729/100000000000000 : ℝ)^6259
        have hw : |(-136014139/625000000 : ℝ)|=(136014139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432127049/10000000000 : ℝ)|^8307 ≤ (111221756013/250000000000 : ℝ)^6259
        have hw : |(5432127049/10000000000 : ℝ)|=(5432127049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229382599/10000000000 : ℝ)|^8307 ≤ (5287311822363/12500000000000 : ℝ)^6259
        have hw : |(5229382599/10000000000 : ℝ)|=(5229382599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s3_1 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5354475151/10000000000 : ℝ)*x 0 + (-2279927307/10000000000 : ℝ)*x 1 + (1307345653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354475151/10000000000 : ℝ)^8307 ≤ (8729325396997/20000000000000 : ℝ)^6259 := by
    have hnat : (5354475151 : ℕ)^8307*20000000000000^6259 ≤ 8729325396997^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354475151 10000000000 8729325396997 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279927307/10000000000 : ℝ)^8307 ≤ (14054878279177/100000000000000 : ℝ)^6259 := by
    have hnat : (2279927307 : ℕ)^8307*100000000000000^6259 ≤ 14054878279177^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279927307 10000000000 14054878279177 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307345653/2500000000 : ℝ)^8307 ≤ (21149247359231/50000000000000 : ℝ)^6259 := by
    have hnat : (1307345653 : ℕ)^8307*50000000000000^6259 ≤ 21149247359231^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307345653 2500000000 21149247359231 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354475151/10000000000 : ℝ), (-2279927307/10000000000 : ℝ), (1307345653/2500000000 : ℝ)] ![(8729325396997/20000000000000 : ℝ), (14054878279177/100000000000000 : ℝ), (21149247359231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354475151/10000000000 : ℝ)|^8307 ≤ (8729325396997/20000000000000 : ℝ)^6259
        have hw : |(5354475151/10000000000 : ℝ)|=(5354475151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279927307/10000000000 : ℝ)|^8307 ≤ (14054878279177/100000000000000 : ℝ)^6259
        have hw : |(-2279927307/10000000000 : ℝ)|=(2279927307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307345653/2500000000 : ℝ)|^8307 ≤ (21149247359231/50000000000000 : ℝ)^6259
        have hw : |(1307345653/2500000000 : ℝ)|=(1307345653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s3_2 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5354475269/10000000000 : ℝ)*x 0 + (2614691357/5000000000 : ℝ)*x 1 + (-1139963509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354475269/10000000000 : ℝ)^8307 ≤ (8729325652317/20000000000000 : ℝ)^6259 := by
    have hnat : (5354475269 : ℕ)^8307*20000000000000^6259 ≤ 8729325652317^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354475269 10000000000 8729325652317 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614691357/5000000000 : ℝ)^8307 ≤ (21149247906731/50000000000000 : ℝ)^6259 := by
    have hnat : (2614691357 : ℕ)^8307*50000000000000^6259 ≤ 21149247906731^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614691357 5000000000 21149247906731 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139963509/5000000000 : ℝ)^8307 ≤ (439214872333/3125000000000 : ℝ)^6259 := by
    have hnat : (1139963509 : ℕ)^8307*3125000000000^6259 ≤ 439214872333^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139963509 5000000000 439214872333 3125000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354475269/10000000000 : ℝ), (2614691357/5000000000 : ℝ), (-1139963509/5000000000 : ℝ)] ![(8729325652317/20000000000000 : ℝ), (21149247906731/50000000000000 : ℝ), (439214872333/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354475269/10000000000 : ℝ)|^8307 ≤ (8729325652317/20000000000000 : ℝ)^6259
        have hw : |(5354475269/10000000000 : ℝ)|=(5354475269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614691357/5000000000 : ℝ)|^8307 ≤ (21149247906731/50000000000000 : ℝ)^6259
        have hw : |(2614691357/5000000000 : ℝ)|=(2614691357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1139963509/5000000000 : ℝ)|^8307 ≤ (439214872333/3125000000000 : ℝ)^6259
        have hw : |(-1139963509/5000000000 : ℝ)|=(1139963509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s3_3 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366188963/10000000000 : ℝ)*x 0 + (4170226527/10000000000 : ℝ)*x 1 + (457136657/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366188963/10000000000 : ℝ)^8307 ≤ (16646038883481/50000000000000 : ℝ)^6259 := by
    have hnat : (4366188963 : ℕ)^8307*50000000000000^6259 ≤ 16646038883481^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366188963 10000000000 16646038883481 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170226527/10000000000 : ℝ)^8307 ≤ (1957728892577/6250000000000 : ℝ)^6259 := by
    have hnat : (4170226527 : ℕ)^8307*6250000000000^6259 ≤ 1957728892577^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170226527 10000000000 1957728892577 6250000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457136657/1000000000 : ℝ)^8307 ≤ (35384259937973/100000000000000 : ℝ)^6259 := by
    have hnat : (457136657 : ℕ)^8307*100000000000000^6259 ≤ 35384259937973^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457136657 1000000000 35384259937973 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366188963/10000000000 : ℝ), (4170226527/10000000000 : ℝ), (457136657/1000000000 : ℝ)] ![(16646038883481/50000000000000 : ℝ), (1957728892577/6250000000000 : ℝ), (35384259937973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366188963/10000000000 : ℝ)|^8307 ≤ (16646038883481/50000000000000 : ℝ)^6259
        have hw : |(4366188963/10000000000 : ℝ)|=(4366188963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170226527/10000000000 : ℝ)|^8307 ≤ (1957728892577/6250000000000 : ℝ)^6259
        have hw : |(4170226527/10000000000 : ℝ)|=(4170226527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(457136657/1000000000 : ℝ)|^8307 ≤ (35384259937973/100000000000000 : ℝ)^6259
        have hw : |(457136657/1000000000 : ℝ)|=(457136657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s3_4 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088122833/5000000000 : ℝ)*x 0 + (5230185099/10000000000 : ℝ)*x 1 + (2715660011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088122833/5000000000 : ℝ)^8307 ≤ (6606479835823/50000000000000 : ℝ)^6259 := by
    have hnat : (1088122833 : ℕ)^8307*50000000000000^6259 ≤ 6606479835823^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088122833 5000000000 6606479835823 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230185099/10000000000 : ℝ)^8307 ≤ (42307109864853/100000000000000 : ℝ)^6259 := by
    have hnat : (5230185099 : ℕ)^8307*100000000000000^6259 ≤ 42307109864853^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230185099 10000000000 42307109864853 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715660011/5000000000 : ℝ)^8307 ≤ (44479930446317/100000000000000 : ℝ)^6259 := by
    have hnat : (2715660011 : ℕ)^8307*100000000000000^6259 ≤ 44479930446317^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715660011 5000000000 44479930446317 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088122833/5000000000 : ℝ), (5230185099/10000000000 : ℝ), (2715660011/5000000000 : ℝ)] ![(6606479835823/50000000000000 : ℝ), (42307109864853/100000000000000 : ℝ), (44479930446317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088122833/5000000000 : ℝ)|^8307 ≤ (6606479835823/50000000000000 : ℝ)^6259
        have hw : |(-1088122833/5000000000 : ℝ)|=(1088122833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230185099/10000000000 : ℝ)|^8307 ≤ (42307109864853/100000000000000 : ℝ)^6259
        have hw : |(5230185099/10000000000 : ℝ)|=(5230185099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715660011/5000000000 : ℝ)|^8307 ≤ (44479930446317/100000000000000 : ℝ)^6259
        have hw : |(2715660011/5000000000 : ℝ)|=(2715660011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s3_5 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530321697/1000000000 : ℝ)*x 0 + (-415597953/2000000000 : ℝ)*x 1 + (5431320179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530321697/1000000000 : ℝ)^8307 ≤ (43092953093991/100000000000000 : ℝ)^6259 := by
    have hnat : (530321697 : ℕ)^8307*100000000000000^6259 ≤ 43092953093991^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530321697 1000000000 43092953093991 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415597953/2000000000 : ℝ)^8307 ≤ (1242711473579/10000000000000 : ℝ)^6259 := by
    have hnat : (415597953 : ℕ)^8307*10000000000000^6259 ≤ 1242711473579^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415597953 2000000000 1242711473579 10000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431320179/10000000000 : ℝ)^8307 ≤ (44479932152783/100000000000000 : ℝ)^6259 := by
    have hnat : (5431320179 : ℕ)^8307*100000000000000^6259 ≤ 44479932152783^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431320179 10000000000 44479932152783 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530321697/1000000000 : ℝ), (-415597953/2000000000 : ℝ), (5431320179/10000000000 : ℝ)] ![(43092953093991/100000000000000 : ℝ), (1242711473579/10000000000000 : ℝ), (44479932152783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530321697/1000000000 : ℝ)|^8307 ≤ (43092953093991/100000000000000 : ℝ)^6259
        have hw : |(530321697/1000000000 : ℝ)|=(530321697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415597953/2000000000 : ℝ)|^8307 ≤ (1242711473579/10000000000000 : ℝ)^6259
        have hw : |(-415597953/2000000000 : ℝ)|=(415597953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431320179/10000000000 : ℝ)|^8307 ≤ (44479932152783/100000000000000 : ℝ)^6259
        have hw : |(5431320179/10000000000 : ℝ)|=(5431320179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s3_6 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060643399/2000000000 : ℝ)*x 0 + (5431320037/10000000000 : ℝ)*x 1 + (-2077989927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060643399/2000000000 : ℝ)^8307 ≤ (5386619170451/12500000000000 : ℝ)^6259 := by
    have hnat : (1060643399 : ℕ)^8307*12500000000000^6259 ≤ 5386619170451^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060643399 2000000000 5386619170451 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431320037/10000000000 : ℝ)^8307 ≤ (8895986121871/20000000000000 : ℝ)^6259 := by
    have hnat : (5431320037 : ℕ)^8307*20000000000000^6259 ≤ 8895986121871^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431320037 10000000000 8895986121871 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077989927/10000000000 : ℝ)^8307 ≤ (12427116021613/100000000000000 : ℝ)^6259 := by
    have hnat : (2077989927 : ℕ)^8307*100000000000000^6259 ≤ 12427116021613^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077989927 10000000000 12427116021613 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060643399/2000000000 : ℝ), (5431320037/10000000000 : ℝ), (-2077989927/10000000000 : ℝ)] ![(5386619170451/12500000000000 : ℝ), (8895986121871/20000000000000 : ℝ), (12427116021613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060643399/2000000000 : ℝ)|^8307 ≤ (5386619170451/12500000000000 : ℝ)^6259
        have hw : |(1060643399/2000000000 : ℝ)|=(1060643399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431320037/10000000000 : ℝ)|^8307 ≤ (8895986121871/20000000000000 : ℝ)^6259
        have hw : |(5431320037/10000000000 : ℝ)|=(5431320037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2077989927/10000000000 : ℝ)|^8307 ≤ (12427116021613/100000000000000 : ℝ)^6259
        have hw : |(-2077989927/10000000000 : ℝ)|=(2077989927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s3_7 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136444607/312500000 : ℝ)*x 0 + (571222431/1250000000 : ℝ)*x 1 + (4171822831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136444607/312500000 : ℝ)^8307 ≤ (16646233495131/50000000000000 : ℝ)^6259 := by
    have hnat : (136444607 : ℕ)^8307*50000000000000^6259 ≤ 16646233495131^6259*312500000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136444607 312500000 16646233495131 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571222431/1250000000 : ℝ)^8307 ≤ (3536795613313/10000000000000 : ℝ)^6259 := by
    have hnat : (571222431 : ℕ)^8307*10000000000000^6259 ≤ 3536795613313^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571222431 1250000000 3536795613313 10000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171822831/10000000000 : ℝ)^8307 ≤ (15669788426223/50000000000000 : ℝ)^6259 := by
    have hnat : (4171822831 : ℕ)^8307*50000000000000^6259 ≤ 15669788426223^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171822831 10000000000 15669788426223 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136444607/312500000 : ℝ), (571222431/1250000000 : ℝ), (4171822831/10000000000 : ℝ)] ![(16646233495131/50000000000000 : ℝ), (3536795613313/10000000000000 : ℝ), (15669788426223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136444607/312500000 : ℝ)|^8307 ≤ (16646233495131/50000000000000 : ℝ)^6259
        have hw : |(136444607/312500000 : ℝ)|=(136444607/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571222431/1250000000 : ℝ)|^8307 ≤ (3536795613313/10000000000000 : ℝ)^6259
        have hw : |(571222431/1250000000 : ℝ)|=(571222431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171822831/10000000000 : ℝ)|^8307 ≤ (15669788426223/50000000000000 : ℝ)^6259
        have hw : |(4171822831/10000000000 : ℝ)|=(4171822831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1114_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16587/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (211/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (371/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16587/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4471/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16587/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4471/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16587/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4471/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16587/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4471/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16587/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4471/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16587/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4471/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4471/50000 : ℝ) ^ (4153/1024 : ℝ) ≤ (2794739030190031/50000000000000000000 : ℝ) := by
    have hpowers : (4471/50000 : ℝ)^4153 ≤ (2794739030190031/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4471 : ℕ)^4153*50000000000000000000^1024 ≤ 2794739030190031^1024*50000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4471 50000 2794739030190031 50000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4471/50000 : ℝ)) (X := (2794739030190031/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16587/100000 : ℝ) ^ (4153/1024 : ℝ) ≤ (1712302520056779/2500000000000000000 : ℝ) := by
    have hpowers : (16587/100000 : ℝ)^4153 ≤ (1712302520056779/2500000000000000000 : ℝ)^1024 := by
      have hnat : (16587 : ℕ)^4153*2500000000000000000^1024 ≤ 1712302520056779^1024*100000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16587 100000 1712302520056779 2500000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16587/100000 : ℝ)) (X := (1712302520056779/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002794739030190031/25000000000000000000 : ℝ) ≤ (5000137813255749/5000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (25002794739030190031/25000000000000000000 : ℝ)^1024 ≤ (5000137813255749/5000000000000000 : ℝ)^4153 := by
      have hnat : (25002794739030190031 : ℕ)^1024*5000000000000000^4153 ≤ 5000137813255749^4153*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002794739030190031 25000000000000000000 5000137813255749 5000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000137813255749/5000000000000000 : ℝ)) (X := (25002794739030190031/25000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50037040789431325611/50000000000000000000 : ℝ) ≤ (10001826110649511/10000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50037040789431325611/50000000000000000000 : ℝ)^1024 ≤ (10001826110649511/10000000000000000 : ℝ)^4153 := by
      have hnat : (50037040789431325611 : ℕ)^1024*10000000000000000^4153 ≤ 10001826110649511^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037040789431325611 50000000000000000000 10001826110649511 10000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001826110649511/10000000000000000 : ℝ)) (X := (50037040789431325611/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1251712302520056779/1250000000000000000 : ℝ) ≤ (2500844148696881/2500000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (1251712302520056779/1250000000000000000 : ℝ)^1024 ≤ (2500844148696881/2500000000000000 : ℝ)^4153 := by
      have hnat : (1251712302520056779 : ℕ)^1024*2500000000000000^4153 ≤ 2500844148696881^4153*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1251712302520056779 1250000000000000000 2500844148696881 2500000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500844148696881/2500000000000000 : ℝ)) (X := (1251712302520056779/1250000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2794739030190031/50000000000000000000 : ℝ) ≤ ((38212189153178088859/38225000000000000000 : ℝ)+2*(1550484138013/764500000000000 : ℝ)*(4471/50000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (38212189153178088859/38225000000000000000 : ℝ)+2*(1550484138013/764500000000000 : ℝ)*(4471/50000 : ℝ)=(5000137813255749/5000000000000000 : ℝ) by norm_num, show 1+2*(2794739030190031/50000000000000000000 : ℝ)=(25002794739030190031/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1712302520056779/2500000000000000000 : ℝ)+(2794739030190031/50000000000000000000 : ℝ) ≤ ((38212189153178088859/38225000000000000000 : ℝ)+(1550484138013/764500000000000 : ℝ)*((16587/100000 : ℝ)+(4471/50000 : ℝ)))^(4153/1024 : ℝ) := by
    rw [show (38212189153178088859/38225000000000000000 : ℝ)+(1550484138013/764500000000000 : ℝ)*((16587/100000 : ℝ)+(4471/50000 : ℝ))=(10001826110649511/10000000000000000 : ℝ) by norm_num, show 1+(1712302520056779/2500000000000000000 : ℝ)+(2794739030190031/50000000000000000000 : ℝ)=(50037040789431325611/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1712302520056779/2500000000000000000 : ℝ) ≤ ((38212189153178088859/38225000000000000000 : ℝ)+2*(1550484138013/764500000000000 : ℝ)*(16587/100000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (38212189153178088859/38225000000000000000 : ℝ)+2*(1550484138013/764500000000000 : ℝ)*(16587/100000 : ℝ)=(2500844148696881/2500000000000000 : ℝ) by norm_num, show 1+2*(1712302520056779/2500000000000000000 : ℝ)=(1251712302520056779/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38212189153178088859/38225000000000000000 : ℝ)*(X 1 0+X 2 0)+(1550484138013/764500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (4471/50000 : ℝ)) (hi := (16587/100000 : ℝ)) (c := (38212189153178088859/38225000000000000000 : ℝ)) (alpha := (1550484138013/764500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38212189153178088859/38225000000000000000 : ℝ)*(X 0 1+X 2 1)+(1550484138013/764500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (4471/50000 : ℝ)) (hi := (16587/100000 : ℝ)) (c := (38212189153178088859/38225000000000000000 : ℝ)) (alpha := (1550484138013/764500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38212189153178088859/38225000000000000000 : ℝ)*(X 0 2+X 1 2)+(1550484138013/764500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (4471/50000 : ℝ)) (hi := (16587/100000 : ℝ)) (c := (38212189153178088859/38225000000000000000 : ℝ)) (alpha := (1550484138013/764500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-136014139/625000000 : ℝ)*X 0 0+(5432127049/10000000000 : ℝ)*X 0 1+(5229382599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354475151/10000000000 : ℝ)*X 1 0+(-2279927307/10000000000 : ℝ)*X 1 1+(1307345653/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354475269/10000000000 : ℝ)*X 2 0+(2614691357/5000000000 : ℝ)*X 2 1+(-1139963509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366188963/10000000000 : ℝ)*X 0 0+(4170226527/10000000000 : ℝ)*X 0 1+(457136657/1000000000 : ℝ)*X 0 2+(4366188963/10000000000 : ℝ)*X 1 0+(4170226527/10000000000 : ℝ)*X 1 1+(457136657/1000000000 : ℝ)*X 1 2+(4366188963/10000000000 : ℝ)*X 2 0+(4170226527/10000000000 : ℝ)*X 2 1+(457136657/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1088122833/5000000000 : ℝ)*X 0 0+(5230185099/10000000000 : ℝ)*X 0 1+(2715660011/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530321697/1000000000 : ℝ)*X 1 0+(-415597953/2000000000 : ℝ)*X 1 1+(5431320179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060643399/2000000000 : ℝ)*X 2 0+(5431320037/10000000000 : ℝ)*X 2 1+(-2077989927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136444607/312500000 : ℝ)*X 0 0+(571222431/1250000000 : ℝ)*X 0 1+(4171822831/10000000000 : ℝ)*X 0 2+(136444607/312500000 : ℝ)*X 1 0+(571222431/1250000000 : ℝ)*X 1 1+(4171822831/10000000000 : ℝ)*X 1 2+(136444607/312500000 : ℝ)*X 2 0+(571222431/1250000000 : ℝ)*X 2 1+(4171822831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3313283508964178400025174917/477812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374937501/20000000000000 : ℝ)*(base19) + (352723907/20000000000000 : ℝ)*(base23) + (117673243/100000000000000 : ℝ)*(lower2) + (95943941/100000000000000 : ℝ)*(upper3) + (24588427/10000000000000 : ℝ)*(upper5) + (928164544498421/25000000000000 : ℝ)*(major0) + (928164544498421/25000000000000 : ℝ)*(major1) + (928164544498421/25000000000000 : ℝ)*(major2) + (493234951660943/10000000000000 : ℝ)*(sp0) + (2466193748169977/50000000000000 : ℝ)*(sp1) + (1233096901851981/25000000000000 : ℝ)*(sp2) + (2492911213704893/100000000000000 : ℝ)*(sp3) + (3985441803/10000000000000 : ℝ)*(sp4) + (3885028123/25000000000000 : ℝ)*(sp7) + (1246463376908693/50000000000000 : ℝ)*(f.failure) + (4932389371027459/100000000000000 : ℝ)*(f.sum) + (178574284253817/38225000000000000000000000000 : ℝ)*base65 + (4680168551130033361/955625000000000000000000000000000 : ℝ)*base68 + (1978013700645658361/955625000000000000000000000000000 : ℝ)*base70 + (261637167421283361/955625000000000000000000000000000 : ℝ)*base72 + (36812633289367/38225000000000000000000000000 : ℝ)*base73 + (14391484555028091639/955625000000000000000000000000000 : ℝ)*base75 + (6321521545354966639/955625000000000000000000000000000 : ℝ)*base77 + (1639196542495033361/955625000000000000000000000000000 : ℝ)*base80 + (44085793646571/19112500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4448973/625000000000000000000 : ℝ)*base89 + (4448973/625000000000000000000 : ℝ)*base91 + (4448973/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (451796338448701240289744337/86875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118755881/12500000000000 : ℝ)*(base19) + (295733151/25000000000000 : ℝ)*(base23) + (68603817/50000000000000 : ℝ)*(upper3) + (104134491/100000000000000 : ℝ)*(lower4) + (12972781/20000000000000 : ℝ)*(upper5) + (1871155055359897/50000000000000 : ℝ)*(major0) + (1871155055359897/50000000000000 : ℝ)*(major1) + (1871155055359897/50000000000000 : ℝ)*(major2) + (4641229493/25000000000000 : ℝ)*(sp1) + (19918874143/100000000000000 : ℝ)*(sp2) + (1242945751377481/25000000000000 : ℝ)*(sp4) + (994352698108981/20000000000000 : ℝ)*(sp5) + (4971761903703177/100000000000000 : ℝ)*(sp6) + (125641852128927/5000000000000 : ℝ)*(sp7) + (125641852128927/5000000000000 : ℝ)*(f.failure) + (1242945751377481/25000000000000 : ℝ)*(f.sum) + (71285056781639/19112500000000000000000000000 : ℝ)*base66 + (17307308931730862477/1911250000000000000000000000000000 : ℝ)*base68 + (20267408346090862477/1911250000000000000000000000000000 : ℝ)*base70 + (23592959482223362477/1911250000000000000000000000000000 : ℝ)*base72 + (95943090946653/38225000000000000000000000000 : ℝ)*base74 + (34934995508464612477/1911250000000000000000000000000000 : ℝ)*base76 + (24641492179523362477/1911250000000000000000000000000000 : ℝ)*base78 + (28937263604949612477/1911250000000000000000000000000000 : ℝ)*base80 + (101079227321253/38225000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (753847/62500000000000000000 : ℝ)*base89 + (753847/62500000000000000000 : ℝ)*base91 + (753847/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1114_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16587/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (211/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (371/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1114_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1114_s4_0 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-435892473/2000000000 : ℝ)*x 0 + (1350817159/2500000000 : ℝ)*x 1 + (5256124977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435892473/2000000000 : ℝ)^8307 ≤ (6619443174051/50000000000000 : ℝ)^6259 := by
    have hnat : (435892473 : ℕ)^8307*50000000000000^6259 ≤ 6619443174051^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435892473 2000000000 6619443174051 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350817159/2500000000 : ℝ)^8307 ≤ (44175291979967/100000000000000 : ℝ)^6259 := by
    have hnat : (1350817159 : ℕ)^8307*100000000000000^6259 ≤ 44175291979967^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350817159 2500000000 44175291979967 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256124977/10000000000 : ℝ)^8307 ≤ (21292910830139/50000000000000 : ℝ)^6259 := by
    have hnat : (5256124977 : ℕ)^8307*50000000000000^6259 ≤ 21292910830139^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256124977 10000000000 21292910830139 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435892473/2000000000 : ℝ), (1350817159/2500000000 : ℝ), (5256124977/10000000000 : ℝ)] ![(6619443174051/50000000000000 : ℝ), (44175291979967/100000000000000 : ℝ), (21292910830139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435892473/2000000000 : ℝ)|^8307 ≤ (6619443174051/50000000000000 : ℝ)^6259
        have hw : |(-435892473/2000000000 : ℝ)|=(435892473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350817159/2500000000 : ℝ)|^8307 ≤ (44175291979967/100000000000000 : ℝ)^6259
        have hw : |(1350817159/2500000000 : ℝ)|=(1350817159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256124977/10000000000 : ℝ)|^8307 ≤ (21292910830139/50000000000000 : ℝ)^6259
        have hw : |(5256124977/10000000000 : ℝ)|=(5256124977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s4_1 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069457863/2000000000 : ℝ)*x 0 + (-2254261407/10000000000 : ℝ)*x 1 + (5256125057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069457863/2000000000 : ℝ)^8307 ≤ (10892225755049/25000000000000 : ℝ)^6259 := by
    have hnat : (1069457863 : ℕ)^8307*25000000000000^6259 ≤ 10892225755049^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069457863 2000000000 10892225755049 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254261407/10000000000 : ℝ)^8307 ≤ (13845274449373/100000000000000 : ℝ)^6259 := by
    have hnat : (2254261407 : ℕ)^8307*100000000000000^6259 ≤ 13845274449373^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254261407 10000000000 13845274449373 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256125057/10000000000 : ℝ)^8307 ≤ (5323227815067/12500000000000 : ℝ)^6259 := by
    have hnat : (5256125057 : ℕ)^8307*12500000000000^6259 ≤ 5323227815067^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256125057 10000000000 5323227815067 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069457863/2000000000 : ℝ), (-2254261407/10000000000 : ℝ), (5256125057/10000000000 : ℝ)] ![(10892225755049/25000000000000 : ℝ), (13845274449373/100000000000000 : ℝ), (5323227815067/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069457863/2000000000 : ℝ)|^8307 ≤ (10892225755049/25000000000000 : ℝ)^6259
        have hw : |(1069457863/2000000000 : ℝ)|=(1069457863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2254261407/10000000000 : ℝ)|^8307 ≤ (13845274449373/100000000000000 : ℝ)^6259
        have hw : |(-2254261407/10000000000 : ℝ)|=(2254261407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256125057/10000000000 : ℝ)|^8307 ≤ (5323227815067/12500000000000 : ℝ)^6259
        have hw : |(5256125057/10000000000 : ℝ)|=(5256125057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s4_2 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673644609/5000000000 : ℝ)*x 0 + (1051224989/2000000000 : ℝ)*x 1 + (-2254261683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673644609/5000000000 : ℝ)^8307 ≤ (2723056373203/6250000000000 : ℝ)^6259 := by
    have hnat : (2673644609 : ℕ)^8307*6250000000000^6259 ≤ 2723056373203^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673644609 5000000000 2723056373203 6250000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051224989/2000000000 : ℝ)^8307 ≤ (1703432852647/4000000000000 : ℝ)^6259 := by
    have hnat : (1051224989 : ℕ)^8307*4000000000000^6259 ≤ 1703432852647^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051224989 2000000000 1703432852647 4000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254261683/10000000000 : ℝ)^8307 ≤ (6922638349591/50000000000000 : ℝ)^6259 := by
    have hnat : (2254261683 : ℕ)^8307*50000000000000^6259 ≤ 6922638349591^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254261683 10000000000 6922638349591 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673644609/5000000000 : ℝ), (1051224989/2000000000 : ℝ), (-2254261683/10000000000 : ℝ)] ![(2723056373203/6250000000000 : ℝ), (1703432852647/4000000000000 : ℝ), (6922638349591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673644609/5000000000 : ℝ)|^8307 ≤ (2723056373203/6250000000000 : ℝ)^6259
        have hw : |(2673644609/5000000000 : ℝ)|=(2673644609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051224989/2000000000 : ℝ)|^8307 ≤ (1703432852647/4000000000000 : ℝ)^6259
        have hw : |(1051224989/2000000000 : ℝ)|=(1051224989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2254261683/10000000000 : ℝ)|^8307 ≤ (6922638349591/50000000000000 : ℝ)^6259
        have hw : |(-2254261683/10000000000 : ℝ)|=(2254261683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s4_3 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184058507/5000000000 : ℝ)*x 0 + (2112489809/5000000000 : ℝ)*x 1 + (17641061/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184058507/5000000000 : ℝ)^8307 ≤ (33311590923159/100000000000000 : ℝ)^6259 := by
    have hnat : (2184058507 : ℕ)^8307*100000000000000^6259 ≤ 33311590923159^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184058507 5000000000 33311590923159 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112489809/5000000000 : ℝ)^8307 ≤ (15935332790271/50000000000000 : ℝ)^6259 := by
    have hnat : (2112489809 : ℕ)^8307*50000000000000^6259 ≤ 15935332790271^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112489809 5000000000 15935332790271 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17641061/39062500 : ℝ)^8307 ≤ (17408871740801/50000000000000 : ℝ)^6259 := by
    have hnat : (17641061 : ℕ)^8307*50000000000000^6259 ≤ 17408871740801^6259*39062500^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17641061 39062500 17408871740801 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184058507/5000000000 : ℝ), (2112489809/5000000000 : ℝ), (17641061/39062500 : ℝ)] ![(33311590923159/100000000000000 : ℝ), (15935332790271/50000000000000 : ℝ), (17408871740801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184058507/5000000000 : ℝ)|^8307 ≤ (33311590923159/100000000000000 : ℝ)^6259
        have hw : |(2184058507/5000000000 : ℝ)|=(2184058507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112489809/5000000000 : ℝ)|^8307 ≤ (15935332790271/50000000000000 : ℝ)^6259
        have hw : |(2112489809/5000000000 : ℝ)|=(2112489809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17641061/39062500 : ℝ)|^8307 ≤ (17408871740801/50000000000000 : ℝ)^6259
        have hw : |(17641061/39062500 : ℝ)|=(17641061/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s4_4 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179469867/10000000000 : ℝ)*x 0 + (525654831/1000000000 : ℝ)*x 1 + (2701421763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179469867/10000000000 : ℝ)^8307 ≤ (6619473414529/50000000000000 : ℝ)^6259 := by
    have hnat : (2179469867 : ℕ)^8307*50000000000000^6259 ≤ 6619473414529^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179469867 10000000000 6619473414529 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525654831/1000000000 : ℝ)^8307 ≤ (42590373913937/100000000000000 : ℝ)^6259 := by
    have hnat : (525654831 : ℕ)^8307*100000000000000^6259 ≤ 42590373913937^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525654831 1000000000 42590373913937 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701421763/5000000000 : ℝ)^8307 ≤ (44170679251837/100000000000000 : ℝ)^6259 := by
    have hnat : (2701421763 : ℕ)^8307*100000000000000^6259 ≤ 44170679251837^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701421763 5000000000 44170679251837 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179469867/10000000000 : ℝ), (525654831/1000000000 : ℝ), (2701421763/5000000000 : ℝ)] ![(6619473414529/50000000000000 : ℝ), (42590373913937/100000000000000 : ℝ), (44170679251837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179469867/10000000000 : ℝ)|^8307 ≤ (6619473414529/50000000000000 : ℝ)^6259
        have hw : |(-2179469867/10000000000 : ℝ)|=(2179469867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525654831/1000000000 : ℝ)|^8307 ≤ (42590373913937/100000000000000 : ℝ)^6259
        have hw : |(525654831/1000000000 : ℝ)|=(525654831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701421763/5000000000 : ℝ)|^8307 ≤ (44170679251837/100000000000000 : ℝ)^6259
        have hw : |(2701421763/5000000000 : ℝ)|=(2701421763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s4_5 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310089637/10000000000 : ℝ)*x 0 + (-210754333/1000000000 : ℝ)*x 1 + (5402843699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310089637/10000000000 : ℝ)^8307 ≤ (4316708812353/10000000000000 : ℝ)^6259 := by
    have hnat : (5310089637 : ℕ)^8307*10000000000000^6259 ≤ 4316708812353^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310089637 10000000000 4316708812353 10000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210754333/1000000000 : ℝ)^8307 ≤ (3165557684831/25000000000000 : ℝ)^6259 := by
    have hnat : (210754333 : ℕ)^8307*25000000000000^6259 ≤ 3165557684831^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210754333 1000000000 3165557684831 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402843699/10000000000 : ℝ)^8307 ≤ (44170681128979/100000000000000 : ℝ)^6259 := by
    have hnat : (5402843699 : ℕ)^8307*100000000000000^6259 ≤ 44170681128979^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402843699 10000000000 44170681128979 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310089637/10000000000 : ℝ), (-210754333/1000000000 : ℝ), (5402843699/10000000000 : ℝ)] ![(4316708812353/10000000000000 : ℝ), (3165557684831/25000000000000 : ℝ), (44170681128979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310089637/10000000000 : ℝ)|^8307 ≤ (4316708812353/10000000000000 : ℝ)^6259
        have hw : |(5310089637/10000000000 : ℝ)|=(5310089637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210754333/1000000000 : ℝ)|^8307 ≤ (3165557684831/25000000000000 : ℝ)^6259
        have hw : |(-210754333/1000000000 : ℝ)|=(210754333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402843699/10000000000 : ℝ)|^8307 ≤ (44170681128979/100000000000000 : ℝ)^6259
        have hw : |(5402843699/10000000000 : ℝ)|=(5402843699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s4_6 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663761233/1250000000 : ℝ)*x 0 + (1350710929/2500000000 : ℝ)*x 1 + (-1053771499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663761233/1250000000 : ℝ)^8307 ≤ (10791772643171/25000000000000 : ℝ)^6259 := by
    have hnat : (663761233 : ℕ)^8307*25000000000000^6259 ≤ 10791772643171^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663761233 1250000000 10791772643171 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350710929/2500000000 : ℝ)^8307 ≤ (22085340656719/50000000000000 : ℝ)^6259 := by
    have hnat : (1350710929 : ℕ)^8307*50000000000000^6259 ≤ 22085340656719^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350710929 2500000000 22085340656719 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053771499/5000000000 : ℝ)^8307 ≤ (1582778511497/12500000000000 : ℝ)^6259 := by
    have hnat : (1053771499 : ℕ)^8307*12500000000000^6259 ≤ 1582778511497^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053771499 5000000000 1582778511497 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663761233/1250000000 : ℝ), (1350710929/2500000000 : ℝ), (-1053771499/5000000000 : ℝ)] ![(10791772643171/25000000000000 : ℝ), (22085340656719/50000000000000 : ℝ), (1582778511497/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663761233/1250000000 : ℝ)|^8307 ≤ (10791772643171/25000000000000 : ℝ)^6259
        have hw : |(663761233/1250000000 : ℝ)|=(663761233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350710929/2500000000 : ℝ)|^8307 ≤ (22085340656719/50000000000000 : ℝ)^6259
        have hw : |(1350710929/2500000000 : ℝ)|=(1350710929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1053771499/5000000000 : ℝ)|^8307 ≤ (1582778511497/12500000000000 : ℝ)^6259
        have hw : |(-1053771499/5000000000 : ℝ)|=(1053771499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s4_7 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368132539/10000000000 : ℝ)*x 0 + (2257636771/5000000000 : ℝ)*x 1 + (4225820417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368132539/10000000000 : ℝ)^8307 ≤ (16655874028953/50000000000000 : ℝ)^6259 := by
    have hnat : (4368132539 : ℕ)^8307*50000000000000^6259 ≤ 16655874028953^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368132539 10000000000 16655874028953 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257636771/5000000000 : ℝ)^8307 ≤ (6961833655781/20000000000000 : ℝ)^6259 := by
    have hnat : (2257636771 : ℕ)^8307*20000000000000^6259 ≤ 6961833655781^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257636771 5000000000 6961833655781 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225820417/10000000000 : ℝ)^8307 ≤ (6375816728429/20000000000000 : ℝ)^6259 := by
    have hnat : (4225820417 : ℕ)^8307*20000000000000^6259 ≤ 6375816728429^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225820417 10000000000 6375816728429 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368132539/10000000000 : ℝ), (2257636771/5000000000 : ℝ), (4225820417/10000000000 : ℝ)] ![(16655874028953/50000000000000 : ℝ), (6961833655781/20000000000000 : ℝ), (6375816728429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368132539/10000000000 : ℝ)|^8307 ≤ (16655874028953/50000000000000 : ℝ)^6259
        have hw : |(4368132539/10000000000 : ℝ)|=(4368132539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257636771/5000000000 : ℝ)|^8307 ≤ (6961833655781/20000000000000 : ℝ)^6259
        have hw : |(2257636771/5000000000 : ℝ)|=(2257636771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225820417/10000000000 : ℝ)|^8307 ≤ (6375816728429/20000000000000 : ℝ)^6259
        have hw : |(4225820417/10000000000 : ℝ)|=(4225820417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1114_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (371/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (211/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (11121/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (371/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (211/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (371/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (211/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (371/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (211/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (371/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (211/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (371/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (211/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (371/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (211/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (211/2000 : ℝ) ^ (4153/1024 : ℝ) ≤ (5465250928974783/50000000000000000000 : ℝ) := by
    have hpowers : (211/2000 : ℝ)^4153 ≤ (5465250928974783/50000000000000000000 : ℝ)^1024 := by
      have hnat : (211 : ℕ)^4153*50000000000000000000^1024 ≤ 5465250928974783^1024*2000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        211 2000 5465250928974783 50000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (211/2000 : ℝ)) (X := (5465250928974783/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (371/2500 : ℝ) ^ (4153/1024 : ℝ) ≤ (43612827997166247/100000000000000000000 : ℝ) := by
    have hpowers : (371/2500 : ℝ)^4153 ≤ (43612827997166247/100000000000000000000 : ℝ)^1024 := by
      have hnat : (371 : ℕ)^4153*100000000000000000000^1024 ≤ 43612827997166247^1024*2500^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        371 2500 43612827997166247 100000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (371/2500 : ℝ)) (X := (43612827997166247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005465250928974783/25000000000000000000 : ℝ) ≤ (10000538979641113/10000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (25005465250928974783/25000000000000000000 : ℝ)^1024 ≤ (10000538979641113/10000000000000000 : ℝ)^4153 := by
      have hnat : (25005465250928974783 : ℕ)^1024*10000000000000000^4153 ≤ 10000538979641113^4153*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005465250928974783 25000000000000000000 10000538979641113 10000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538979641113/10000000000000000 : ℝ)) (X := (25005465250928974783/25000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054543329855115813/100000000000000000000 : ℝ) ≤ (5000672295897677/5000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (100054543329855115813/100000000000000000000 : ℝ)^1024 ≤ (5000672295897677/5000000000000000 : ℝ)^4153 := by
      have hnat : (100054543329855115813 : ℕ)^1024*5000000000000000^4153 ≤ 5000672295897677^4153*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054543329855115813 100000000000000000000 5000672295897677 5000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000672295897677/5000000000000000 : ℝ)) (X := (100054543329855115813/100000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043612827997166247/50000000000000000000 : ℝ) ≤ (2000430040789919/2000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50043612827997166247/50000000000000000000 : ℝ)^1024 ≤ (2000430040789919/2000000000000000 : ℝ)^4153 := by
      have hnat : (50043612827997166247 : ℕ)^1024*2000000000000000^4153 ≤ 2000430040789919^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043612827997166247 50000000000000000000 2000430040789919 2000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000430040789919/2000000000000000 : ℝ)) (X := (50043612827997166247/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5465250928974783/50000000000000000000 : ℝ) ≤ ((1429510460206862989/1430000000000000000 : ℝ)+2*(268537384747/143000000000000 : ℝ)*(211/2000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (1429510460206862989/1430000000000000000 : ℝ)+2*(268537384747/143000000000000 : ℝ)*(211/2000 : ℝ)=(10000538979641113/10000000000000000 : ℝ) by norm_num, show 1+2*(5465250928974783/50000000000000000000 : ℝ)=(25005465250928974783/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43612827997166247/100000000000000000000 : ℝ)+(5465250928974783/50000000000000000000 : ℝ) ≤ ((1429510460206862989/1430000000000000000 : ℝ)+(268537384747/143000000000000 : ℝ)*((371/2500 : ℝ)+(211/2000 : ℝ)))^(4153/1024 : ℝ) := by
    rw [show (1429510460206862989/1430000000000000000 : ℝ)+(268537384747/143000000000000 : ℝ)*((371/2500 : ℝ)+(211/2000 : ℝ))=(5000672295897677/5000000000000000 : ℝ) by norm_num, show 1+(43612827997166247/100000000000000000000 : ℝ)+(5465250928974783/50000000000000000000 : ℝ)=(100054543329855115813/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43612827997166247/100000000000000000000 : ℝ) ≤ ((1429510460206862989/1430000000000000000 : ℝ)+2*(268537384747/143000000000000 : ℝ)*(371/2500 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (1429510460206862989/1430000000000000000 : ℝ)+2*(268537384747/143000000000000 : ℝ)*(371/2500 : ℝ)=(2000430040789919/2000000000000000 : ℝ) by norm_num, show 1+2*(43612827997166247/100000000000000000000 : ℝ)=(50043612827997166247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1429510460206862989/1430000000000000000 : ℝ)*(X 1 0+X 2 0)+(268537384747/143000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (211/2000 : ℝ)) (hi := (371/2500 : ℝ)) (c := (1429510460206862989/1430000000000000000 : ℝ)) (alpha := (268537384747/143000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1429510460206862989/1430000000000000000 : ℝ)*(X 0 1+X 2 1)+(268537384747/143000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (211/2000 : ℝ)) (hi := (371/2500 : ℝ)) (c := (1429510460206862989/1430000000000000000 : ℝ)) (alpha := (268537384747/143000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1429510460206862989/1430000000000000000 : ℝ)*(X 0 2+X 1 2)+(268537384747/143000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (211/2000 : ℝ)) (hi := (371/2500 : ℝ)) (c := (1429510460206862989/1430000000000000000 : ℝ)) (alpha := (268537384747/143000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-435892473/2000000000 : ℝ)*X 0 0+(1350817159/2500000000 : ℝ)*X 0 1+(5256124977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069457863/2000000000 : ℝ)*X 1 0+(-2254261407/10000000000 : ℝ)*X 1 1+(5256125057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673644609/5000000000 : ℝ)*X 2 0+(1051224989/2000000000 : ℝ)*X 2 1+(-2254261683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184058507/5000000000 : ℝ)*X 0 0+(2112489809/5000000000 : ℝ)*X 0 1+(17641061/39062500 : ℝ)*X 0 2+(2184058507/5000000000 : ℝ)*X 1 0+(2112489809/5000000000 : ℝ)*X 1 1+(17641061/39062500 : ℝ)*X 1 2+(2184058507/5000000000 : ℝ)*X 2 0+(2112489809/5000000000 : ℝ)*X 2 1+(17641061/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2179469867/10000000000 : ℝ)*X 0 0+(525654831/1000000000 : ℝ)*X 0 1+(2701421763/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310089637/10000000000 : ℝ)*X 1 0+(-210754333/1000000000 : ℝ)*X 1 1+(5402843699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663761233/1250000000 : ℝ)*X 2 0+(1350710929/2500000000 : ℝ)*X 2 1+(-1053771499/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368132539/10000000000 : ℝ)*X 0 0+(2257636771/5000000000 : ℝ)*X 0 1+(4225820417/10000000000 : ℝ)*X 0 2+(4368132539/10000000000 : ℝ)*X 1 0+(2257636771/5000000000 : ℝ)*X 1 1+(4225820417/10000000000 : ℝ)*X 1 2+(4368132539/10000000000 : ℝ)*X 2 0+(2257636771/5000000000 : ℝ)*X 2 1+(4225820417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3946019626344522308602593/650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (298009761/20000000000000 : ℝ)*(base19) + (709307021/50000000000000 : ℝ)*(base23) + (8022413/25000000000000 : ℝ)*(upper2) + (66700339/20000000000000 : ℝ)*(upper3) + (1023106420574469/20000000000000 : ℝ)*(major0) + (1023106420574469/20000000000000 : ℝ)*(major1) + (1023106420574469/20000000000000 : ℝ)*(major2) + (6796124813495909/100000000000000 : ℝ)*(sp0) + (67961524764109/1000000000000 : ℝ)*(sp1) + (1699037843595659/25000000000000 : ℝ)*(sp2) + (429360806638047/12500000000000 : ℝ)*(sp3) + (7288240949/25000000000000 : ℝ)*(sp4) + (293365757/25000000000000 : ℝ)*(sp6) + (23583820621/100000000000000 : ℝ)*(sp7) + (1717455018462499/50000000000000 : ℝ)*(f.failure) + (1359230793291941/20000000000000 : ℝ)*(f.sum) + (7583006367/130000000000000000000000000 : ℝ)*base66 + (3783478095867469/2600000000000000000000000000000 : ℝ)*base68 + (6637993931332531/2600000000000000000000000000000 : ℝ)*base69 + (8591815783267469/2600000000000000000000000000000 : ℝ)*base72 + (73544587713/130000000000000000000000000 : ℝ)*base73 + (19374271597267469/2600000000000000000000000000000 : ℝ)*base76 + (25573022467267469/2600000000000000000000000000000 : ℝ)*base78 + (19054817774267469/2600000000000000000000000000000 : ℝ)*base80 + (118387490883/130000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5096539/625000000000000000000 : ℝ)*base89 + (5096539/625000000000000000000 : ℝ)*base91 + (5096539/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27208910249589847693911/3575000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102684473/10000000000000 : ℝ)*(base19) + (192520933/10000000000000 : ℝ)*(base23) + (180800947/50000000000000 : ℝ)*(upper3) + (42844381/20000000000000 : ℝ)*(lower4) + (40663697/12500000000000 : ℝ)*(upper5) + (2572570768643679/50000000000000 : ℝ)*(major0) + (2572570768643679/50000000000000 : ℝ)*(major1) + (2572570768643679/50000000000000 : ℝ)*(major2) + (7794124529/50000000000000 : ℝ)*(sp1) + (11131909169/25000000000000 : ℝ)*(sp2) + (3417745515698963/50000000000000 : ℝ)*(sp4) + (6835474416304137/100000000000000 : ℝ)*(sp5) + (85443057231899/1250000000000 : ℝ)*(sp6) + (3454791789480649/100000000000000 : ℝ)*(sp7) + (3454791789480649/100000000000000 : ℝ)*(f.failure) + (3417745515698963/50000000000000 : ℝ)*(f.sum) + (3210046262519/1787500000000000000000000000 : ℝ)*base65 + (845778083430973469/71500000000000000000000000000000 : ℝ)*base68 + (565000721637473469/71500000000000000000000000000000 : ℝ)*base70 + (768235208031026531/71500000000000000000000000000000 : ℝ)*base71 + (17914882328437/3575000000000000000000000000 : ℝ)*base74 + (96402735863026531/71500000000000000000000000000000 : ℝ)*base75 + (506562746337526531/71500000000000000000000000000000 : ℝ)*base77 + (782816075750973469/71500000000000000000000000000000 : ℝ)*base80 + (5107608364669/1787500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2961311/1250000000000000000000 : ℝ)*base90 + (2961311/1250000000000000000000 : ℝ)*base92 + (2961311/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1114_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (371/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (211/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1114_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1114_s5_0 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180162893/10000000000 : ℝ)*x 0 + (539566013/1000000000 : ℝ)*x 1 + (263163697/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180162893/10000000000 : ℝ)^8307 ≤ (13244534282883/100000000000000 : ℝ)^6259 := by
    have hnat : (2180162893 : ℕ)^8307*100000000000000^6259 ≤ 13244534282883^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180162893 10000000000 13244534282883 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539566013/1000000000 : ℝ)^8307 ≤ (8818550511693/20000000000000 : ℝ)^6259 := by
    have hnat : (539566013 : ℕ)^8307*20000000000000^6259 ≤ 8818550511693^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539566013 1000000000 8818550511693 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263163697/500000000 : ℝ)^8307 ≤ (42662713146603/100000000000000 : ℝ)^6259 := by
    have hnat : (263163697 : ℕ)^8307*100000000000000^6259 ≤ 42662713146603^6259*500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263163697 500000000 42662713146603 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180162893/10000000000 : ℝ), (539566013/1000000000 : ℝ), (263163697/500000000 : ℝ)] ![(13244534282883/100000000000000 : ℝ), (8818550511693/20000000000000 : ℝ), (42662713146603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180162893/10000000000 : ℝ)|^8307 ≤ (13244534282883/100000000000000 : ℝ)^6259
        have hw : |(-2180162893/10000000000 : ℝ)|=(2180162893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539566013/1000000000 : ℝ)|^8307 ≤ (8818550511693/20000000000000 : ℝ)^6259
        have hw : |(539566013/1000000000 : ℝ)|=(539566013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263163697/500000000 : ℝ)|^8307 ≤ (42662713146603/100000000000000 : ℝ)^6259
        have hw : |(263163697/500000000 : ℝ)|=(263163697/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s5_1 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345386003/10000000000 : ℝ)*x 0 + (-1123674739/5000000000 : ℝ)*x 1 + (1052654873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345386003/10000000000 : ℝ)^8307 ≤ (43548322000197/100000000000000 : ℝ)^6259 := by
    have hnat : (5345386003 : ℕ)^8307*100000000000000^6259 ≤ 43548322000197^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345386003 10000000000 43548322000197 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123674739/5000000000 : ℝ)^8307 ≤ (689448013517/5000000000000 : ℝ)^6259 := by
    have hnat : (1123674739 : ℕ)^8307*5000000000000^6259 ≤ 689448013517^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123674739 5000000000 689448013517 5000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052654873/2000000000 : ℝ)^8307 ≤ (10665679429689/25000000000000 : ℝ)^6259 := by
    have hnat : (1052654873 : ℕ)^8307*25000000000000^6259 ≤ 10665679429689^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052654873 2000000000 10665679429689 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345386003/10000000000 : ℝ), (-1123674739/5000000000 : ℝ), (1052654873/2000000000 : ℝ)] ![(43548322000197/100000000000000 : ℝ), (689448013517/5000000000000 : ℝ), (10665679429689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345386003/10000000000 : ℝ)|^8307 ≤ (43548322000197/100000000000000 : ℝ)^6259
        have hw : |(5345386003/10000000000 : ℝ)|=(5345386003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123674739/5000000000 : ℝ)|^8307 ≤ (689448013517/5000000000000 : ℝ)^6259
        have hw : |(-1123674739/5000000000 : ℝ)|=(1123674739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052654873/2000000000 : ℝ)|^8307 ≤ (10665679429689/25000000000000 : ℝ)^6259
        have hw : |(1052654873/2000000000 : ℝ)|=(1052654873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s5_2 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336346591/2500000000 : ℝ)*x 0 + (5263274029/10000000000 : ℝ)*x 1 + (-2247349441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336346591/2500000000 : ℝ)^8307 ≤ (43548325903559/100000000000000 : ℝ)^6259 := by
    have hnat : (1336346591 : ℕ)^8307*100000000000000^6259 ≤ 43548325903559^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336346591 2500000000 43548325903559 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263274029/10000000000 : ℝ)^8307 ≤ (21331357052033/50000000000000 : ℝ)^6259 := by
    have hnat : (5263274029 : ℕ)^8307*50000000000000^6259 ≤ 21331357052033^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263274029 10000000000 21331357052033 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247349441/10000000000 : ℝ)^8307 ≤ (6894479984519/50000000000000 : ℝ)^6259 := by
    have hnat : (2247349441 : ℕ)^8307*50000000000000^6259 ≤ 6894479984519^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247349441 10000000000 6894479984519 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336346591/2500000000 : ℝ), (5263274029/10000000000 : ℝ), (-2247349441/10000000000 : ℝ)] ![(43548325903559/100000000000000 : ℝ), (21331357052033/50000000000000 : ℝ), (6894479984519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336346591/2500000000 : ℝ)|^8307 ≤ (43548325903559/100000000000000 : ℝ)^6259
        have hw : |(1336346591/2500000000 : ℝ)|=(1336346591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263274029/10000000000 : ℝ)|^8307 ≤ (21331357052033/50000000000000 : ℝ)^6259
        have hw : |(5263274029/10000000000 : ℝ)|=(5263274029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2247349441/10000000000 : ℝ)|^8307 ≤ (6894479984519/50000000000000 : ℝ)^6259
        have hw : |(-2247349441/10000000000 : ℝ)|=(2247349441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s5_3 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092131557/2500000000 : ℝ)*x 0 + (529940731/1250000000 : ℝ)*x 1 + (281341159/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092131557/2500000000 : ℝ)^8307 ≤ (3331573280313/10000000000000 : ℝ)^6259 := by
    have hnat : (1092131557 : ℕ)^8307*10000000000000^6259 ≤ 3331573280313^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092131557 2500000000 3331573280313 10000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529940731/1250000000 : ℝ)^8307 ≤ (6403275870081/20000000000000 : ℝ)^6259 := by
    have hnat : (529940731 : ℕ)^8307*20000000000000^6259 ≤ 6403275870081^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529940731 1250000000 6403275870081 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281341159/625000000 : ℝ)^8307 ≤ (8666971957269/25000000000000 : ℝ)^6259 := by
    have hnat : (281341159 : ℕ)^8307*25000000000000^6259 ≤ 8666971957269^6259*625000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281341159 625000000 8666971957269 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092131557/2500000000 : ℝ), (529940731/1250000000 : ℝ), (281341159/625000000 : ℝ)] ![(3331573280313/10000000000000 : ℝ), (6403275870081/20000000000000 : ℝ), (8666971957269/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092131557/2500000000 : ℝ)|^8307 ≤ (3331573280313/10000000000000 : ℝ)^6259
        have hw : |(1092131557/2500000000 : ℝ)|=(1092131557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529940731/1250000000 : ℝ)|^8307 ≤ (6403275870081/20000000000000 : ℝ)^6259
        have hw : |(529940731/1250000000 : ℝ)|=(529940731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281341159/625000000 : ℝ)|^8307 ≤ (8666971957269/25000000000000 : ℝ)^6259
        have hw : |(281341159/625000000 : ℝ)|=(281341159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s5_4 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-545042077/2500000000 : ℝ)*x 0 + (1315904259/2500000000 : ℝ)*x 1 + (5395315779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545042077/2500000000 : ℝ)^8307 ≤ (529783117723/4000000000000 : ℝ)^6259 := by
    have hnat : (545042077 : ℕ)^8307*4000000000000^6259 ≤ 529783117723^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545042077 2500000000 529783117723 4000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315904259/2500000000 : ℝ)^8307 ≤ (42666404214567/100000000000000 : ℝ)^6259 := by
    have hnat : (1315904259 : ℕ)^8307*100000000000000^6259 ≤ 42666404214567^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315904259 2500000000 42666404214567 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395315779/10000000000 : ℝ)^8307 ≤ (44089017832869/100000000000000 : ℝ)^6259 := by
    have hnat : (5395315779 : ℕ)^8307*100000000000000^6259 ≤ 44089017832869^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395315779 10000000000 44089017832869 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545042077/2500000000 : ℝ), (1315904259/2500000000 : ℝ), (5395315779/10000000000 : ℝ)] ![(529783117723/4000000000000 : ℝ), (42666404214567/100000000000000 : ℝ), (44089017832869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545042077/2500000000 : ℝ)|^8307 ≤ (529783117723/4000000000000 : ℝ)^6259
        have hw : |(-545042077/2500000000 : ℝ)|=(545042077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315904259/2500000000 : ℝ)|^8307 ≤ (42666404214567/100000000000000 : ℝ)^6259
        have hw : |(1315904259/2500000000 : ℝ)|=(1315904259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395315779/10000000000 : ℝ)|^8307 ≤ (44089017832869/100000000000000 : ℝ)^6259
        have hw : |(5395315779/10000000000 : ℝ)|=(5395315779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s5_5 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327979131/2500000000 : ℝ)*x 0 + (-1057653961/5000000000 : ℝ)*x 1 + (2697657881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327979131/2500000000 : ℝ)^8307 ≤ (10796699980931/25000000000000 : ℝ)^6259 := by
    have hnat : (1327979131 : ℕ)^8307*25000000000000^6259 ≤ 10796699980931^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327979131 2500000000 10796699980931 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057653961/5000000000 : ℝ)^8307 ≤ (12724182419077/100000000000000 : ℝ)^6259 := by
    have hnat : (1057653961 : ℕ)^8307*100000000000000^6259 ≤ 12724182419077^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057653961 5000000000 12724182419077 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697657881/5000000000 : ℝ)^8307 ≤ (22044508824247/50000000000000 : ℝ)^6259 := by
    have hnat : (2697657881 : ℕ)^8307*50000000000000^6259 ≤ 22044508824247^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697657881 5000000000 22044508824247 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327979131/2500000000 : ℝ), (-1057653961/5000000000 : ℝ), (2697657881/5000000000 : ℝ)] ![(10796699980931/25000000000000 : ℝ), (12724182419077/100000000000000 : ℝ), (22044508824247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327979131/2500000000 : ℝ)|^8307 ≤ (10796699980931/25000000000000 : ℝ)^6259
        have hw : |(1327979131/2500000000 : ℝ)|=(1327979131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057653961/5000000000 : ℝ)|^8307 ≤ (12724182419077/100000000000000 : ℝ)^6259
        have hw : |(-1057653961/5000000000 : ℝ)|=(1057653961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697657881/5000000000 : ℝ)|^8307 ≤ (22044508824247/50000000000000 : ℝ)^6259
        have hw : |(2697657881/5000000000 : ℝ)|=(2697657881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s5_6 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311916509/10000000000 : ℝ)*x 0 + (1348828943/2500000000 : ℝ)*x 1 + (-2115307929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311916509/10000000000 : ℝ)^8307 ≤ (43186799761867/100000000000000 : ℝ)^6259 := by
    have hnat : (5311916509 : ℕ)^8307*100000000000000^6259 ≤ 43186799761867^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311916509 10000000000 43186799761867 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348828943/2500000000 : ℝ)^8307 ≤ (881780355139/2000000000000 : ℝ)^6259 := by
    have hnat : (1348828943 : ℕ)^8307*2000000000000^6259 ≤ 881780355139^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348828943 2500000000 881780355139 2000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115307929/10000000000 : ℝ)^8307 ≤ (6362091237481/50000000000000 : ℝ)^6259 := by
    have hnat : (2115307929 : ℕ)^8307*50000000000000^6259 ≤ 6362091237481^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115307929 10000000000 6362091237481 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311916509/10000000000 : ℝ), (1348828943/2500000000 : ℝ), (-2115307929/10000000000 : ℝ)] ![(43186799761867/100000000000000 : ℝ), (881780355139/2000000000000 : ℝ), (6362091237481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311916509/10000000000 : ℝ)|^8307 ≤ (43186799761867/100000000000000 : ℝ)^6259
        have hw : |(5311916509/10000000000 : ℝ)|=(5311916509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348828943/2500000000 : ℝ)|^8307 ≤ (881780355139/2000000000000 : ℝ)^6259
        have hw : |(1348828943/2500000000 : ℝ)|=(1348828943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2115307929/10000000000 : ℝ)|^8307 ≤ (6362091237481/50000000000000 : ℝ)^6259
        have hw : |(-2115307929/10000000000 : ℝ)|=(2115307929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s5_7 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218426839/500000000 : ℝ)*x 0 + (70324689/156250000 : ℝ)*x 1 + (848041409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218426839/500000000 : ℝ)^8307 ≤ (6663167921481/20000000000000 : ℝ)^6259 := by
    have hnat : (218426839 : ℕ)^8307*20000000000000^6259 ≤ 6663167921481^6259*500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218426839 500000000 6663167921481 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70324689/156250000 : ℝ)^8307 ≤ (17330476631873/50000000000000 : ℝ)^6259 := by
    have hnat : (70324689 : ℕ)^8307*50000000000000^6259 ≤ 17330476631873^6259*156250000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70324689 156250000 17330476631873 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848041409/2000000000 : ℝ)^8307 ≤ (32023207111729/100000000000000 : ℝ)^6259 := by
    have hnat : (848041409 : ℕ)^8307*100000000000000^6259 ≤ 32023207111729^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848041409 2000000000 32023207111729 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218426839/500000000 : ℝ), (70324689/156250000 : ℝ), (848041409/2000000000 : ℝ)] ![(6663167921481/20000000000000 : ℝ), (17330476631873/50000000000000 : ℝ), (32023207111729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218426839/500000000 : ℝ)|^8307 ≤ (6663167921481/20000000000000 : ℝ)^6259
        have hw : |(218426839/500000000 : ℝ)|=(218426839/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70324689/156250000 : ℝ)|^8307 ≤ (17330476631873/50000000000000 : ℝ)^6259
        have hw : |(70324689/156250000 : ℝ)|=(70324689/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848041409/2000000000 : ℝ)|^8307 ≤ (32023207111729/100000000000000 : ℝ)^6259
        have hw : |(848041409/2000000000 : ℝ)|=(848041409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1114_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11273/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14077/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11121/100000 : ℝ) ^ (4153/1024 : ℝ) ≤ (3383918251277779/25000000000000000000 : ℝ) := by
    have hpowers : (11121/100000 : ℝ)^4153 ≤ (3383918251277779/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11121 : ℕ)^4153*25000000000000000000^1024 ≤ 3383918251277779^1024*100000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11121 100000 3383918251277779 25000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11121/100000 : ℝ)) (X := (3383918251277779/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (4153/1024 : ℝ) ≤ (36859528354320539/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^4153 ≤ (36859528354320539/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14237 : ℕ)^4153*100000000000000000000^1024 ≤ 36859528354320539^1024*100000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 36859528354320539 100000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (36859528354320539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503383918251277779/12500000000000000000 : ℝ) ≤ (2500166856680189/2500000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (12503383918251277779/12500000000000000000 : ℝ)^1024 ≤ (2500166856680189/2500000000000000 : ℝ)^4153 := by
      have hnat : (12503383918251277779 : ℕ)^1024*2500000000000000^4153 ≤ 2500166856680189^4153*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503383918251277779 12500000000000000000 2500166856680189 2500000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500166856680189/2500000000000000 : ℝ)) (X := (12503383918251277779/12500000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010079040271886331/20000000000000000000 : ℝ) ≤ (2500310588081523/2500000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (20010079040271886331/20000000000000000000 : ℝ)^1024 ≤ (2500310588081523/2500000000000000 : ℝ)^4153 := by
      have hnat : (20010079040271886331 : ℕ)^1024*2500000000000000^4153 ≤ 2500310588081523^4153*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010079040271886331 20000000000000000000 2500310588081523 2500000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500310588081523/2500000000000000 : ℝ)) (X := (20010079040271886331/20000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036859528354320539/50000000000000000000 : ℝ) ≤ (2500454319482857/2500000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50036859528354320539/50000000000000000000 : ℝ)^1024 ≤ (2500454319482857/2500000000000000 : ℝ)^4153 := by
      have hnat : (50036859528354320539 : ℕ)^1024*2500000000000000^4153 ≤ 2500454319482857^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036859528354320539 50000000000000000000 2500454319482857 2500000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500454319482857/2500000000000000 : ℝ)) (X := (50036859528354320539/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3383918251277779/25000000000000000000 : ℝ) ≤ ((486707690724187381/486875000000000000 : ℝ)+2*(71865700667/38950000000000 : ℝ)*(11121/100000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (486707690724187381/486875000000000000 : ℝ)+2*(71865700667/38950000000000 : ℝ)*(11121/100000 : ℝ)=(2500166856680189/2500000000000000 : ℝ) by norm_num, show 1+2*(3383918251277779/25000000000000000000 : ℝ)=(12503383918251277779/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36859528354320539/100000000000000000000 : ℝ)+(3383918251277779/25000000000000000000 : ℝ) ≤ ((486707690724187381/486875000000000000 : ℝ)+(71865700667/38950000000000 : ℝ)*((14237/100000 : ℝ)+(11121/100000 : ℝ)))^(4153/1024 : ℝ) := by
    rw [show (486707690724187381/486875000000000000 : ℝ)+(71865700667/38950000000000 : ℝ)*((14237/100000 : ℝ)+(11121/100000 : ℝ))=(2500310588081523/2500000000000000 : ℝ) by norm_num, show 1+(36859528354320539/100000000000000000000 : ℝ)+(3383918251277779/25000000000000000000 : ℝ)=(20010079040271886331/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36859528354320539/100000000000000000000 : ℝ) ≤ ((486707690724187381/486875000000000000 : ℝ)+2*(71865700667/38950000000000 : ℝ)*(14237/100000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (486707690724187381/486875000000000000 : ℝ)+2*(71865700667/38950000000000 : ℝ)*(14237/100000 : ℝ)=(2500454319482857/2500000000000000 : ℝ) by norm_num, show 1+2*(36859528354320539/100000000000000000000 : ℝ)=(50036859528354320539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (486707690724187381/486875000000000000 : ℝ)*(X 1 0+X 2 0)+(71865700667/38950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (486707690724187381/486875000000000000 : ℝ)) (alpha := (71865700667/38950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (486707690724187381/486875000000000000 : ℝ)*(X 0 1+X 2 1)+(71865700667/38950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (486707690724187381/486875000000000000 : ℝ)) (alpha := (71865700667/38950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (486707690724187381/486875000000000000 : ℝ)*(X 0 2+X 1 2)+(71865700667/38950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (486707690724187381/486875000000000000 : ℝ)) (alpha := (71865700667/38950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2180162893/10000000000 : ℝ)*X 0 0+(539566013/1000000000 : ℝ)*X 0 1+(263163697/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345386003/10000000000 : ℝ)*X 1 0+(-1123674739/5000000000 : ℝ)*X 1 1+(1052654873/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336346591/2500000000 : ℝ)*X 2 0+(5263274029/10000000000 : ℝ)*X 2 1+(-2247349441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092131557/2500000000 : ℝ)*X 0 0+(529940731/1250000000 : ℝ)*X 0 1+(281341159/625000000 : ℝ)*X 0 2+(1092131557/2500000000 : ℝ)*X 1 0+(529940731/1250000000 : ℝ)*X 1 1+(281341159/625000000 : ℝ)*X 1 2+(1092131557/2500000000 : ℝ)*X 2 0+(529940731/1250000000 : ℝ)*X 2 1+(281341159/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-545042077/2500000000 : ℝ)*X 0 0+(1315904259/2500000000 : ℝ)*X 0 1+(5395315779/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327979131/2500000000 : ℝ)*X 1 0+(-1057653961/5000000000 : ℝ)*X 1 1+(2697657881/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311916509/10000000000 : ℝ)*X 2 0+(1348828943/2500000000 : ℝ)*X 2 1+(-2115307929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218426839/500000000 : ℝ)*X 0 0+(70324689/156250000 : ℝ)*X 0 1+(848041409/2000000000 : ℝ)*X 0 2+(218426839/500000000 : ℝ)*X 1 0+(70324689/156250000 : ℝ)*X 1 1+(848041409/2000000000 : ℝ)*X 1 2+(218426839/500000000 : ℝ)*X 2 0+(70324689/156250000 : ℝ)*X 2 1+(848041409/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28967806093739211662946837/3042968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (2045837523/100000000000000 : ℝ)*(base19) + (2308463637/100000000000000 : ℝ)*(base23) + (26461711/20000000000000 : ℝ)*(lower2) + (31852049/12500000000000 : ℝ)*(upper3) + (222489311/100000000000000 : ℝ)*(upper5) + (1421456279045031/25000000000000 : ℝ)*(major0) + (1421456279045031/25000000000000 : ℝ)*(major1) + (1421456279045031/25000000000000 : ℝ)*(major2) + (7553728640841251/100000000000000 : ℝ)*(sp0) + (7553805000266557/100000000000000 : ℝ)*(sp1) + (1888451184410111/25000000000000 : ℝ)*(sp2) + (1908903187263079/50000000000000 : ℝ)*(sp3) + (78405262829/100000000000000 : ℝ)*(sp4) + (18247205213/50000000000000 : ℝ)*(sp7) + (3817842868936583/100000000000000 : ℝ)*(f.failure) + (94422588076301/1250000000000 : ℝ)*(f.sum) + (27426044558539/3895000000000000000000000000 : ℝ)*base66 + (163206652525677439/12171875000000000000000000000000 : ℝ)*base68 + (8064381403055383/1521484375000000000000000000000 : ℝ)*base70 + (10838793550018407/6085937500000000000000000000000 : ℝ)*base72 + (7271837029507/1947500000000000000000000000 : ℝ)*base74 + (175969232285237157/6085937500000000000000000000000 : ℝ)*base76 + (165740296055583689/12171875000000000000000000000000 : ℝ)*base78 + (177609040684396189/12171875000000000000000000000000 : ℝ)*base80 + (243012894097/1947500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (9398737/1250000000000000000000 : ℝ)*base90 + (9398737/1250000000000000000000 : ℝ)*base92 + (9398737/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15214773823623032464837359/6085937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (29533947/6250000000000 : ℝ)*(base19) + (491189913/100000000000000 : ℝ)*(base23) + (4217719/10000000000000 : ℝ)*(upper3) + (1950769/10000000000000 : ℝ)*(lower4) + (5059799/12500000000000 : ℝ)*(upper5) + (5715390652290099/100000000000000 : ℝ)*(major0) + (5715390652290099/100000000000000 : ℝ)*(major1) + (5715390652290099/100000000000000 : ℝ)*(major2) + (12307183089/100000000000000 : ℝ)*(sp1) + (6420470499/50000000000000 : ℝ)*(sp2) + (7593086076009979/100000000000000 : ℝ)*(sp4) + (3796536648141869/50000000000000 : ℝ)*(sp5) + (1898268185969767/25000000000000 : ℝ)*(sp6) + (239855946577329/6250000000000 : ℝ)*(sp7) + (239855946577329/6250000000000 : ℝ)*(f.failure) + (7593086076009979/100000000000000 : ℝ)*(f.sum) + (2477641800403/1947500000000000000000000000 : ℝ)*base65 + (687233582206703219/48687500000000000000000000000000 : ℝ)*base67 + (65084885531234281/48687500000000000000000000000000 : ℝ)*base70 + (316816145814890719/48687500000000000000000000000000 : ℝ)*base71 + (1671097950187/486875000000000000000000000 : ℝ)*base73 + (310260041793765719/48687500000000000000000000000000 : ℝ)*base75 + (40617075127703219/48687500000000000000000000000000 : ℝ)*base77 + (279943208948828219/48687500000000000000000000000000 : ℝ)*base79 + (188221516469/60859375000000000000000000 : ℝ)*base81 + (304419/78125000000000000000 : ℝ)*base89 + (304419/78125000000000000000 : ℝ)*base91 + (304419/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1114_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1114_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1114_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16587/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1114_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1114_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1114_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16587/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1114_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
