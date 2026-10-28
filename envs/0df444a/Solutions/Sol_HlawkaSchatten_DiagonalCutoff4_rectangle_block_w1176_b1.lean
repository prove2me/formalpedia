-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1176_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:47:41.860083+00:00
-- url     : https://prove2.me/submissions/2b503c80-f33f-4159-aedc-829fea995d60

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
theorem support_rectangle_w1176_s3_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147288469/10000000000 : ℝ)*x 0 + (1085152983/2000000000 : ℝ)*x 1 + (5235179017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147288469/10000000000 : ℝ)^8369 ≤ (1592331029/12207031250 : ℝ)^6321 := by
    have hnat : (2147288469 : ℕ)^8369*12207031250^6321 ≤ 1592331029^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147288469 10000000000 1592331029 12207031250 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085152983/2000000000 : ℝ)^8369 ≤ (44506812930787/100000000000000 : ℝ)^6321 := by
    have hnat : (1085152983 : ℕ)^8369*100000000000000^6321 ≤ 44506812930787^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085152983 2000000000 44506812930787 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235179017/10000000000 : ℝ)^8369 ≤ (2122440563409/5000000000000 : ℝ)^6321 := by
    have hnat : (5235179017 : ℕ)^8369*5000000000000^6321 ≤ 2122440563409^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235179017 10000000000 2122440563409 5000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147288469/10000000000 : ℝ), (1085152983/2000000000 : ℝ), (5235179017/10000000000 : ℝ)] ![(1592331029/12207031250 : ℝ), (44506812930787/100000000000000 : ℝ), (2122440563409/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147288469/10000000000 : ℝ)|^8369 ≤ (1592331029/12207031250 : ℝ)^6321
        have hw : |(-2147288469/10000000000 : ℝ)|=(2147288469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085152983/2000000000 : ℝ)|^8369 ≤ (44506812930787/100000000000000 : ℝ)^6321
        have hw : |(1085152983/2000000000 : ℝ)|=(1085152983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235179017/10000000000 : ℝ)|^8369 ≤ (2122440563409/5000000000000 : ℝ)^6321
        have hw : |(5235179017/10000000000 : ℝ)|=(5235179017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s3_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338246807/2500000000 : ℝ)*x 0 + (-2244638961/10000000000 : ℝ)*x 1 + (261758941/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338246807/2500000000 : ℝ)^8369 ≤ (2732382954457/6250000000000 : ℝ)^6321 := by
    have hnat : (1338246807 : ℕ)^8369*6250000000000^6321 ≤ 2732382954457^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338246807 2500000000 2732382954457 6250000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244638961/10000000000 : ℝ)^8369 ≤ (6916531779977/50000000000000 : ℝ)^6321 := by
    have hnat : (2244638961 : ℕ)^8369*50000000000000^6321 ≤ 6916531779977^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244638961 10000000000 6916531779977 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261758941/500000000 : ℝ)^8369 ≤ (42448809153289/100000000000000 : ℝ)^6321 := by
    have hnat : (261758941 : ℕ)^8369*100000000000000^6321 ≤ 42448809153289^6321*500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261758941 500000000 42448809153289 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338246807/2500000000 : ℝ), (-2244638961/10000000000 : ℝ), (261758941/500000000 : ℝ)] ![(2732382954457/6250000000000 : ℝ), (6916531779977/50000000000000 : ℝ), (42448809153289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338246807/2500000000 : ℝ)|^8369 ≤ (2732382954457/6250000000000 : ℝ)^6321
        have hw : |(1338246807/2500000000 : ℝ)|=(1338246807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2244638961/10000000000 : ℝ)|^8369 ≤ (6916531779977/50000000000000 : ℝ)^6321
        have hw : |(-2244638961/10000000000 : ℝ)|=(2244638961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261758941/500000000 : ℝ)|^8369 ≤ (42448809153289/100000000000000 : ℝ)^6321
        have hw : |(261758941/500000000 : ℝ)|=(261758941/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s3_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070597463/2000000000 : ℝ)*x 0 + (5235178801/10000000000 : ℝ)*x 1 + (-2244638871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070597463/2000000000 : ℝ)^8369 ≤ (21859064106029/50000000000000 : ℝ)^6321 := by
    have hnat : (1070597463 : ℕ)^8369*50000000000000^6321 ≤ 21859064106029^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070597463 2000000000 21859064106029 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235178801/10000000000 : ℝ)^8369 ≤ (8489761789863/20000000000000 : ℝ)^6321 := by
    have hnat : (5235178801 : ℕ)^8369*20000000000000^6321 ≤ 8489761789863^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235178801 10000000000 8489761789863 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244638871/10000000000 : ℝ)^8369 ≤ (2766612565121/20000000000000 : ℝ)^6321 := by
    have hnat : (2244638871 : ℕ)^8369*20000000000000^6321 ≤ 2766612565121^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244638871 10000000000 2766612565121 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070597463/2000000000 : ℝ), (5235178801/10000000000 : ℝ), (-2244638871/10000000000 : ℝ)] ![(21859064106029/50000000000000 : ℝ), (8489761789863/20000000000000 : ℝ), (2766612565121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070597463/2000000000 : ℝ)|^8369 ≤ (21859064106029/50000000000000 : ℝ)^6321
        have hw : |(1070597463/2000000000 : ℝ)|=(1070597463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235178801/10000000000 : ℝ)|^8369 ≤ (8489761789863/20000000000000 : ℝ)^6321
        have hw : |(5235178801/10000000000 : ℝ)|=(5235178801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2244638871/10000000000 : ℝ)|^8369 ≤ (2766612565121/20000000000000 : ℝ)^6321
        have hw : |(-2244638871/10000000000 : ℝ)|=(2244638871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s3_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357855607/10000000000 : ℝ)*x 0 + (4171127917/10000000000 : ℝ)*x 1 + (182112959/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357855607/10000000000 : ℝ)^8369 ≤ (8324103512517/25000000000000 : ℝ)^6321 := by
    have hnat : (4357855607 : ℕ)^8369*25000000000000^6321 ≤ 8324103512517^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357855607 10000000000 8324103512517 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171127917/10000000000 : ℝ)^8369 ≤ (3142070214319/10000000000000 : ℝ)^6321 := by
    have hnat : (4171127917 : ℕ)^8369*10000000000000^6321 ≤ 3142070214319^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171127917 10000000000 3142070214319 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182112959/400000000 : ℝ)^8369 ≤ (35282883794831/100000000000000 : ℝ)^6321 := by
    have hnat : (182112959 : ℕ)^8369*100000000000000^6321 ≤ 35282883794831^6321*400000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182112959 400000000 35282883794831 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357855607/10000000000 : ℝ), (4171127917/10000000000 : ℝ), (182112959/400000000 : ℝ)] ![(8324103512517/25000000000000 : ℝ), (3142070214319/10000000000000 : ℝ), (35282883794831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357855607/10000000000 : ℝ)|^8369 ≤ (8324103512517/25000000000000 : ℝ)^6321
        have hw : |(4357855607/10000000000 : ℝ)|=(4357855607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171127917/10000000000 : ℝ)|^8369 ≤ (3142070214319/10000000000000 : ℝ)^6321
        have hw : |(4171127917/10000000000 : ℝ)|=(4171127917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182112959/400000000 : ℝ)|^8369 ≤ (35282883794831/100000000000000 : ℝ)^6321
        have hw : |(182112959/400000000 : ℝ)|=(182112959/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s3_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147304903/10000000000 : ℝ)*x 0 + (5235901361/10000000000 : ℝ)*x 1 + (5425038689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147304903/10000000000 : ℝ)^8369 ≤ (13044507969191/100000000000000 : ℝ)^6321 := by
    have hnat : (2147304903 : ℕ)^8369*100000000000000^6321 ≤ 13044507969191^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147304903 10000000000 13044507969191 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235901361/10000000000 : ℝ)^8369 ≤ (165845961549/390625000000 : ℝ)^6321 := by
    have hnat : (5235901361 : ℕ)^8369*390625000000^6321 ≤ 165845961549^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235901361 10000000000 165845961549 390625000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425038689/10000000000 : ℝ)^8369 ≤ (355991406889/800000000000 : ℝ)^6321 := by
    have hnat : (5425038689 : ℕ)^8369*800000000000^6321 ≤ 355991406889^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425038689 10000000000 355991406889 800000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147304903/10000000000 : ℝ), (5235901361/10000000000 : ℝ), (5425038689/10000000000 : ℝ)] ![(13044507969191/100000000000000 : ℝ), (165845961549/390625000000 : ℝ), (355991406889/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147304903/10000000000 : ℝ)|^8369 ≤ (13044507969191/100000000000000 : ℝ)^6321
        have hw : |(-2147304903/10000000000 : ℝ)|=(2147304903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235901361/10000000000 : ℝ)|^8369 ≤ (165845961549/390625000000 : ℝ)^6321
        have hw : |(5235901361/10000000000 : ℝ)|=(5235901361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425038689/10000000000 : ℝ)|^8369 ≤ (355991406889/800000000000 : ℝ)^6321
        have hw : |(5425038689/10000000000 : ℝ)|=(5425038689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s3_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (20721033/39062500 : ℝ)*x 0 + (-51369493/250000000 : ℝ)*x 1 + (2712519277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20721033/39062500 : ℝ)^8369 ≤ (21597753959251/50000000000000 : ℝ)^6321 := by
    have hnat : (20721033 : ℕ)^8369*50000000000000^6321 ≤ 21597753959251^6321*39062500^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20721033 39062500 21597753959251 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51369493/250000000 : ℝ)^8369 ≤ (6152783839687/50000000000000 : ℝ)^6321 := by
    have hnat : (51369493 : ℕ)^8369*50000000000000^6321 ≤ 6152783839687^6321*250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51369493 250000000 6152783839687 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712519277/5000000000 : ℝ)^8369 ≤ (44498924395009/100000000000000 : ℝ)^6321 := by
    have hnat : (2712519277 : ℕ)^8369*100000000000000^6321 ≤ 44498924395009^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712519277 5000000000 44498924395009 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20721033/39062500 : ℝ), (-51369493/250000000 : ℝ), (2712519277/5000000000 : ℝ)] ![(21597753959251/50000000000000 : ℝ), (6152783839687/50000000000000 : ℝ), (44498924395009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20721033/39062500 : ℝ)|^8369 ≤ (21597753959251/50000000000000 : ℝ)^6321
        have hw : |(20721033/39062500 : ℝ)|=(20721033/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51369493/250000000 : ℝ)|^8369 ≤ (6152783839687/50000000000000 : ℝ)^6321
        have hw : |(-51369493/250000000 : ℝ)|=(51369493/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712519277/5000000000 : ℝ)|^8369 ≤ (44498924395009/100000000000000 : ℝ)^6321
        have hw : |(2712519277/5000000000 : ℝ)|=(2712519277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s3_6 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663073201/1250000000 : ℝ)*x 0 + (1356259371/2500000000 : ℝ)*x 1 + (-256847451/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663073201/1250000000 : ℝ)^8369 ≤ (43195520424921/100000000000000 : ℝ)^6321 := by
    have hnat : (663073201 : ℕ)^8369*100000000000000^6321 ≤ 43195520424921^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663073201 1250000000 43195520424921 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356259371/2500000000 : ℝ)^8369 ≤ (8899782554937/20000000000000 : ℝ)^6321 := by
    have hnat : (1356259371 : ℕ)^8369*20000000000000^6321 ≤ 8899782554937^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356259371 2500000000 8899782554937 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256847451/1250000000 : ℝ)^8369 ≤ (2461113358263/20000000000000 : ℝ)^6321 := by
    have hnat : (256847451 : ℕ)^8369*20000000000000^6321 ≤ 2461113358263^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256847451 1250000000 2461113358263 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663073201/1250000000 : ℝ), (1356259371/2500000000 : ℝ), (-256847451/1250000000 : ℝ)] ![(43195520424921/100000000000000 : ℝ), (8899782554937/20000000000000 : ℝ), (2461113358263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663073201/1250000000 : ℝ)|^8369 ≤ (43195520424921/100000000000000 : ℝ)^6321
        have hw : |(663073201/1250000000 : ℝ)|=(663073201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356259371/2500000000 : ℝ)|^8369 ≤ (8899782554937/20000000000000 : ℝ)^6321
        have hw : |(1356259371/2500000000 : ℝ)|=(1356259371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256847451/1250000000 : ℝ)|^8369 ≤ (2461113358263/20000000000000 : ℝ)^6321
        have hw : |(-256847451/1250000000 : ℝ)|=(256847451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s3_7 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871577649/2000000000 : ℝ)*x 0 + (4551377637/10000000000 : ℝ)*x 1 + (1043145653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871577649/2000000000 : ℝ)^8369 ≤ (33296744219201/100000000000000 : ℝ)^6321 := by
    have hnat : (871577649 : ℕ)^8369*100000000000000^6321 ≤ 33296744219201^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871577649 2000000000 33296744219201 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4551377637/10000000000 : ℝ)^8369 ≤ (7053608864651/20000000000000 : ℝ)^6321 := by
    have hnat : (4551377637 : ℕ)^8369*20000000000000^6321 ≤ 7053608864651^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551377637 10000000000 7053608864651 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043145653/2500000000 : ℝ)^8369 ≤ (15717605724509/50000000000000 : ℝ)^6321 := by
    have hnat : (1043145653 : ℕ)^8369*50000000000000^6321 ≤ 15717605724509^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043145653 2500000000 15717605724509 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871577649/2000000000 : ℝ), (4551377637/10000000000 : ℝ), (1043145653/2500000000 : ℝ)] ![(33296744219201/100000000000000 : ℝ), (7053608864651/20000000000000 : ℝ), (15717605724509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871577649/2000000000 : ℝ)|^8369 ≤ (33296744219201/100000000000000 : ℝ)^6321
        have hw : |(871577649/2000000000 : ℝ)|=(871577649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4551377637/10000000000 : ℝ)|^8369 ≤ (7053608864651/20000000000000 : ℝ)^6321
        have hw : |(4551377637/10000000000 : ℝ)|=(4551377637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043145653/2500000000 : ℝ)|^8369 ≤ (15717605724509/50000000000000 : ℝ)^6321
        have hw : |(1043145653/2500000000 : ℝ)|=(1043145653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16403/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10733/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16403/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16403/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16403/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16403/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16403/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16403/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9221/100000 : ℝ) ^ (523/128 : ℝ) ≤ (1472609873625897/25000000000000000000 : ℝ) := by
    have hpowers : (9221/100000 : ℝ)^523 ≤ (1472609873625897/25000000000000000000 : ℝ)^128 := by
      have hnat : (9221 : ℕ)^523*25000000000000000000^128 ≤ 1472609873625897^128*100000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9221 100000 1472609873625897 25000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9221/100000 : ℝ)) (X := (1472609873625897/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (16403/100000 : ℝ) ^ (523/128 : ℝ) ≤ (61976294888707563/100000000000000000000 : ℝ) := by
    have hpowers : (16403/100000 : ℝ)^523 ≤ (61976294888707563/100000000000000000000 : ℝ)^128 := by
      have hnat : (16403 : ℕ)^523*100000000000000000000^128 ≤ 61976294888707563^128*100000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16403 100000 61976294888707563 100000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16403/100000 : ℝ)) (X := (61976294888707563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501472609873625897/12500000000000000000 : ℝ) ≤ (10000288314613651/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (12501472609873625897/12500000000000000000 : ℝ)^128 ≤ (10000288314613651/10000000000000000 : ℝ)^523 := by
      have hnat : (12501472609873625897 : ℕ)^128*10000000000000000^523 ≤ 10000288314613651^523*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501472609873625897 12500000000000000000 10000288314613651 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000288314613651/10000000000000000 : ℝ)) (X := (12501472609873625897/12500000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100067866734383211151/100000000000000000000 : ℝ) ≤ (2000332111531777/2000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (100067866734383211151/100000000000000000000 : ℝ)^128 ≤ (2000332111531777/2000000000000000 : ℝ)^523 := by
      have hnat : (100067866734383211151 : ℕ)^128*2000000000000000^523 ≤ 2000332111531777^523*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100067866734383211151 100000000000000000000 2000332111531777 2000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000332111531777/2000000000000000 : ℝ)) (X := (100067866734383211151/100000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50061976294888707563/50000000000000000000 : ℝ) ≤ (10003032800704119/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (50061976294888707563/50000000000000000000 : ℝ)^128 ≤ (10003032800704119/10000000000000000 : ℝ)^523 := by
      have hnat : (50061976294888707563 : ℕ)^128*10000000000000000^523 ≤ 10003032800704119^523*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50061976294888707563 50000000000000000000 10003032800704119 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003032800704119/10000000000000000 : ℝ)) (X := (50061976294888707563/50000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1472609873625897/25000000000000000000 : ℝ) ≤ ((35898381884657518027/35910000000000000000 : ℝ)+2*(686121522617/359100000000000 : ℝ)*(9221/100000 : ℝ))^(523/128 : ℝ) := by
    rw [show (35898381884657518027/35910000000000000000 : ℝ)+2*(686121522617/359100000000000 : ℝ)*(9221/100000 : ℝ)=(10000288314613651/10000000000000000 : ℝ) by norm_num, show 1+2*(1472609873625897/25000000000000000000 : ℝ)=(12501472609873625897/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(61976294888707563/100000000000000000000 : ℝ)+(1472609873625897/25000000000000000000 : ℝ) ≤ ((35898381884657518027/35910000000000000000 : ℝ)+(686121522617/359100000000000 : ℝ)*((16403/100000 : ℝ)+(9221/100000 : ℝ)))^(523/128 : ℝ) := by
    rw [show (35898381884657518027/35910000000000000000 : ℝ)+(686121522617/359100000000000 : ℝ)*((16403/100000 : ℝ)+(9221/100000 : ℝ))=(2000332111531777/2000000000000000 : ℝ) by norm_num, show 1+(61976294888707563/100000000000000000000 : ℝ)+(1472609873625897/25000000000000000000 : ℝ)=(100067866734383211151/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(61976294888707563/100000000000000000000 : ℝ) ≤ ((35898381884657518027/35910000000000000000 : ℝ)+2*(686121522617/359100000000000 : ℝ)*(16403/100000 : ℝ))^(523/128 : ℝ) := by
    rw [show (35898381884657518027/35910000000000000000 : ℝ)+2*(686121522617/359100000000000 : ℝ)*(16403/100000 : ℝ)=(10003032800704119/10000000000000000 : ℝ) by norm_num, show 1+2*(61976294888707563/100000000000000000000 : ℝ)=(50061976294888707563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35898381884657518027/35910000000000000000 : ℝ)*(X 1 0+X 2 0)+(686121522617/359100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (9221/100000 : ℝ)) (hi := (16403/100000 : ℝ)) (c := (35898381884657518027/35910000000000000000 : ℝ)) (alpha := (686121522617/359100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35898381884657518027/35910000000000000000 : ℝ)*(X 0 1+X 2 1)+(686121522617/359100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (9221/100000 : ℝ)) (hi := (16403/100000 : ℝ)) (c := (35898381884657518027/35910000000000000000 : ℝ)) (alpha := (686121522617/359100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35898381884657518027/35910000000000000000 : ℝ)*(X 0 2+X 1 2)+(686121522617/359100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (9221/100000 : ℝ)) (hi := (16403/100000 : ℝ)) (c := (35898381884657518027/35910000000000000000 : ℝ)) (alpha := (686121522617/359100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2147288469/10000000000 : ℝ)*X 0 0+(1085152983/2000000000 : ℝ)*X 0 1+(5235179017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338246807/2500000000 : ℝ)*X 1 0+(-2244638961/10000000000 : ℝ)*X 1 1+(261758941/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070597463/2000000000 : ℝ)*X 2 0+(5235178801/10000000000 : ℝ)*X 2 1+(-2244638871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357855607/10000000000 : ℝ)*X 0 0+(4171127917/10000000000 : ℝ)*X 0 1+(182112959/400000000 : ℝ)*X 0 2+(4357855607/10000000000 : ℝ)*X 1 0+(4171127917/10000000000 : ℝ)*X 1 1+(182112959/400000000 : ℝ)*X 1 2+(4357855607/10000000000 : ℝ)*X 2 0+(4171127917/10000000000 : ℝ)*X 2 1+(182112959/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2147304903/10000000000 : ℝ)*X 0 0+(5235901361/10000000000 : ℝ)*X 0 1+(5425038689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((20721033/39062500 : ℝ)*X 1 0+(-51369493/250000000 : ℝ)*X 1 1+(2712519277/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663073201/1250000000 : ℝ)*X 2 0+(1356259371/2500000000 : ℝ)*X 2 1+(-256847451/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871577649/2000000000 : ℝ)*X 0 0+(4551377637/10000000000 : ℝ)*X 0 1+(1043145653/2500000000 : ℝ)*X 0 2+(871577649/2000000000 : ℝ)*X 1 0+(4551377637/10000000000 : ℝ)*X 1 1+(1043145653/2500000000 : ℝ)*X 1 2+(871577649/2000000000 : ℝ)*X 2 0+(4551377637/10000000000 : ℝ)*X 2 1+(1043145653/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52438379389612945809743999/5343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1115500611/50000000000000 : ℝ)*(base19) + (2146586183/100000000000000 : ℝ)*(base23) + (709661/781250000000 : ℝ)*(lower2) + (225671487/100000000000000 : ℝ)*(upper3) + (209474399/100000000000000 : ℝ)*(upper5) + (245843040588509/6250000000000 : ℝ)*(major0) + (245843040588509/6250000000000 : ℝ)*(major1) + (245843040588509/6250000000000 : ℝ)*(major2) + (1311753627314811/25000000000000 : ℝ)*(sp0) + (5247050938061073/100000000000000 : ℝ)*(sp1) + (5247051022476111/100000000000000 : ℝ)*(sp2) + (1309952017942267/50000000000000 : ℝ)*(sp3) + (38659803051/100000000000000 : ℝ)*(sp4) + (395335689/2000000000000 : ℝ)*(sp7) + (327490475333623/12500000000000 : ℝ)*(f.failure) + (1049410633812459/20000000000000 : ℝ)*(f.sum) + (6357252680329/2565000000000000000000000000 : ℝ)*base65 + (58571928270654139/3562500000000000000000000000000 : ℝ)*base68 + (4794072775220861/3562500000000000000000000000000 : ℝ)*base69 + (17246183825716639/3562500000000000000000000000000 : ℝ)*base72 + (7573927362611/2565000000000000000000000000 : ℝ)*base74 + (9593976141091639/3562500000000000000000000000000 : ℝ)*base76 + (56780584280720861/3562500000000000000000000000000 : ℝ)*base77 + (27858355500654139/3562500000000000000000000000000 : ℝ)*base80 + (2436343739779/2565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5168583/1250000000000000000000 : ℝ)*base89 + (5168583/1250000000000000000000 : ℝ)*base91 + (5168583/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (900416716013787525960320369/99750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1102634869/100000000000000 : ℝ)*(base19) + (296377509/12500000000000 : ℝ)*(base23) + (104399/78125000000 : ℝ)*(upper3) + (3178481/25000000000000 : ℝ)*(lower4) + (46514243/50000000000000 : ℝ)*(upper5) + (1981781393945347/50000000000000 : ℝ)*(major0) + (1981781393945347/50000000000000 : ℝ)*(major1) + (1981781393945347/50000000000000 : ℝ)*(major2) + (61608739/390625000000 : ℝ)*(sp1) + (12720656931/50000000000000 : ℝ)*(sp2) + (1057434082236373/20000000000000 : ℝ)*(sp4) + (1321788384177453/25000000000000 : ℝ)*(sp5) + (5287142598847931/100000000000000 : ℝ)*(sp6) + (2639954863708383/100000000000000 : ℝ)*(sp7) + (2639954863708383/100000000000000 : ℝ)*(f.failure) + (1057434082236373/20000000000000 : ℝ)*(f.sum) + (47632240587751/8977500000000000000000000000 : ℝ)*base66 + (768654217735869959/199500000000000000000000000000000 : ℝ)*base68 + (1663922865663369959/199500000000000000000000000000000 : ℝ)*base70 + (2648682033972369959/199500000000000000000000000000000 : ℝ)*base72 + (17225206136987/17955000000000000000000000000 : ℝ)*base74 + (1012587234391869959/199500000000000000000000000000000 : ℝ)*base76 + (2351656030047369959/199500000000000000000000000000000 : ℝ)*base78 + (1616263244535369959/199500000000000000000000000000000 : ℝ)*base80 + (5695275100279/2244375000000000000000000000 : ℝ)*base82 + (90538543/10000000000000000000000 : ℝ)*base89 + (90538543/10000000000000000000000 : ℝ)*base91 + (90538543/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1176_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16403/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10733/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1176_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1176_s4_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150026821/10000000000 : ℝ)*x 0 + (2700157447/5000000000 : ℝ)*x 1 + (1314709179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150026821/10000000000 : ℝ)^8369 ≤ (6533202518159/50000000000000 : ℝ)^6321 := by
    have hnat : (2150026821 : ℕ)^8369*50000000000000^6321 ≤ 6533202518159^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150026821 10000000000 6533202518159 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700157447/5000000000 : ℝ)^8369 ≤ (44230621015499/100000000000000 : ℝ)^6321 := by
    have hnat : (2700157447 : ℕ)^8369*100000000000000^6321 ≤ 44230621015499^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700157447 5000000000 44230621015499 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314709179/2500000000 : ℝ)^8369 ≤ (42702973942701/100000000000000 : ℝ)^6321 := by
    have hnat : (1314709179 : ℕ)^8369*100000000000000^6321 ≤ 42702973942701^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314709179 2500000000 42702973942701 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150026821/10000000000 : ℝ), (2700157447/5000000000 : ℝ), (1314709179/2500000000 : ℝ)] ![(6533202518159/50000000000000 : ℝ), (44230621015499/100000000000000 : ℝ), (42702973942701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150026821/10000000000 : ℝ)|^8369 ≤ (6533202518159/50000000000000 : ℝ)^6321
        have hw : |(-2150026821/10000000000 : ℝ)|=(2150026821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700157447/5000000000 : ℝ)|^8369 ≤ (44230621015499/100000000000000 : ℝ)^6321
        have hw : |(2700157447/5000000000 : ℝ)|=(2700157447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314709179/2500000000 : ℝ)|^8369 ≤ (42702973942701/100000000000000 : ℝ)^6321
        have hw : |(1314709179/2500000000 : ℝ)|=(1314709179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s4_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346610663/10000000000 : ℝ)*x 0 + (-2221899993/10000000000 : ℝ)*x 1 + (262941857/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346610663/10000000000 : ℝ)^8369 ≤ (43649189685217/100000000000000 : ℝ)^6321 := by
    have hnat : (5346610663 : ℕ)^8369*100000000000000^6321 ≤ 43649189685217^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346610663 10000000000 43649189685217 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2221899993/10000000000 : ℝ)^8369 ≤ (852989487441/6250000000000 : ℝ)^6321 := by
    have hnat : (2221899993 : ℕ)^8369*6250000000000^6321 ≤ 852989487441^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221899993 10000000000 852989487441 6250000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262941857/500000000 : ℝ)^8369 ≤ (21351489250601/50000000000000 : ℝ)^6321 := by
    have hnat : (262941857 : ℕ)^8369*50000000000000^6321 ≤ 21351489250601^6321*500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262941857 500000000 21351489250601 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346610663/10000000000 : ℝ), (-2221899993/10000000000 : ℝ), (262941857/500000000 : ℝ)] ![(43649189685217/100000000000000 : ℝ), (852989487441/6250000000000 : ℝ), (21351489250601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346610663/10000000000 : ℝ)|^8369 ≤ (43649189685217/100000000000000 : ℝ)^6321
        have hw : |(5346610663/10000000000 : ℝ)|=(5346610663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2221899993/10000000000 : ℝ)|^8369 ≤ (852989487441/6250000000000 : ℝ)^6321
        have hw : |(-2221899993/10000000000 : ℝ)|=(2221899993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262941857/500000000 : ℝ)|^8369 ≤ (21351489250601/50000000000000 : ℝ)^6321
        have hw : |(262941857/500000000 : ℝ)|=(262941857/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s4_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673305309/5000000000 : ℝ)*x 0 + (657354703/1250000000 : ℝ)*x 1 + (-2221899413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673305309/5000000000 : ℝ)^8369 ≤ (10912297299703/25000000000000 : ℝ)^6321 := by
    have hnat : (2673305309 : ℕ)^8369*25000000000000^6321 ≤ 10912297299703^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673305309 5000000000 10912297299703 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657354703/1250000000 : ℝ)^8369 ≤ (1708119348191/4000000000000 : ℝ)^6321 := by
    have hnat : (657354703 : ℕ)^8369*4000000000000^6321 ≤ 1708119348191^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657354703 1250000000 1708119348191 4000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2221899413/10000000000 : ℝ)^8369 ≤ (545913083287/4000000000000 : ℝ)^6321 := by
    have hnat : (2221899413 : ℕ)^8369*4000000000000^6321 ≤ 545913083287^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221899413 10000000000 545913083287 4000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673305309/5000000000 : ℝ), (657354703/1250000000 : ℝ), (-2221899413/10000000000 : ℝ)] ![(10912297299703/25000000000000 : ℝ), (1708119348191/4000000000000 : ℝ), (545913083287/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673305309/5000000000 : ℝ)|^8369 ≤ (10912297299703/25000000000000 : ℝ)^6321
        have hw : |(2673305309/5000000000 : ℝ)|=(2673305309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657354703/1250000000 : ℝ)|^8369 ≤ (1708119348191/4000000000000 : ℝ)^6321
        have hw : |(657354703/1250000000 : ℝ)|=(657354703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2221899413/10000000000 : ℝ)|^8369 ≤ (545913083287/4000000000000 : ℝ)^6321
        have hw : |(-2221899413/10000000000 : ℝ)|=(2221899413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s4_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359493641/10000000000 : ℝ)*x 0 + (527511517/1250000000 : ℝ)*x 1 + (4503437/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359493641/10000000000 : ℝ)^8369 ≤ (6662597109539/20000000000000 : ℝ)^6321 := by
    have hnat : (4359493641 : ℕ)^8369*20000000000000^6321 ≤ 6662597109539^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359493641 10000000000 6662597109539 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527511517/1250000000 : ℝ)^8369 ≤ (6381995180711/20000000000000 : ℝ)^6321 := by
    have hnat : (527511517 : ℕ)^8369*20000000000000^6321 ≤ 6381995180711^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527511517 1250000000 6381995180711 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503437/10000000 : ℝ)^8369 ≤ (8694259633869/25000000000000 : ℝ)^6321 := by
    have hnat : (4503437 : ℕ)^8369*25000000000000^6321 ≤ 8694259633869^6321*10000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503437 10000000 8694259633869 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359493641/10000000000 : ℝ), (527511517/1250000000 : ℝ), (4503437/10000000 : ℝ)] ![(6662597109539/20000000000000 : ℝ), (6381995180711/20000000000000 : ℝ), (8694259633869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359493641/10000000000 : ℝ)|^8369 ≤ (6662597109539/20000000000000 : ℝ)^6321
        have hw : |(4359493641/10000000000 : ℝ)|=(4359493641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527511517/1250000000 : ℝ)|^8369 ≤ (6381995180711/20000000000000 : ℝ)^6321
        have hw : |(527511517/1250000000 : ℝ)|=(527511517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503437/10000000 : ℝ)|^8369 ≤ (8694259633869/25000000000000 : ℝ)^6321
        have hw : |(4503437/10000000 : ℝ)|=(4503437/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s4_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150033603/10000000000 : ℝ)*x 0 + (2629617931/5000000000 : ℝ)*x 1 + (5399914123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150033603/10000000000 : ℝ)^8369 ≤ (13066459606829/100000000000000 : ℝ)^6321 := by
    have hnat : (2150033603 : ℕ)^8369*100000000000000^6321 ≤ 13066459606829^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150033603 10000000000 13066459606829 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629617931/5000000000 : ℝ)^8369 ≤ (42707265286743/100000000000000 : ℝ)^6321 := by
    have hnat : (2629617931 : ℕ)^8369*100000000000000^6321 ≤ 42707265286743^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629617931 5000000000 42707265286743 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399914123/10000000000 : ℝ)^8369 ≤ (44226275084797/100000000000000 : ℝ)^6321 := by
    have hnat : (5399914123 : ℕ)^8369*100000000000000^6321 ≤ 44226275084797^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399914123 10000000000 44226275084797 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150033603/10000000000 : ℝ), (2629617931/5000000000 : ℝ), (5399914123/10000000000 : ℝ)] ![(13066459606829/100000000000000 : ℝ), (42707265286743/100000000000000 : ℝ), (44226275084797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150033603/10000000000 : ℝ)|^8369 ≤ (13066459606829/100000000000000 : ℝ)^6321
        have hw : |(-2150033603/10000000000 : ℝ)|=(2150033603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629617931/5000000000 : ℝ)|^8369 ≤ (42707265286743/100000000000000 : ℝ)^6321
        have hw : |(2629617931/5000000000 : ℝ)|=(2629617931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399914123/10000000000 : ℝ)|^8369 ≤ (44226275084797/100000000000000 : ℝ)^6321
        have hw : |(5399914123/10000000000 : ℝ)|=(5399914123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s4_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310679941/10000000000 : ℝ)*x 0 + (-2080822387/10000000000 : ℝ)*x 1 + (2699957123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310679941/10000000000 : ℝ)^8369 ≤ (21630619036179/50000000000000 : ℝ)^6321 := by
    have hnat : (5310679941 : ℕ)^8369*50000000000000^6321 ≤ 21630619036179^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310679941 10000000000 21630619036179 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080822387/10000000000 : ℝ)^8369 ≤ (12512485490469/100000000000000 : ℝ)^6321 := by
    have hnat : (2080822387 : ℕ)^8369*100000000000000^6321 ≤ 12512485490469^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080822387 10000000000 12512485490469 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699957123/5000000000 : ℝ)^8369 ≤ (44226276418583/100000000000000 : ℝ)^6321 := by
    have hnat : (2699957123 : ℕ)^8369*100000000000000^6321 ≤ 44226276418583^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699957123 5000000000 44226276418583 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310679941/10000000000 : ℝ), (-2080822387/10000000000 : ℝ), (2699957123/5000000000 : ℝ)] ![(21630619036179/50000000000000 : ℝ), (12512485490469/100000000000000 : ℝ), (44226276418583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310679941/10000000000 : ℝ)|^8369 ≤ (21630619036179/50000000000000 : ℝ)^6321
        have hw : |(5310679941/10000000000 : ℝ)|=(5310679941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080822387/10000000000 : ℝ)|^8369 ≤ (12512485490469/100000000000000 : ℝ)^6321
        have hw : |(-2080822387/10000000000 : ℝ)|=(2080822387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699957123/5000000000 : ℝ)|^8369 ≤ (44226276418583/100000000000000 : ℝ)^6321
        have hw : |(2699957123/5000000000 : ℝ)|=(2699957123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s4_6 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310680007/10000000000 : ℝ)*x 0 + (5399914073/10000000000 : ℝ)*x 1 + (-2080822533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310680007/10000000000 : ℝ)^8369 ≤ (8652247756839/20000000000000 : ℝ)^6321 := by
    have hnat : (5310680007 : ℕ)^8369*20000000000000^6321 ≤ 8652247756839^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310680007 10000000000 8652247756839 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399914073/10000000000 : ℝ)^8369 ≤ (44226274542607/100000000000000 : ℝ)^6321 := by
    have hnat : (5399914073 : ℕ)^8369*100000000000000^6321 ≤ 44226274542607^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399914073 10000000000 44226274542607 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080822533/10000000000 : ℝ)^8369 ≤ (3128121663213/25000000000000 : ℝ)^6321 := by
    have hnat : (2080822533 : ℕ)^8369*25000000000000^6321 ≤ 3128121663213^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080822533 10000000000 3128121663213 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310680007/10000000000 : ℝ), (5399914073/10000000000 : ℝ), (-2080822533/10000000000 : ℝ)] ![(8652247756839/20000000000000 : ℝ), (44226274542607/100000000000000 : ℝ), (3128121663213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310680007/10000000000 : ℝ)|^8369 ≤ (8652247756839/20000000000000 : ℝ)^6321
        have hw : |(5310680007/10000000000 : ℝ)|=(5310680007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399914073/10000000000 : ℝ)|^8369 ≤ (44226274542607/100000000000000 : ℝ)^6321
        have hw : |(5399914073/10000000000 : ℝ)|=(5399914073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080822533/10000000000 : ℝ)|^8369 ≤ (3128121663213/25000000000000 : ℝ)^6321
        have hw : |(-2080822533/10000000000 : ℝ)|=(2080822533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s4_7 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179753179/5000000000 : ℝ)*x 0 + (4502638081/10000000000 : ℝ)*x 1 + (2110447577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179753179/5000000000 : ℝ)^8369 ≤ (6662622841931/20000000000000 : ℝ)^6321 := by
    have hnat : (2179753179 : ℕ)^8369*20000000000000^6321 ≤ 6662622841931^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179753179 5000000000 6662622841931 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502638081/10000000000 : ℝ)^8369 ≤ (17384435165977/50000000000000 : ℝ)^6321 := by
    have hnat : (4502638081 : ℕ)^8369*50000000000000^6321 ≤ 17384435165977^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502638081 10000000000 17384435165977 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110447577/5000000000 : ℝ)^8369 ≤ (31918015439623/100000000000000 : ℝ)^6321 := by
    have hnat : (2110447577 : ℕ)^8369*100000000000000^6321 ≤ 31918015439623^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110447577 5000000000 31918015439623 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179753179/5000000000 : ℝ), (4502638081/10000000000 : ℝ), (2110447577/5000000000 : ℝ)] ![(6662622841931/20000000000000 : ℝ), (17384435165977/50000000000000 : ℝ), (31918015439623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179753179/5000000000 : ℝ)|^8369 ≤ (6662622841931/20000000000000 : ℝ)^6321
        have hw : |(2179753179/5000000000 : ℝ)|=(2179753179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502638081/10000000000 : ℝ)|^8369 ≤ (17384435165977/50000000000000 : ℝ)^6321
        have hw : |(4502638081/10000000000 : ℝ)|=(4502638081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2110447577/5000000000 : ℝ)|^8369 ≤ (31918015439623/100000000000000 : ℝ)^6321
        have hw : |(2110447577/5000000000 : ℝ)|=(2110447577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5619/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10733/100000 : ℝ) ^ (523/128 : ℝ) ≤ (10954362652919953/100000000000000000000 : ℝ) := by
    have hpowers : (10733/100000 : ℝ)^523 ≤ (10954362652919953/100000000000000000000 : ℝ)^128 := by
      have hnat : (10733 : ℕ)^523*100000000000000000000^128 ≤ 10954362652919953^128*100000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10733 100000 10954362652919953 100000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10733/100000 : ℝ)) (X := (10954362652919953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (523/128 : ℝ) ≤ (20172055702126381/50000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^523 ≤ (20172055702126381/50000000000000000000 : ℝ)^128 := by
      have hnat : (14767 : ℕ)^523*50000000000000000000^128 ≤ 20172055702126381^128*100000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 20172055702126381 50000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (20172055702126381/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010954362652919953/50000000000000000000 : ℝ) ≤ (10000536153892417/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (50010954362652919953/50000000000000000000 : ℝ)^128 ≤ (10000536153892417/10000000000000000 : ℝ)^523 := by
      have hnat : (50010954362652919953 : ℕ)^128*10000000000000000^523 ≤ 10000536153892417^523*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010954362652919953 50000000000000000000 10000536153892417 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000536153892417/10000000000000000 : ℝ)) (X := (50010954362652919953/50000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010259694811434543/20000000000000000000 : ℝ) ≤ (10001255245328733/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (20010259694811434543/20000000000000000000 : ℝ)^128 ≤ (10001255245328733/10000000000000000 : ℝ)^523 := by
      have hnat : (20010259694811434543 : ℕ)^128*10000000000000000^523 ≤ 10001255245328733^523*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010259694811434543 20000000000000000000 10001255245328733 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001255245328733/10000000000000000 : ℝ)) (X := (20010259694811434543/20000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020172055702126381/25000000000000000000 : ℝ) ≤ (10001974336765049/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (25020172055702126381/25000000000000000000 : ℝ)^128 ≤ (10001974336765049/10000000000000000 : ℝ)^523 := by
      have hnat : (25020172055702126381 : ℕ)^128*10000000000000000^523 ≤ 10001974336765049^523*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020172055702126381 25000000000000000000 10001974336765049 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001974336765049/10000000000000000 : ℝ)) (X := (25020172055702126381/25000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10954362652919953/100000000000000000000 : ℝ) ≤ ((20163363414015025461/20170000000000000000 : ℝ)+2*(179772859079/100850000000000 : ℝ)*(10733/100000 : ℝ))^(523/128 : ℝ) := by
    rw [show (20163363414015025461/20170000000000000000 : ℝ)+2*(179772859079/100850000000000 : ℝ)*(10733/100000 : ℝ)=(10000536153892417/10000000000000000 : ℝ) by norm_num, show 1+2*(10954362652919953/100000000000000000000 : ℝ)=(50010954362652919953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20172055702126381/50000000000000000000 : ℝ)+(10954362652919953/100000000000000000000 : ℝ) ≤ ((20163363414015025461/20170000000000000000 : ℝ)+(179772859079/100850000000000 : ℝ)*((14767/100000 : ℝ)+(10733/100000 : ℝ)))^(523/128 : ℝ) := by
    rw [show (20163363414015025461/20170000000000000000 : ℝ)+(179772859079/100850000000000 : ℝ)*((14767/100000 : ℝ)+(10733/100000 : ℝ))=(10001255245328733/10000000000000000 : ℝ) by norm_num, show 1+(20172055702126381/50000000000000000000 : ℝ)+(10954362652919953/100000000000000000000 : ℝ)=(20010259694811434543/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20172055702126381/50000000000000000000 : ℝ) ≤ ((20163363414015025461/20170000000000000000 : ℝ)+2*(179772859079/100850000000000 : ℝ)*(14767/100000 : ℝ))^(523/128 : ℝ) := by
    rw [show (20163363414015025461/20170000000000000000 : ℝ)+2*(179772859079/100850000000000 : ℝ)*(14767/100000 : ℝ)=(10001974336765049/10000000000000000 : ℝ) by norm_num, show 1+2*(20172055702126381/50000000000000000000 : ℝ)=(25020172055702126381/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20163363414015025461/20170000000000000000 : ℝ)*(X 1 0+X 2 0)+(179772859079/100850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (10733/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (20163363414015025461/20170000000000000000 : ℝ)) (alpha := (179772859079/100850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20163363414015025461/20170000000000000000 : ℝ)*(X 0 1+X 2 1)+(179772859079/100850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (10733/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (20163363414015025461/20170000000000000000 : ℝ)) (alpha := (179772859079/100850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20163363414015025461/20170000000000000000 : ℝ)*(X 0 2+X 1 2)+(179772859079/100850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (10733/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (20163363414015025461/20170000000000000000 : ℝ)) (alpha := (179772859079/100850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2150026821/10000000000 : ℝ)*X 0 0+(2700157447/5000000000 : ℝ)*X 0 1+(1314709179/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346610663/10000000000 : ℝ)*X 1 0+(-2221899993/10000000000 : ℝ)*X 1 1+(262941857/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673305309/5000000000 : ℝ)*X 2 0+(657354703/1250000000 : ℝ)*X 2 1+(-2221899413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359493641/10000000000 : ℝ)*X 0 0+(527511517/1250000000 : ℝ)*X 0 1+(4503437/10000000 : ℝ)*X 0 2+(4359493641/10000000000 : ℝ)*X 1 0+(527511517/1250000000 : ℝ)*X 1 1+(4503437/10000000 : ℝ)*X 1 2+(4359493641/10000000000 : ℝ)*X 2 0+(527511517/1250000000 : ℝ)*X 2 1+(4503437/10000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2150033603/10000000000 : ℝ)*X 0 0+(2629617931/5000000000 : ℝ)*X 0 1+(5399914123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310679941/10000000000 : ℝ)*X 1 0+(-2080822387/10000000000 : ℝ)*X 1 1+(2699957123/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310680007/10000000000 : ℝ)*X 2 0+(5399914073/10000000000 : ℝ)*X 2 1+(-2080822533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179753179/5000000000 : ℝ)*X 0 0+(4502638081/10000000000 : ℝ)*X 0 1+(2110447577/5000000000 : ℝ)*X 0 2+(2179753179/5000000000 : ℝ)*X 1 0+(4502638081/10000000000 : ℝ)*X 1 1+(2110447577/5000000000 : ℝ)*X 1 2+(2179753179/5000000000 : ℝ)*X 2 0+(4502638081/10000000000 : ℝ)*X 2 1+(2110447577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79643432477310208695483/10085000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1979381911/100000000000000 : ℝ)*(base19) + (1686538509/100000000000000 : ℝ)*(base23) + (62382163/50000000000000 : ℝ)*(lower2) + (35148531/100000000000000 : ℝ)*(upper3) + (693996851/100000000000000 : ℝ)*(upper5) + (1324711927002571/25000000000000 : ℝ)*(major0) + (1324711927002571/25000000000000 : ℝ)*(major1) + (1324711927002571/25000000000000 : ℝ)*(major2) + (7068280453994663/100000000000000 : ℝ)*(sp0) + (3534181873735559/50000000000000 : ℝ)*(sp1) + (7068364040314519/100000000000000 : ℝ)*(sp2) + (882326062459869/25000000000000 : ℝ)*(sp3) + (17054571673/20000000000000 : ℝ)*(sp4) + (5035217499/20000000000000 : ℝ)*(sp7) + (352932942592697/10000000000000 : ℝ)*(f.failure) + (1767091431713257/25000000000000 : ℝ)*(f.sum) + (20450672621327/2521250000000000000000000000 : ℝ)*base66 + (637633472621510231/504250000000000000000000000000000 : ℝ)*base67 + (5980468478859010231/504250000000000000000000000000000 : ℝ)*base69 + (355659545980739769/504250000000000000000000000000000 : ℝ)*base72 + (5095028263973/10085000000000000000000000000 : ℝ)*base74 + (4115164599038239769/504250000000000000000000000000000 : ℝ)*base76 + (4672862233889739769/504250000000000000000000000000000 : ℝ)*base78 + (2422392812979510231/504250000000000000000000000000000 : ℝ)*base79 + (3583067173183/10085000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (284137/1000000000000000000000 : ℝ)*base89 + (284137/1000000000000000000000 : ℝ)*base91 + (284137/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (390638616153231685426964091/1008500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (850883561/100000000000000 : ℝ)*(base19) + (345071821/25000000000000 : ℝ)*(base23) + (235891959/100000000000000 : ℝ)*(upper2) + (123332501/100000000000000 : ℝ)*(upper5) + (5328877526060759/100000000000000 : ℝ)*(major0) + (5328877526060759/100000000000000 : ℝ)*(major1) + (5328877526060759/100000000000000 : ℝ)*(major2) + (2744052337/100000000000000 : ℝ)*(sp0) + (36686301917/100000000000000 : ℝ)*(sp1) + (7244984297/20000000000000 : ℝ)*(sp2) + (7108421328076621/100000000000000 : ℝ)*(sp4) + (177709663373587/2500000000000 : ℝ)*(sp5) + (7108386466920189/100000000000000 : ℝ)*(sp6) + (1774665483540507/50000000000000 : ℝ)*(sp7) + (1774665483540507/50000000000000 : ℝ)*(f.failure) + (3554212036064479/50000000000000 : ℝ)*(f.sum) + (18353381166099/5042500000000000000000000000 : ℝ)*base66 + (16910280166527815101/2017000000000000000000000000000000 : ℝ)*base68 + (18200648084516815101/2017000000000000000000000000000000 : ℝ)*base70 + (9349714906660815101/2017000000000000000000000000000000 : ℝ)*base72 + (72598873135483/10085000000000000000000000000 : ℝ)*base74 + (2517242280861815101/2017000000000000000000000000000000 : ℝ)*base76 + (13847651938494815101/2017000000000000000000000000000000 : ℝ)*base78 + (19430081672096815101/2017000000000000000000000000000000 : ℝ)*base80 + (2101258093923/630312500000000000000000000 : ℝ)*base82 + (74063147/5000000000000000000000 : ℝ)*base89 + (74063147/5000000000000000000000 : ℝ)*base91 + (74063147/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1176_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1176_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1176_s5_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-215059403/1000000000 : ℝ)*x 0 + (1348508997/2500000000 : ℝ)*x 1 + (5264743067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215059403/1000000000 : ℝ)^8369 ≤ (13070969205023/100000000000000 : ℝ)^6321 := by
    have hnat : (215059403 : ℕ)^8369*100000000000000^6321 ≤ 13070969205023^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215059403 1000000000 13070969205023 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348508997/2500000000 : ℝ)^8369 ≤ (8832509007773/20000000000000 : ℝ)^6321 := by
    have hnat : (1348508997 : ℕ)^8369*20000000000000^6321 ≤ 8832509007773^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348508997 2500000000 8832509007773 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264743067/10000000000 : ℝ)^8369 ≤ (213832428739/500000000000 : ℝ)^6321 := by
    have hnat : (5264743067 : ℕ)^8369*500000000000^6321 ≤ 213832428739^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264743067 10000000000 213832428739 500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215059403/1000000000 : ℝ), (1348508997/2500000000 : ℝ), (5264743067/10000000000 : ℝ)] ![(13070969205023/100000000000000 : ℝ), (8832509007773/20000000000000 : ℝ), (213832428739/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215059403/1000000000 : ℝ)|^8369 ≤ (13070969205023/100000000000000 : ℝ)^6321
        have hw : |(-215059403/1000000000 : ℝ)|=(215059403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348508997/2500000000 : ℝ)|^8369 ≤ (8832509007773/20000000000000 : ℝ)^6321
        have hw : |(1348508997/2500000000 : ℝ)|=(1348508997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264743067/10000000000 : ℝ)|^8369 ≤ (213832428739/500000000000 : ℝ)^6321
        have hw : |(5264743067/10000000000 : ℝ)|=(5264743067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s5_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672515439/5000000000 : ℝ)*x 0 + (-277023517/1250000000 : ℝ)*x 1 + (526474311/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672515439/5000000000 : ℝ)^8369 ≤ (8726422922209/20000000000000 : ℝ)^6321 := by
    have hnat : (2672515439 : ℕ)^8369*20000000000000^6321 ≤ 8726422922209^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672515439 5000000000 8726422922209 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277023517/1250000000 : ℝ)^8369 ≤ (1360139917249/10000000000000 : ℝ)^6321 := by
    have hnat : (277023517 : ℕ)^8369*10000000000000^6321 ≤ 1360139917249^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277023517 1250000000 1360139917249 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526474311/1000000000 : ℝ)^8369 ≤ (42766486210269/100000000000000 : ℝ)^6321 := by
    have hnat : (526474311 : ℕ)^8369*100000000000000^6321 ≤ 42766486210269^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526474311 1000000000 42766486210269 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672515439/5000000000 : ℝ), (-277023517/1250000000 : ℝ), (526474311/1000000000 : ℝ)] ![(8726422922209/20000000000000 : ℝ), (1360139917249/10000000000000 : ℝ), (42766486210269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672515439/5000000000 : ℝ)|^8369 ≤ (8726422922209/20000000000000 : ℝ)^6321
        have hw : |(2672515439/5000000000 : ℝ)|=(2672515439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277023517/1250000000 : ℝ)|^8369 ≤ (1360139917249/10000000000000 : ℝ)^6321
        have hw : |(-277023517/1250000000 : ℝ)|=(277023517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526474311/1000000000 : ℝ)|^8369 ≤ (42766486210269/100000000000000 : ℝ)^6321
        have hw : |(526474311/1000000000 : ℝ)|=(526474311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s5_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336257731/2500000000 : ℝ)*x 0 + (2632371481/5000000000 : ℝ)*x 1 + (-221618827/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336257731/2500000000 : ℝ)^8369 ≤ (43632115108211/100000000000000 : ℝ)^6321 := by
    have hnat : (1336257731 : ℕ)^8369*100000000000000^6321 ≤ 43632115108211^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336257731 2500000000 43632115108211 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632371481/5000000000 : ℝ)^8369 ≤ (8553296923703/20000000000000 : ℝ)^6321 := by
    have hnat : (2632371481 : ℕ)^8369*20000000000000^6321 ≤ 8553296923703^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632371481 5000000000 8553296923703 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221618827/1000000000 : ℝ)^8369 ≤ (13601400261343/100000000000000 : ℝ)^6321 := by
    have hnat : (221618827 : ℕ)^8369*100000000000000^6321 ≤ 13601400261343^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221618827 1000000000 13601400261343 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336257731/2500000000 : ℝ), (2632371481/5000000000 : ℝ), (-221618827/1000000000 : ℝ)] ![(43632115108211/100000000000000 : ℝ), (8553296923703/20000000000000 : ℝ), (13601400261343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336257731/2500000000 : ℝ)|^8369 ≤ (43632115108211/100000000000000 : ℝ)^6321
        have hw : |(1336257731/2500000000 : ℝ)|=(1336257731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632371481/5000000000 : ℝ)|^8369 ≤ (8553296923703/20000000000000 : ℝ)^6321
        have hw : |(2632371481/5000000000 : ℝ)|=(2632371481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221618827/1000000000 : ℝ)|^8369 ≤ (13601400261343/100000000000000 : ℝ)^6321
        have hw : |(-221618827/1000000000 : ℝ)|=(221618827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s5_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359824619/10000000000 : ℝ)*x 0 + (4232250917/10000000000 : ℝ)*x 1 + (1122798269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359824619/10000000000 : ℝ)^8369 ≤ (33316334197669/100000000000000 : ℝ)^6321 := by
    have hnat : (4359824619 : ℕ)^8369*100000000000000^6321 ≤ 33316334197669^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359824619 10000000000 33316334197669 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232250917/10000000000 : ℝ)^8369 ≤ (1281270336133/4000000000000 : ℝ)^6321 := by
    have hnat : (4232250917 : ℕ)^8369*4000000000000^6321 ≤ 1281270336133^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232250917 10000000000 1281270336133 4000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122798269/2500000000 : ℝ)^8369 ≤ (8662976844219/25000000000000 : ℝ)^6321 := by
    have hnat : (1122798269 : ℕ)^8369*25000000000000^6321 ≤ 8662976844219^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122798269 2500000000 8662976844219 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359824619/10000000000 : ℝ), (4232250917/10000000000 : ℝ), (1122798269/2500000000 : ℝ)] ![(33316334197669/100000000000000 : ℝ), (1281270336133/4000000000000 : ℝ), (8662976844219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359824619/10000000000 : ℝ)|^8369 ≤ (33316334197669/100000000000000 : ℝ)^6321
        have hw : |(4359824619/10000000000 : ℝ)|=(4359824619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232250917/10000000000 : ℝ)|^8369 ≤ (1281270336133/4000000000000 : ℝ)^6321
        have hw : |(4232250917/10000000000 : ℝ)|=(4232250917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122798269/2500000000 : ℝ)|^8369 ≤ (8662976844219/25000000000000 : ℝ)^6321
        have hw : |(1122798269/2500000000 : ℝ)|=(1122798269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s5_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-86023973/400000000 : ℝ)*x 0 + (5265076411/10000000000 : ℝ)*x 1 + (1348425329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86023973/400000000 : ℝ)^8369 ≤ (13071011814213/100000000000000 : ℝ)^6321 := by
    have hnat : (86023973 : ℕ)^8369*100000000000000^6321 ≤ 13071011814213^6321*400000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86023973 400000000 13071011814213 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265076411/10000000000 : ℝ)^8369 ≤ (5346258866277/12500000000000 : ℝ)^6321 := by
    have hnat : (5265076411 : ℕ)^8369*12500000000000^6321 ≤ 5346258866277^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265076411 10000000000 5346258866277 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348425329/2500000000 : ℝ)^8369 ≤ (441589172413/1000000000000 : ℝ)^6321 := by
    have hnat : (1348425329 : ℕ)^8369*1000000000000^6321 ≤ 441589172413^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348425329 2500000000 441589172413 1000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86023973/400000000 : ℝ), (5265076411/10000000000 : ℝ), (1348425329/2500000000 : ℝ)] ![(13071011814213/100000000000000 : ℝ), (5346258866277/12500000000000 : ℝ), (441589172413/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86023973/400000000 : ℝ)|^8369 ≤ (13071011814213/100000000000000 : ℝ)^6321
        have hw : |(-86023973/400000000 : ℝ)|=(86023973/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265076411/10000000000 : ℝ)|^8369 ≤ (5346258866277/12500000000000 : ℝ)^6321
        have hw : |(5265076411/10000000000 : ℝ)|=(5265076411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348425329/2500000000 : ℝ)|^8369 ≤ (441589172413/1000000000000 : ℝ)^6321
        have hw : |(1348425329/2500000000 : ℝ)|=(1348425329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s5_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312193473/10000000000 : ℝ)*x 0 + (-130451837/625000000 : ℝ)*x 1 + (269685063/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312193473/10000000000 : ℝ)^8369 ≤ (4327756288667/10000000000000 : ℝ)^6321 := by
    have hnat : (5312193473 : ℕ)^8369*10000000000000^6321 ≤ 4327756288667^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312193473 10000000000 4327756288667 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130451837/625000000 : ℝ)^8369 ≤ (98152503577/781250000000 : ℝ)^6321 := by
    have hnat : (130451837 : ℕ)^8369*781250000000^6321 ≤ 98152503577^6321*625000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130451837 625000000 98152503577 781250000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269685063/500000000 : ℝ)^8369 ≤ (22079458317137/50000000000000 : ℝ)^6321 := by
    have hnat : (269685063 : ℕ)^8369*50000000000000^6321 ≤ 22079458317137^6321*500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269685063 500000000 22079458317137 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312193473/10000000000 : ℝ), (-130451837/625000000 : ℝ), (269685063/500000000 : ℝ)] ![(4327756288667/10000000000000 : ℝ), (98152503577/781250000000 : ℝ), (22079458317137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312193473/10000000000 : ℝ)|^8369 ≤ (4327756288667/10000000000000 : ℝ)^6321
        have hw : |(5312193473/10000000000 : ℝ)|=(5312193473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130451837/625000000 : ℝ)|^8369 ≤ (98152503577/781250000000 : ℝ)^6321
        have hw : |(-130451837/625000000 : ℝ)|=(130451837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269685063/500000000 : ℝ)|^8369 ≤ (22079458317137/50000000000000 : ℝ)^6321
        have hw : |(269685063/500000000 : ℝ)|=(269685063/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s5_6 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132804823/250000000 : ℝ)*x 0 + (5393701687/10000000000 : ℝ)*x 1 + (-2087229561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132804823/250000000 : ℝ)^8369 ≤ (10819389230447/25000000000000 : ℝ)^6321 := by
    have hnat : (132804823 : ℕ)^8369*25000000000000^6321 ≤ 10819389230447^6321*250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132804823 250000000 10819389230447 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393701687/10000000000 : ℝ)^8369 ≤ (172495786183/390625000000 : ℝ)^6321 := by
    have hnat : (5393701687 : ℕ)^8369*390625000000^6321 ≤ 172495786183^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393701687 10000000000 172495786183 390625000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087229561/10000000000 : ℝ)^8369 ≤ (2512704360939/20000000000000 : ℝ)^6321 := by
    have hnat : (2087229561 : ℕ)^8369*20000000000000^6321 ≤ 2512704360939^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087229561 10000000000 2512704360939 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132804823/250000000 : ℝ), (5393701687/10000000000 : ℝ), (-2087229561/10000000000 : ℝ)] ![(10819389230447/25000000000000 : ℝ), (172495786183/390625000000 : ℝ), (2512704360939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132804823/250000000 : ℝ)|^8369 ≤ (10819389230447/25000000000000 : ℝ)^6321
        have hw : |(132804823/250000000 : ℝ)|=(132804823/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393701687/10000000000 : ℝ)|^8369 ≤ (172495786183/390625000000 : ℝ)^6321
        have hw : |(5393701687/10000000000 : ℝ)|=(5393701687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087229561/10000000000 : ℝ)|^8369 ≤ (2512704360939/20000000000000 : ℝ)^6321
        have hw : |(-2087229561/10000000000 : ℝ)|=(2087229561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s5_7 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359834847/10000000000 : ℝ)*x 0 + (2245262623/5000000000 : ℝ)*x 1 + (52911517/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359834847/10000000000 : ℝ)^8369 ≤ (16658218840077/50000000000000 : ℝ)^6321 := by
    have hnat : (4359834847 : ℕ)^8369*50000000000000^6321 ≤ 16658218840077^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359834847 10000000000 16658218840077 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245262623/5000000000 : ℝ)^8369 ≤ (8661271356221/25000000000000 : ℝ)^6321 := by
    have hnat : (2245262623 : ℕ)^8369*25000000000000^6321 ≤ 8661271356221^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245262623 5000000000 8661271356221 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52911517/125000000 : ℝ)^8369 ≤ (4004809608727/12500000000000 : ℝ)^6321 := by
    have hnat : (52911517 : ℕ)^8369*12500000000000^6321 ≤ 4004809608727^6321*125000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52911517 125000000 4004809608727 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359834847/10000000000 : ℝ), (2245262623/5000000000 : ℝ), (52911517/125000000 : ℝ)] ![(16658218840077/50000000000000 : ℝ), (8661271356221/25000000000000 : ℝ), (4004809608727/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359834847/10000000000 : ℝ)|^8369 ≤ (16658218840077/50000000000000 : ℝ)^6321
        have hw : |(4359834847/10000000000 : ℝ)|=(4359834847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245262623/5000000000 : ℝ)|^8369 ≤ (8661271356221/25000000000000 : ℝ)^6321
        have hw : |(2245262623/5000000000 : ℝ)|=(2245262623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52911517/125000000 : ℝ)|^8369 ≤ (4004809608727/12500000000000 : ℝ)^6321
        have hw : |(52911517/125000000 : ℝ)|=(52911517/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2841/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14103/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5619/50000 : ℝ) ^ (523/128 : ℝ) ≤ (13218272456676109/100000000000000000000 : ℝ) := by
    have hpowers : (5619/50000 : ℝ)^523 ≤ (13218272456676109/100000000000000000000 : ℝ)^128 := by
      have hnat : (5619 : ℕ)^523*100000000000000000000^128 ≤ 13218272456676109^128*50000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5619 50000 13218272456676109 100000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5619/50000 : ℝ)) (X := (13218272456676109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (523/128 : ℝ) ≤ (17358687548677283/50000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^523 ≤ (17358687548677283/50000000000000000000 : ℝ)^128 := by
      have hnat : (7117 : ℕ)^523*50000000000000000000^128 ≤ 17358687548677283^128*50000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 17358687548677283 50000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (17358687548677283/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013218272456676109/50000000000000000000 : ℝ) ≤ (2000129389674249/2000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (50013218272456676109/50000000000000000000 : ℝ)^128 ≤ (2000129389674249/2000000000000000 : ℝ)^523 := by
      have hnat : (50013218272456676109 : ℕ)^128*2000000000000000^523 ≤ 2000129389674249^523*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013218272456676109 50000000000000000000 2000129389674249 2000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000129389674249/2000000000000000 : ℝ)) (X := (50013218272456676109/50000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001917425902161227/4000000000000000000 : ℝ) ≤ (100011729737111/100000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (4001917425902161227/4000000000000000000 : ℝ)^128 ≤ (100011729737111/100000000000000 : ℝ)^523 := by
      have hnat : (4001917425902161227 : ℕ)^128*100000000000000^523 ≤ 100011729737111^523*4000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001917425902161227 4000000000000000000 100011729737111 100000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100011729737111/100000000000000 : ℝ)) (X := (4001917425902161227/4000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017358687548677283/25000000000000000000 : ℝ) ≤ (2000339799810191/2000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (25017358687548677283/25000000000000000000 : ℝ)^128 ≤ (2000339799810191/2000000000000000 : ℝ)^523 := by
      have hnat : (25017358687548677283 : ℕ)^128*2000000000000000^523 ≤ 2000339799810191^523*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017358687548677283 25000000000000000000 2000339799810191 2000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000339799810191/2000000000000000 : ℝ)) (X := (25017358687548677283/25000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13218272456676109/100000000000000000000 : ℝ) ≤ ((374376441397270863/374500000000000000 : ℝ)+2*(105205067971/59920000000000 : ℝ)*(5619/50000 : ℝ))^(523/128 : ℝ) := by
    rw [show (374376441397270863/374500000000000000 : ℝ)+2*(105205067971/59920000000000 : ℝ)*(5619/50000 : ℝ)=(2000129389674249/2000000000000000 : ℝ) by norm_num, show 1+2*(13218272456676109/100000000000000000000 : ℝ)=(50013218272456676109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17358687548677283/50000000000000000000 : ℝ)+(13218272456676109/100000000000000000000 : ℝ) ≤ ((374376441397270863/374500000000000000 : ℝ)+(105205067971/59920000000000 : ℝ)*((7117/50000 : ℝ)+(5619/50000 : ℝ)))^(523/128 : ℝ) := by
    rw [show (374376441397270863/374500000000000000 : ℝ)+(105205067971/59920000000000 : ℝ)*((7117/50000 : ℝ)+(5619/50000 : ℝ))=(100011729737111/100000000000000 : ℝ) by norm_num, show 1+(17358687548677283/50000000000000000000 : ℝ)+(13218272456676109/100000000000000000000 : ℝ)=(4001917425902161227/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17358687548677283/50000000000000000000 : ℝ) ≤ ((374376441397270863/374500000000000000 : ℝ)+2*(105205067971/59920000000000 : ℝ)*(7117/50000 : ℝ))^(523/128 : ℝ) := by
    rw [show (374376441397270863/374500000000000000 : ℝ)+2*(105205067971/59920000000000 : ℝ)*(7117/50000 : ℝ)=(2000339799810191/2000000000000000 : ℝ) by norm_num, show 1+2*(17358687548677283/50000000000000000000 : ℝ)=(25017358687548677283/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (374376441397270863/374500000000000000 : ℝ)*(X 1 0+X 2 0)+(105205067971/59920000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (374376441397270863/374500000000000000 : ℝ)) (alpha := (105205067971/59920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (374376441397270863/374500000000000000 : ℝ)*(X 0 1+X 2 1)+(105205067971/59920000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (374376441397270863/374500000000000000 : ℝ)) (alpha := (105205067971/59920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (374376441397270863/374500000000000000 : ℝ)*(X 0 2+X 1 2)+(105205067971/59920000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (374376441397270863/374500000000000000 : ℝ)) (alpha := (105205067971/59920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215059403/1000000000 : ℝ)*X 0 0+(1348508997/2500000000 : ℝ)*X 0 1+(5264743067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672515439/5000000000 : ℝ)*X 1 0+(-277023517/1250000000 : ℝ)*X 1 1+(526474311/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336257731/2500000000 : ℝ)*X 2 0+(2632371481/5000000000 : ℝ)*X 2 1+(-221618827/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359824619/10000000000 : ℝ)*X 0 0+(4232250917/10000000000 : ℝ)*X 0 1+(1122798269/2500000000 : ℝ)*X 0 2+(4359824619/10000000000 : ℝ)*X 1 0+(4232250917/10000000000 : ℝ)*X 1 1+(1122798269/2500000000 : ℝ)*X 1 2+(4359824619/10000000000 : ℝ)*X 2 0+(4232250917/10000000000 : ℝ)*X 2 1+(1122798269/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-86023973/400000000 : ℝ)*X 0 0+(5265076411/10000000000 : ℝ)*X 0 1+(1348425329/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312193473/10000000000 : ℝ)*X 1 0+(-130451837/625000000 : ℝ)*X 1 1+(269685063/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132804823/250000000 : ℝ)*X 2 0+(5393701687/10000000000 : ℝ)*X 2 1+(-2087229561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359834847/10000000000 : ℝ)*X 0 0+(2245262623/5000000000 : ℝ)*X 0 1+(52911517/125000000 : ℝ)*X 0 2+(4359834847/10000000000 : ℝ)*X 1 0+(2245262623/5000000000 : ℝ)*X 1 1+(52911517/125000000 : ℝ)*X 1 2+(4359834847/10000000000 : ℝ)*X 2 0+(2245262623/5000000000 : ℝ)*X 2 1+(52911517/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146863586505888339531507897/18725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (690672991/50000000000000 : ℝ)*(base19) + (319275651/25000000000000 : ℝ)*(base23) + (81979859/50000000000000 : ℝ)*(lower2) + (163418809/50000000000000 : ℝ)*(upper3) + (581303/800000000000 : ℝ)*(lower4) + (5798177630917327/100000000000000 : ℝ)*(major0) + (5798177630917327/100000000000000 : ℝ)*(major1) + (5798177630917327/100000000000000 : ℝ)*(major2) + (386720795786393/5000000000000 : ℝ)*(sp0) + (7734442490972671/100000000000000 : ℝ)*(sp1) + (7734442595216049/100000000000000 : ℝ)*(sp2) + (3861884787136909/100000000000000 : ℝ)*(sp3) + (27956590793/100000000000000 : ℝ)*(sp4) + (26340939681/100000000000000 : ℝ)*(sp7) + (386191112807659/10000000000000 : ℝ)*(f.failure) + (7734443872318653/100000000000000 : ℝ)*(f.sum) + (183559481671/2996000000000000000000000000 : ℝ)*base66 + (32541019447524451/37450000000000000000000000000000 : ℝ)*base67 + (238547051088975549/37450000000000000000000000000000 : ℝ)*base70 + (55731185419224451/37450000000000000000000000000000 : ℝ)*base71 + (10421936367809/2996000000000000000000000000 : ℝ)*base73 + (189348537166124451/37450000000000000000000000000000 : ℝ)*base75 + (79724121548875549/37450000000000000000000000000000 : ℝ)*base78 + (759674431261774451/37450000000000000000000000000000 : ℝ)*base79 + (14650094723573/2996000000000000000000000000 : ℝ)*base81 + (2073339/1000000000000000000000 : ℝ)*base89 + (2073339/1000000000000000000000 : ℝ)*base91 + (2073339/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (243336930817418966679033/36572265625000000000000000000 : ℝ) := by norm_num
    linear_combination (2469097103/100000000000000 : ℝ)*(base19) + (110583497/6250000000000 : ℝ)*(base23) + (208239307/100000000000000 : ℝ)*(upper3) + (82838537/100000000000000 : ℝ)*(lower4) + (55379599/50000000000000 : ℝ)*(upper5) + (2914113571873659/50000000000000 : ℝ)*(major0) + (2914113571873659/50000000000000 : ℝ)*(major1) + (2914113571873659/50000000000000 : ℝ)*(major2) + (3433529489/5000000000000 : ℝ)*(sp1) + (382298121/625000000000 : ℝ)*(sp2) + (3887264139325547/50000000000000 : ℝ)*(sp4) + (777445713896421/10000000000000 : ℝ)*(sp5) + (3887232670807891/50000000000000 : ℝ)*(sp6) + (970481446764283/25000000000000 : ℝ)*(sp7) + (970481446764283/25000000000000 : ℝ)*(f.failure) + (3887264139325547/50000000000000 : ℝ)*(f.sum) + (7901081729397/1498000000000000000000000000 : ℝ)*base65 + (263767919727353967/18725000000000000000000000000000 : ℝ)*base67 + (79928095792803967/18725000000000000000000000000000 : ℝ)*base69 + (283204303674053967/18725000000000000000000000000000 : ℝ)*base71 + (7636120256033/1498000000000000000000000000 : ℝ)*base73 + (116429099760203967/18725000000000000000000000000000 : ℝ)*base75 + (142262223540696033/18725000000000000000000000000000 : ℝ)*base78 + (38087012100353967/18725000000000000000000000000000 : ℝ)*base79 + (13051929999/11984000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (29037557/2500000000000000000000 : ℝ)*base90 + (29037557/2500000000000000000000 : ℝ)*base92 + (29037557/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1176_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1176_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1176_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16403/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1176_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1176_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1176_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16403/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1176_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
