-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1215_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:52.186637+00:00
-- url     : https://prove2.me/submissions/ae557932-2537-4325-8ea7-c67e8bec7329

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
theorem support_rectangle_w1215_s0_0 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1868919767/10000000000 : ℝ)*x 0 + (150940283/250000000 : ℝ)*x 1 + (2394817443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868919767/10000000000 : ℝ)^1051 ≤ (10890145612771/100000000000000 : ℝ)^795 := by
    have hnat : (1868919767 : ℕ)^1051*100000000000000^795 ≤ 10890145612771^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868919767 10000000000 10890145612771 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150940283/250000000 : ℝ)^1051 ≤ (25660846446361/50000000000000 : ℝ)^795 := by
    have hnat : (150940283 : ℕ)^1051*50000000000000^795 ≤ 25660846446361^795*250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150940283 250000000 25660846446361 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2394817443/5000000000 : ℝ)^1051 ≤ (9447040369763/25000000000000 : ℝ)^795 := by
    have hnat : (2394817443 : ℕ)^1051*25000000000000^795 ≤ 9447040369763^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394817443 5000000000 9447040369763 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1868919767/10000000000 : ℝ), (150940283/250000000 : ℝ), (2394817443/5000000000 : ℝ)] ![(10890145612771/100000000000000 : ℝ), (25660846446361/50000000000000 : ℝ), (9447040369763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1868919767/10000000000 : ℝ)|^1051 ≤ (10890145612771/100000000000000 : ℝ)^795
        have hw : |(-1868919767/10000000000 : ℝ)|=(1868919767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150940283/250000000 : ℝ)|^1051 ≤ (25660846446361/50000000000000 : ℝ)^795
        have hw : |(150940283/250000000 : ℝ)|=(150940283/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2394817443/5000000000 : ℝ)|^1051 ≤ (9447040369763/25000000000000 : ℝ)^795
        have hw : |(2394817443/5000000000 : ℝ)|=(2394817443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s0_1 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5512680657/10000000000 : ℝ)*x 0 + (-645773227/2500000000 : ℝ)*x 1 + (4789634857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512680657/10000000000 : ℝ)^1051 ≤ (9101404371197/20000000000000 : ℝ)^795 := by
    have hnat : (5512680657 : ℕ)^1051*20000000000000^795 ≤ 9101404371197^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512680657 10000000000 9101404371197 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (645773227/2500000000 : ℝ)^1051 ≤ (16704816959553/100000000000000 : ℝ)^795 := by
    have hnat : (645773227 : ℕ)^1051*100000000000000^795 ≤ 16704816959553^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645773227 2500000000 16704816959553 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4789634857/10000000000 : ℝ)^1051 ≤ (18894080588289/50000000000000 : ℝ)^795 := by
    have hnat : (4789634857 : ℕ)^1051*50000000000000^795 ≤ 18894080588289^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789634857 10000000000 18894080588289 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512680657/10000000000 : ℝ), (-645773227/2500000000 : ℝ), (4789634857/10000000000 : ℝ)] ![(9101404371197/20000000000000 : ℝ), (16704816959553/100000000000000 : ℝ), (18894080588289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512680657/10000000000 : ℝ)|^1051 ≤ (9101404371197/20000000000000 : ℝ)^795
        have hw : |(5512680657/10000000000 : ℝ)|=(5512680657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-645773227/2500000000 : ℝ)|^1051 ≤ (16704816959553/100000000000000 : ℝ)^795
        have hw : |(-645773227/2500000000 : ℝ)|=(645773227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4789634857/10000000000 : ℝ)|^1051 ≤ (18894080588289/50000000000000 : ℝ)^795
        have hw : |(4789634857/10000000000 : ℝ)|=(4789634857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s0_2 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5512680637/10000000000 : ℝ)*x 0 + (4789634879/10000000000 : ℝ)*x 1 + (-516618581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512680637/10000000000 : ℝ)^1051 ≤ (45507021637721/100000000000000 : ℝ)^795 := by
    have hnat : (5512680637 : ℕ)^1051*100000000000000^795 ≤ 45507021637721^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512680637 10000000000 45507021637721 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4789634879/10000000000 : ℝ)^1051 ≤ (37788161406041/100000000000000 : ℝ)^795 := by
    have hnat : (4789634879 : ℕ)^1051*100000000000000^795 ≤ 37788161406041^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789634879 10000000000 37788161406041 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516618581/2000000000 : ℝ)^1051 ≤ (1044051058369/6250000000000 : ℝ)^795 := by
    have hnat : (516618581 : ℕ)^1051*6250000000000^795 ≤ 1044051058369^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516618581 2000000000 1044051058369 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512680637/10000000000 : ℝ), (4789634879/10000000000 : ℝ), (-516618581/2000000000 : ℝ)] ![(45507021637721/100000000000000 : ℝ), (37788161406041/100000000000000 : ℝ), (1044051058369/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512680637/10000000000 : ℝ)|^1051 ≤ (45507021637721/100000000000000 : ℝ)^795
        have hw : |(5512680637/10000000000 : ℝ)|=(5512680637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4789634879/10000000000 : ℝ)|^1051 ≤ (37788161406041/100000000000000 : ℝ)^795
        have hw : |(4789634879/10000000000 : ℝ)|=(4789634879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516618581/2000000000 : ℝ)|^1051 ≤ (1044051058369/6250000000000 : ℝ)^795
        have hw : |(-516618581/2000000000 : ℝ)|=(516618581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s0_3 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (419515041/1000000000 : ℝ)*x 0 + (3117935341/10000000000 : ℝ)*x 1 + (5636351841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419515041/1000000000 : ℝ)^1051 ≤ (7928800789869/25000000000000 : ℝ)^795 := by
    have hnat : (419515041 : ℕ)^1051*25000000000000^795 ≤ 7928800789869^795*1000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419515041 1000000000 7928800789869 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117935341/10000000000 : ℝ)^1051 ≤ (10711639553139/50000000000000 : ℝ)^795 := by
    have hnat : (3117935341 : ℕ)^1051*50000000000000^795 ≤ 10711639553139^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117935341 10000000000 10711639553139 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5636351841/10000000000 : ℝ)^1051 ≤ (11715379429791/25000000000000 : ℝ)^795 := by
    have hnat : (5636351841 : ℕ)^1051*25000000000000^795 ≤ 11715379429791^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5636351841 10000000000 11715379429791 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419515041/1000000000 : ℝ), (3117935341/10000000000 : ℝ), (5636351841/10000000000 : ℝ)] ![(7928800789869/25000000000000 : ℝ), (10711639553139/50000000000000 : ℝ), (11715379429791/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419515041/1000000000 : ℝ)|^1051 ≤ (7928800789869/25000000000000 : ℝ)^795
        have hw : |(419515041/1000000000 : ℝ)|=(419515041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117935341/10000000000 : ℝ)|^1051 ≤ (10711639553139/50000000000000 : ℝ)^795
        have hw : |(3117935341/10000000000 : ℝ)|=(3117935341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5636351841/10000000000 : ℝ)|^1051 ≤ (11715379429791/25000000000000 : ℝ)^795
        have hw : |(5636351841/10000000000 : ℝ)|=(5636351841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s0_4 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1873854439/10000000000 : ℝ)*x 0 + (18835117/39062500 : ℝ)*x 1 + (1200864137/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1873854439/10000000000 : ℝ)^1051 ≤ (10928175180187/100000000000000 : ℝ)^795 := by
    have hnat : (1873854439 : ℕ)^1051*100000000000000^795 ≤ 10928175180187^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873854439 10000000000 10928175180187 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18835117/39062500 : ℝ)^1051 ≤ (7624780872731/20000000000000 : ℝ)^795 := by
    have hnat : (18835117 : ℕ)^1051*20000000000000^795 ≤ 7624780872731^795*39062500^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18835117 39062500 7624780872731 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200864137/2000000000 : ℝ)^1051 ≤ (25473960223371/50000000000000 : ℝ)^795 := by
    have hnat : (1200864137 : ℕ)^1051*50000000000000^795 ≤ 25473960223371^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200864137 2000000000 25473960223371 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1873854439/10000000000 : ℝ), (18835117/39062500 : ℝ), (1200864137/2000000000 : ℝ)] ![(10928175180187/100000000000000 : ℝ), (7624780872731/20000000000000 : ℝ), (25473960223371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1873854439/10000000000 : ℝ)|^1051 ≤ (10928175180187/100000000000000 : ℝ)^795
        have hw : |(-1873854439/10000000000 : ℝ)|=(1873854439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18835117/39062500 : ℝ)|^1051 ≤ (7624780872731/20000000000000 : ℝ)^795
        have hw : |(18835117/39062500 : ℝ)|=(18835117/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200864137/2000000000 : ℝ)|^1051 ≤ (25473960223371/50000000000000 : ℝ)^795
        have hw : |(1200864137/2000000000 : ℝ)|=(1200864137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s0_5 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1293310203/2500000000 : ℝ)*x 0 + (-42762669/312500000 : ℝ)*x 1 + (6004322453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293310203/2500000000 : ℝ)^1051 ≤ (20919952146937/50000000000000 : ℝ)^795 := by
    have hnat : (1293310203 : ℕ)^1051*50000000000000^795 ≤ 20919952146937^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293310203 2500000000 20919952146937 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42762669/312500000 : ℝ)^1051 ≤ (450759713051/6250000000000 : ℝ)^795 := by
    have hnat : (42762669 : ℕ)^1051*6250000000000^795 ≤ 450759713051^795*312500000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42762669 312500000 450759713051 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6004322453/10000000000 : ℝ)^1051 ≤ (50947940279379/100000000000000 : ℝ)^795 := by
    have hnat : (6004322453 : ℕ)^1051*100000000000000^795 ≤ 50947940279379^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6004322453 10000000000 50947940279379 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293310203/2500000000 : ℝ), (-42762669/312500000 : ℝ), (6004322453/10000000000 : ℝ)] ![(20919952146937/50000000000000 : ℝ), (450759713051/6250000000000 : ℝ), (50947940279379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293310203/2500000000 : ℝ)|^1051 ≤ (20919952146937/50000000000000 : ℝ)^795
        have hw : |(1293310203/2500000000 : ℝ)|=(1293310203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42762669/312500000 : ℝ)|^1051 ≤ (450759713051/6250000000000 : ℝ)^795
        have hw : |(-42762669/312500000 : ℝ)|=(42762669/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6004322453/10000000000 : ℝ)|^1051 ≤ (50947940279379/100000000000000 : ℝ)^795
        have hw : |(6004322453/10000000000 : ℝ)|=(6004322453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s0_6 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2586620849/5000000000 : ℝ)*x 0 + (6004321157/10000000000 : ℝ)*x 1 + (-273681227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586620849/5000000000 : ℝ)^1051 ≤ (41839913767087/100000000000000 : ℝ)^795 := by
    have hnat : (2586620849 : ℕ)^1051*100000000000000^795 ≤ 41839913767087^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586620849 5000000000 41839913767087 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6004321157/10000000000 : ℝ)^1051 ≤ (12736981435357/25000000000000 : ℝ)^795 := by
    have hnat : (6004321157 : ℕ)^1051*25000000000000^795 ≤ 12736981435357^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6004321157 10000000000 12736981435357 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273681227/2000000000 : ℝ)^1051 ≤ (7212160474293/100000000000000 : ℝ)^795 := by
    have hnat : (273681227 : ℕ)^1051*100000000000000^795 ≤ 7212160474293^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273681227 2000000000 7212160474293 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586620849/5000000000 : ℝ), (6004321157/10000000000 : ℝ), (-273681227/2000000000 : ℝ)] ![(41839913767087/100000000000000 : ℝ), (12736981435357/25000000000000 : ℝ), (7212160474293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586620849/5000000000 : ℝ)|^1051 ≤ (41839913767087/100000000000000 : ℝ)^795
        have hw : |(2586620849/5000000000 : ℝ)|=(2586620849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6004321157/10000000000 : ℝ)|^1051 ≤ (12736981435357/25000000000000 : ℝ)^795
        have hw : |(6004321157/10000000000 : ℝ)|=(6004321157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273681227/2000000000 : ℝ)|^1051 ≤ (7212160474293/100000000000000 : ℝ)^795
        have hw : |(-273681227/2000000000 : ℝ)|=(273681227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s0_7 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (841021531/2000000000 : ℝ)*x 0 + (2785733473/5000000000 : ℝ)*x 1 + (3185110911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841021531/2000000000 : ℝ)^1051 ≤ (15907378794399/50000000000000 : ℝ)^795 := by
    have hnat : (841021531 : ℕ)^1051*50000000000000^795 ≤ 15907378794399^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841021531 2000000000 15907378794399 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2785733473/5000000000 : ℝ)^1051 ≤ (11537416459923/25000000000000 : ℝ)^795 := by
    have hnat : (2785733473 : ℕ)^1051*25000000000000^795 ≤ 11537416459923^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785733473 5000000000 11537416459923 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185110911/10000000000 : ℝ)^1051 ≤ (22035576548359/100000000000000 : ℝ)^795 := by
    have hnat : (3185110911 : ℕ)^1051*100000000000000^795 ≤ 22035576548359^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185110911 10000000000 22035576548359 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841021531/2000000000 : ℝ), (2785733473/5000000000 : ℝ), (3185110911/10000000000 : ℝ)] ![(15907378794399/50000000000000 : ℝ), (11537416459923/25000000000000 : ℝ), (22035576548359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841021531/2000000000 : ℝ)|^1051 ≤ (15907378794399/50000000000000 : ℝ)^795
        have hw : |(841021531/2000000000 : ℝ)|=(841021531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2785733473/5000000000 : ℝ)|^1051 ≤ (11537416459923/25000000000000 : ℝ)^795
        have hw : |(2785733473/5000000000 : ℝ)|=(2785733473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185110911/10000000000 : ℝ)|^1051 ≤ (22035576548359/100000000000000 : ℝ)^795
        have hw : |(3185110911/10000000000 : ℝ)|=(3185110911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1215_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (71/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13769/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8407/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8407 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8407*1^2048 ≤ 0^2048*1^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8407/2048 : ℝ) ≤ (116260996480703301/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8407 ≤ (116260996480703301/5000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8407*5000000000000000000^2048 ≤ 116260996480703301^2048*5^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 116260996480703301 5000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (116260996480703301/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8407 := by
      have hnat : (1 : ℕ)^2048*1^8407 ≤ 1^8407*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5116260996480703301/5000000000000000000 : ℝ) ≤ (10056152426553771/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (5116260996480703301/5000000000000000000 : ℝ)^2048 ≤ (10056152426553771/10000000000000000 : ℝ)^8407 := by
      have hnat : (5116260996480703301 : ℕ)^2048*10000000000000000^8407 ≤ 10056152426553771^8407*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5116260996480703301 5000000000000000000 10056152426553771 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056152426553771/10000000000000000 : ℝ)) (X := (5116260996480703301/5000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2616260996480703301/2500000000000000000 : ℝ) ≤ (5056152426553771/5000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (2616260996480703301/2500000000000000000 : ℝ)^2048 ≤ (5056152426553771/5000000000000000 : ℝ)^8407 := by
      have hnat : (2616260996480703301 : ℕ)^2048*5000000000000000^8407 ≤ 5056152426553771^8407*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2616260996480703301 2500000000000000000 5056152426553771 5000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056152426553771/5000000000000000 : ℝ)) (X := (2616260996480703301/2500000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(56152426553771/4000000000000000 : ℝ)*(0 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56152426553771/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(116260996480703301/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(56152426553771/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8407/2048 : ℝ) := by
    rw [show (1 : ℝ)+(56152426553771/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10056152426553771/10000000000000000 : ℝ) by norm_num, show 1+(116260996480703301/5000000000000000000 : ℝ)+(0 : ℝ)=(5116260996480703301/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(116260996480703301/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(56152426553771/4000000000000000 : ℝ)*(2/5 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56152426553771/4000000000000000 : ℝ)*(2/5 : ℝ)=(5056152426553771/5000000000000000 : ℝ) by norm_num, show 1+2*(116260996480703301/5000000000000000000 : ℝ)=(2616260996480703301/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(56152426553771/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56152426553771/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(56152426553771/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56152426553771/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(56152426553771/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56152426553771/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1868919767/10000000000 : ℝ)*X 0 0+(150940283/250000000 : ℝ)*X 0 1+(2394817443/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512680657/10000000000 : ℝ)*X 1 0+(-645773227/2500000000 : ℝ)*X 1 1+(4789634857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5512680637/10000000000 : ℝ)*X 2 0+(4789634879/10000000000 : ℝ)*X 2 1+(-516618581/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((419515041/1000000000 : ℝ)*X 0 0+(3117935341/10000000000 : ℝ)*X 0 1+(5636351841/10000000000 : ℝ)*X 0 2+(419515041/1000000000 : ℝ)*X 1 0+(3117935341/10000000000 : ℝ)*X 1 1+(5636351841/10000000000 : ℝ)*X 1 2+(419515041/1000000000 : ℝ)*X 2 0+(3117935341/10000000000 : ℝ)*X 2 1+(5636351841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1873854439/10000000000 : ℝ)*X 0 0+(18835117/39062500 : ℝ)*X 0 1+(1200864137/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1293310203/2500000000 : ℝ)*X 1 0+(-42762669/312500000 : ℝ)*X 1 1+(6004322453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2586620849/5000000000 : ℝ)*X 2 0+(6004321157/10000000000 : ℝ)*X 2 1+(-273681227/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((841021531/2000000000 : ℝ)*X 0 0+(2785733473/5000000000 : ℝ)*X 0 1+(3185110911/10000000000 : ℝ)*X 0 2+(841021531/2000000000 : ℝ)*X 1 0+(2785733473/5000000000 : ℝ)*X 1 1+(3185110911/10000000000 : ℝ)*X 1 2+(841021531/2000000000 : ℝ)*X 2 0+(2785733473/5000000000 : ℝ)*X 2 1+(3185110911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3080745938686674759/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (68889111/100000000000000 : ℝ)*(base1) + (753121049/50000000000000 : ℝ)*(base19) + (1400247091/100000000000000 : ℝ)*(base23) + (25771969/25000000000000 : ℝ)*(base24) + (344063587/100000000000000 : ℝ)*(upper3) + (299596223942821/50000000000000 : ℝ)*(major0) + (299596223942821/50000000000000 : ℝ)*(major1) + (299596223942821/50000000000000 : ℝ)*(major2) + (400651138881549/50000000000000 : ℝ)*(sp0) + (801304040321281/100000000000000 : ℝ)*(sp1) + (200326010807103/25000000000000 : ℝ)*(sp2) + (397076445094199/100000000000000 : ℝ)*(sp3) + (208605587/6250000000000 : ℝ)*(sp4) + (2629841531/100000000000000 : ℝ)*(sp7) + (397079143824841/100000000000000 : ℝ)*(f.failure) + (801305546563379/100000000000000 : ℝ)*(f.sum) + (57890571827991/100000000000000000000000000000 : ℝ)*base65 + (80313159872009/200000000000000000000000000000 : ℝ)*base68 + (133757696327991/200000000000000000000000000000 : ℝ)*base69 + (644432183527991/200000000000000000000000000000 : ℝ)*base71 + (147851817772009/100000000000000000000000000000 : ℝ)*base74 + (485441402527991/200000000000000000000000000000 : ℝ)*base75 + (148867181872009/200000000000000000000000000000 : ℝ)*base78 + (345022119327991/200000000000000000000000000000 : ℝ)*base79 + (35987038072009/100000000000000000000000000000 : ℝ)*base82 + (5204841/2000000000000000000000 : ℝ)*base89 + (5204841/2000000000000000000000 : ℝ)*base91 + (5204841/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39517050659700689606943/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5435059/25000000000000 : ℝ)*(base1) + (2138832591/100000000000000 : ℝ)*(base19) + (2307802853/100000000000000 : ℝ)*(base23) + (405729901/100000000000000 : ℝ)*(upper3) + (7668549/6250000000000 : ℝ)*(upper5) + (63234618972511/10000000000000 : ℝ)*(major0) + (63234618972511/10000000000000 : ℝ)*(major1) + (63234618972511/10000000000000 : ℝ)*(major2) + (963761647/20000000000000 : ℝ)*(sp1) + (5186742409/100000000000000 : ℝ)*(sp2) + (105705290513771/12500000000000 : ℝ)*(sp4) + (169127068945821/20000000000000 : ℝ)*(sp5) + (84563480782467/10000000000000 : ℝ)*(sp6) + (104762447973261/25000000000000 : ℝ)*(sp7) + (327382666901/78125000000 : ℝ)*(f.failure) + (211410575592483/25000000000000 : ℝ)*(f.sum) + (6531608971019/20000000000000000000000000000 : ℝ)*base66 + (174525510011019/40000000000000000000000000000 : ℝ)*base68 + (131080414171019/40000000000000000000000000000 : ℝ)*base70 + (89636893388981/40000000000000000000000000000 : ℝ)*base71 + (81771815691019/20000000000000000000000000000 : ℝ)*base74 + (30218910628981/40000000000000000000000000000 : ℝ)*base75 + (101206328131019/40000000000000000000000000000 : ℝ)*base78 + (188885300611019/40000000000000000000000000000 : ℝ)*base80 + (33986177391019/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3151/1562500000000000000 : ℝ)*base89 + (3151/1562500000000000000 : ℝ)*base91 + (3151/1562500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1215_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (71/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13769/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1215_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1215_s1_0 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-10341451/50000000 : ℝ)*x 0 + (355153057/625000000 : ℝ)*x 1 + (2508588453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10341451/50000000 : ℝ)^1051 ≤ (3112932967459/25000000000000 : ℝ)^795 := by
    have hnat : (10341451 : ℕ)^1051*25000000000000^795 ≤ 3112932967459^795*50000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10341451 50000000 3112932967459 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355153057/625000000 : ℝ)^1051 ≤ (23684427993481/50000000000000 : ℝ)^795 := by
    have hnat : (355153057 : ℕ)^1051*50000000000000^795 ≤ 23684427993481^795*625000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355153057 625000000 23684427993481 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508588453/5000000000 : ℝ)^1051 ≤ (8035882425781/20000000000000 : ℝ)^795 := by
    have hnat : (2508588453 : ℕ)^1051*20000000000000^795 ≤ 8035882425781^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508588453 5000000000 8035882425781 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10341451/50000000 : ℝ), (355153057/625000000 : ℝ), (2508588453/5000000000 : ℝ)] ![(3112932967459/25000000000000 : ℝ), (23684427993481/50000000000000 : ℝ), (8035882425781/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10341451/50000000 : ℝ)|^1051 ≤ (3112932967459/25000000000000 : ℝ)^795
        have hw : |(-10341451/50000000 : ℝ)|=(10341451/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(355153057/625000000 : ℝ)|^1051 ≤ (23684427993481/50000000000000 : ℝ)^795
        have hw : |(355153057/625000000 : ℝ)|=(355153057/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2508588453/5000000000 : ℝ)|^1051 ≤ (8035882425781/20000000000000 : ℝ)^795
        have hw : |(2508588453/5000000000 : ℝ)|=(2508588453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s1_1 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2707565131/5000000000 : ℝ)*x 0 + (-242600019/1000000000 : ℝ)*x 1 + (1254294359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707565131/5000000000 : ℝ)^1051 ≤ (22222741272939/50000000000000 : ℝ)^795 := by
    have hnat : (2707565131 : ℕ)^1051*50000000000000^795 ≤ 22222741272939^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707565131 5000000000 22222741272939 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242600019/1000000000 : ℝ)^1051 ≤ (1537509970399/10000000000000 : ℝ)^795 := by
    have hnat : (242600019 : ℕ)^1051*10000000000000^795 ≤ 1537509970399^795*1000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242600019 1000000000 1537509970399 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1254294359/2500000000 : ℝ)^1051 ≤ (5022427217513/12500000000000 : ℝ)^795 := by
    have hnat : (1254294359 : ℕ)^1051*12500000000000^795 ≤ 5022427217513^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254294359 2500000000 5022427217513 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707565131/5000000000 : ℝ), (-242600019/1000000000 : ℝ), (1254294359/2500000000 : ℝ)] ![(22222741272939/50000000000000 : ℝ), (1537509970399/10000000000000 : ℝ), (5022427217513/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707565131/5000000000 : ℝ)|^1051 ≤ (22222741272939/50000000000000 : ℝ)^795
        have hw : |(2707565131/5000000000 : ℝ)|=(2707565131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-242600019/1000000000 : ℝ)|^1051 ≤ (1537509970399/10000000000000 : ℝ)^795
        have hw : |(-242600019/1000000000 : ℝ)|=(242600019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1254294359/2500000000 : ℝ)|^1051 ≤ (5022427217513/12500000000000 : ℝ)^795
        have hw : |(1254294359/2500000000 : ℝ)|=(1254294359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s1_2 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (541512891/1000000000 : ℝ)*x 0 + (5017178301/10000000000 : ℝ)*x 1 + (-1213000423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541512891/1000000000 : ℝ)^1051 ≤ (44445467875849/100000000000000 : ℝ)^795 := by
    have hnat : (541512891 : ℕ)^1051*100000000000000^795 ≤ 44445467875849^795*1000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541512891 1000000000 44445467875849 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5017178301/10000000000 : ℝ)^1051 ≤ (10044856724501/25000000000000 : ℝ)^795 := by
    have hnat : (5017178301 : ℕ)^1051*25000000000000^795 ≤ 10044856724501^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017178301 10000000000 10044856724501 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1213000423/5000000000 : ℝ)^1051 ≤ (15375105200241/100000000000000 : ℝ)^795 := by
    have hnat : (1213000423 : ℕ)^1051*100000000000000^795 ≤ 15375105200241^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213000423 5000000000 15375105200241 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541512891/1000000000 : ℝ), (5017178301/10000000000 : ℝ), (-1213000423/5000000000 : ℝ)] ![(44445467875849/100000000000000 : ℝ), (10044856724501/25000000000000 : ℝ), (15375105200241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541512891/1000000000 : ℝ)|^1051 ≤ (44445467875849/100000000000000 : ℝ)^795
        have hw : |(541512891/1000000000 : ℝ)|=(541512891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5017178301/10000000000 : ℝ)|^1051 ≤ (10044856724501/25000000000000 : ℝ)^795
        have hw : |(5017178301/10000000000 : ℝ)|=(5017178301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1213000423/5000000000 : ℝ)|^1051 ≤ (15375105200241/100000000000000 : ℝ)^795
        have hw : |(-1213000423/5000000000 : ℝ)|=(1213000423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s1_3 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4311190047/10000000000 : ℝ)*x 0 + (3690532797/10000000000 : ℝ)*x 1 + (5033053149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311190047/10000000000 : ℝ)^1051 ≤ (822001989087/2500000000000 : ℝ)^795 := by
    have hnat : (4311190047 : ℕ)^1051*2500000000000^795 ≤ 822001989087^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311190047 10000000000 822001989087 2500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3690532797/10000000000 : ℝ)^1051 ≤ (26772338289409/100000000000000 : ℝ)^795 := by
    have hnat : (3690532797 : ℕ)^1051*100000000000000^795 ≤ 26772338289409^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3690532797 10000000000 26772338289409 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5033053149/10000000000 : ℝ)^1051 ≤ (20173791067653/50000000000000 : ℝ)^795 := by
    have hnat : (5033053149 : ℕ)^1051*50000000000000^795 ≤ 20173791067653^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033053149 10000000000 20173791067653 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311190047/10000000000 : ℝ), (3690532797/10000000000 : ℝ), (5033053149/10000000000 : ℝ)] ![(822001989087/2500000000000 : ℝ), (26772338289409/100000000000000 : ℝ), (20173791067653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311190047/10000000000 : ℝ)|^1051 ≤ (822001989087/2500000000000 : ℝ)^795
        have hw : |(4311190047/10000000000 : ℝ)|=(4311190047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3690532797/10000000000 : ℝ)|^1051 ≤ (26772338289409/100000000000000 : ℝ)^795
        have hw : |(3690532797/10000000000 : ℝ)|=(3690532797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5033053149/10000000000 : ℝ)|^1051 ≤ (20173791067653/50000000000000 : ℝ)^795
        have hw : |(5033053149/10000000000 : ℝ)|=(5033053149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s1_4 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-51724903/250000000 : ℝ)*x 0 + (1256501823/2500000000 : ℝ)*x 1 + (2836725517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51724903/250000000 : ℝ)^1051 ≤ (12457350535921/100000000000000 : ℝ)^795 := by
    have hnat : (51724903 : ℕ)^1051*100000000000000^795 ≤ 12457350535921^795*250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51724903 250000000 12457350535921 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1256501823/2500000000 : ℝ)^1051 ≤ (10068231844851/25000000000000 : ℝ)^795 := by
    have hnat : (1256501823 : ℕ)^1051*25000000000000^795 ≤ 10068231844851^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256501823 2500000000 10068231844851 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2836725517/5000000000 : ℝ)^1051 ≤ (4726972206943/10000000000000 : ℝ)^795 := by
    have hnat : (2836725517 : ℕ)^1051*10000000000000^795 ≤ 4726972206943^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2836725517 5000000000 4726972206943 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51724903/250000000 : ℝ), (1256501823/2500000000 : ℝ), (2836725517/5000000000 : ℝ)] ![(12457350535921/100000000000000 : ℝ), (10068231844851/25000000000000 : ℝ), (4726972206943/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51724903/250000000 : ℝ)|^1051 ≤ (12457350535921/100000000000000 : ℝ)^795
        have hw : |(-51724903/250000000 : ℝ)|=(51724903/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1256501823/2500000000 : ℝ)|^1051 ≤ (10068231844851/25000000000000 : ℝ)^795
        have hw : |(1256501823/2500000000 : ℝ)|=(1256501823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2836725517/5000000000 : ℝ)|^1051 ≤ (4726972206943/10000000000000 : ℝ)^795
        have hw : |(2836725517/5000000000 : ℝ)|=(2836725517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s1_5 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1310988987/2500000000 : ℝ)*x 0 + (-884865449/5000000000 : ℝ)*x 1 + (5673446523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310988987/2500000000 : ℝ)^1051 ≤ (21298828763/50000000000 : ℝ)^795 := by
    have hnat : (1310988987 : ℕ)^1051*50000000000^795 ≤ 21298828763^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310988987 2500000000 21298828763 50000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884865449/5000000000 : ℝ)^1051 ≤ (2026534015927/20000000000000 : ℝ)^795 := by
    have hnat : (884865449 : ℕ)^1051*20000000000000^795 ≤ 2026534015927^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884865449 5000000000 2026534015927 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5673446523/10000000000 : ℝ)^1051 ≤ (47269672382279/100000000000000 : ℝ)^795 := by
    have hnat : (5673446523 : ℕ)^1051*100000000000000^795 ≤ 47269672382279^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673446523 10000000000 47269672382279 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310988987/2500000000 : ℝ), (-884865449/5000000000 : ℝ), (5673446523/10000000000 : ℝ)] ![(21298828763/50000000000 : ℝ), (2026534015927/20000000000000 : ℝ), (47269672382279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310988987/2500000000 : ℝ)|^1051 ≤ (21298828763/50000000000 : ℝ)^795
        have hw : |(1310988987/2500000000 : ℝ)|=(1310988987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-884865449/5000000000 : ℝ)|^1051 ≤ (2026534015927/20000000000000 : ℝ)^795
        have hw : |(-884865449/5000000000 : ℝ)|=(884865449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5673446523/10000000000 : ℝ)|^1051 ≤ (47269672382279/100000000000000 : ℝ)^795
        have hw : |(5673446523/10000000000 : ℝ)|=(5673446523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s1_6 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5243956103/10000000000 : ℝ)*x 0 + (1418361741/2500000000 : ℝ)*x 1 + (-1769730037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243956103/10000000000 : ℝ)^1051 ≤ (42597659190539/100000000000000 : ℝ)^795 := by
    have hnat : (5243956103 : ℕ)^1051*100000000000000^795 ≤ 42597659190539^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243956103 10000000000 42597659190539 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1418361741/2500000000 : ℝ)^1051 ≤ (23634838619873/50000000000000 : ℝ)^795 := by
    have hnat : (1418361741 : ℕ)^1051*50000000000000^795 ≤ 23634838619873^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418361741 2500000000 23634838619873 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1769730037/10000000000 : ℝ)^1051 ≤ (253316589063/2500000000000 : ℝ)^795 := by
    have hnat : (1769730037 : ℕ)^1051*2500000000000^795 ≤ 253316589063^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769730037 10000000000 253316589063 2500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243956103/10000000000 : ℝ), (1418361741/2500000000 : ℝ), (-1769730037/10000000000 : ℝ)] ![(42597659190539/100000000000000 : ℝ), (23634838619873/50000000000000 : ℝ), (253316589063/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243956103/10000000000 : ℝ)|^1051 ≤ (42597659190539/100000000000000 : ℝ)^795
        have hw : |(5243956103/10000000000 : ℝ)|=(5243956103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1418361741/2500000000 : ℝ)|^1051 ≤ (23634838619873/50000000000000 : ℝ)^795
        have hw : |(1418361741/2500000000 : ℝ)|=(1418361741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1769730037/10000000000 : ℝ)|^1051 ≤ (253316589063/2500000000000 : ℝ)^795
        have hw : |(-1769730037/10000000000 : ℝ)|=(1769730037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s1_7 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (539077597/1250000000 : ℝ)*x 0 + (5015229109/10000000000 : ℝ)*x 1 + (3708699693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539077597/1250000000 : ℝ)^1051 ≤ (6578901152121/20000000000000 : ℝ)^795 := by
    have hnat : (539077597 : ℕ)^1051*20000000000000^795 ≤ 6578901152121^795*1250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539077597 1250000000 6578901152121 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5015229109/10000000000 : ℝ)^1051 ≤ (40158791766487/100000000000000 : ℝ)^795 := by
    have hnat : (5015229109 : ℕ)^1051*100000000000000^795 ≤ 40158791766487^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015229109 10000000000 40158791766487 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3708699693/10000000000 : ℝ)^1051 ≤ (2694670245681/10000000000000 : ℝ)^795 := by
    have hnat : (3708699693 : ℕ)^1051*10000000000000^795 ≤ 2694670245681^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3708699693 10000000000 2694670245681 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539077597/1250000000 : ℝ), (5015229109/10000000000 : ℝ), (3708699693/10000000000 : ℝ)] ![(6578901152121/20000000000000 : ℝ), (40158791766487/100000000000000 : ℝ), (2694670245681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539077597/1250000000 : ℝ)|^1051 ≤ (6578901152121/20000000000000 : ℝ)^795
        have hw : |(539077597/1250000000 : ℝ)|=(539077597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5015229109/10000000000 : ℝ)|^1051 ≤ (40158791766487/100000000000000 : ℝ)^795
        have hw : |(5015229109/10000000000 : ℝ)|=(5015229109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3708699693/10000000000 : ℝ)|^1051 ≤ (2694670245681/10000000000000 : ℝ)^795
        have hw : |(3708699693/10000000000 : ℝ)|=(3708699693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1215_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13769/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (189/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10057/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13769/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (71/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13769/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (71/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13769/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (71/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13769/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (71/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13769/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (71/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13769/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (71/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (71/10000 : ℝ) ^ (8407/2048 : ℝ) ≤ (7558358611/5000000000000000000 : ℝ) := by
    have hpowers : (71/10000 : ℝ)^8407 ≤ (7558358611/5000000000000000000 : ℝ)^2048 := by
      have hnat : (71 : ℕ)^8407*5000000000000000000^2048 ≤ 7558358611^2048*10000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71 10000 7558358611 5000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71/10000 : ℝ)) (X := (7558358611/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13769/50000 : ℝ) ^ (8407/2048 : ℝ) ≤ (251132793206429629/50000000000000000000 : ℝ) := by
    have hpowers : (13769/50000 : ℝ)^8407 ≤ (251132793206429629/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13769 : ℕ)^8407*50000000000000000000^2048 ≤ 251132793206429629^2048*50000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13769 50000 251132793206429629 50000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13769/50000 : ℝ)) (X := (251132793206429629/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500000007558358611/2500000000000000000 : ℝ) ≤ (5000000003682531/5000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (2500000007558358611/2500000000000000000 : ℝ)^2048 ≤ (5000000003682531/5000000000000000 : ℝ)^8407 := by
      have hnat : (2500000007558358611 : ℕ)^2048*5000000000000000^8407 ≤ 5000000003682531^8407*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500000007558358611 2500000000000000000 5000000003682531 5000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000003682531/5000000000000000 : ℝ)) (X := (2500000007558358611/2500000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50251132868790015739/50000000000000000000 : ℝ) ≤ (1251526543357107/1250000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50251132868790015739/50000000000000000000 : ℝ)^2048 ≤ (1251526543357107/1250000000000000 : ℝ)^8407 := by
      have hnat : (50251132868790015739 : ℕ)^2048*1250000000000000^8407 ≤ 1251526543357107^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50251132868790015739 50000000000000000000 1251526543357107 1250000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251526543357107/1250000000000000 : ℝ)) (X := (50251132868790015739/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25251132793206429629/25000000000000000000 : ℝ) ≤ (200488493726973/200000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (25251132793206429629/25000000000000000000 : ℝ)^2048 ≤ (200488493726973/200000000000000 : ℝ)^8407 := by
      have hnat : (25251132793206429629 : ℕ)^2048*200000000000000^8407 ≤ 200488493726973^8407*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25251132793206429629 25000000000000000000 200488493726973 200000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200488493726973/200000000000000 : ℝ)) (X := (25251132793206429629/25000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7558358611/5000000000000000000 : ℝ) ≤ ((16766416167219470991/16767500000000000000 : ℝ)+2*(6106169745897/1341400000000000 : ℝ)*(71/10000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (16766416167219470991/16767500000000000000 : ℝ)+2*(6106169745897/1341400000000000 : ℝ)*(71/10000 : ℝ)=(5000000003682531/5000000000000000 : ℝ) by norm_num, show 1+2*(7558358611/5000000000000000000 : ℝ)=(2500000007558358611/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(251132793206429629/50000000000000000000 : ℝ)+(7558358611/5000000000000000000 : ℝ) ≤ ((16766416167219470991/16767500000000000000 : ℝ)+(6106169745897/1341400000000000 : ℝ)*((13769/50000 : ℝ)+(71/10000 : ℝ)))^(8407/2048 : ℝ) := by
    rw [show (16766416167219470991/16767500000000000000 : ℝ)+(6106169745897/1341400000000000 : ℝ)*((13769/50000 : ℝ)+(71/10000 : ℝ))=(1251526543357107/1250000000000000 : ℝ) by norm_num, show 1+(251132793206429629/50000000000000000000 : ℝ)+(7558358611/5000000000000000000 : ℝ)=(50251132868790015739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(251132793206429629/50000000000000000000 : ℝ) ≤ ((16766416167219470991/16767500000000000000 : ℝ)+2*(6106169745897/1341400000000000 : ℝ)*(13769/50000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (16766416167219470991/16767500000000000000 : ℝ)+2*(6106169745897/1341400000000000 : ℝ)*(13769/50000 : ℝ)=(200488493726973/200000000000000 : ℝ) by norm_num, show 1+2*(251132793206429629/50000000000000000000 : ℝ)=(25251132793206429629/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16766416167219470991/16767500000000000000 : ℝ)*(X 1 0+X 2 0)+(6106169745897/1341400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (71/10000 : ℝ)) (hi := (13769/50000 : ℝ)) (c := (16766416167219470991/16767500000000000000 : ℝ)) (alpha := (6106169745897/1341400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16766416167219470991/16767500000000000000 : ℝ)*(X 0 1+X 2 1)+(6106169745897/1341400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (71/10000 : ℝ)) (hi := (13769/50000 : ℝ)) (c := (16766416167219470991/16767500000000000000 : ℝ)) (alpha := (6106169745897/1341400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16766416167219470991/16767500000000000000 : ℝ)*(X 0 2+X 1 2)+(6106169745897/1341400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (71/10000 : ℝ)) (hi := (13769/50000 : ℝ)) (c := (16766416167219470991/16767500000000000000 : ℝ)) (alpha := (6106169745897/1341400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-10341451/50000000 : ℝ)*X 0 0+(355153057/625000000 : ℝ)*X 0 1+(2508588453/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2707565131/5000000000 : ℝ)*X 1 0+(-242600019/1000000000 : ℝ)*X 1 1+(1254294359/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((541512891/1000000000 : ℝ)*X 2 0+(5017178301/10000000000 : ℝ)*X 2 1+(-1213000423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4311190047/10000000000 : ℝ)*X 0 0+(3690532797/10000000000 : ℝ)*X 0 1+(5033053149/10000000000 : ℝ)*X 0 2+(4311190047/10000000000 : ℝ)*X 1 0+(3690532797/10000000000 : ℝ)*X 1 1+(5033053149/10000000000 : ℝ)*X 1 2+(4311190047/10000000000 : ℝ)*X 2 0+(3690532797/10000000000 : ℝ)*X 2 1+(5033053149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-51724903/250000000 : ℝ)*X 0 0+(1256501823/2500000000 : ℝ)*X 0 1+(2836725517/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1310988987/2500000000 : ℝ)*X 1 0+(-884865449/5000000000 : ℝ)*X 1 1+(5673446523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5243956103/10000000000 : ℝ)*X 2 0+(1418361741/2500000000 : ℝ)*X 2 1+(-1769730037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((539077597/1250000000 : ℝ)*X 0 0+(5015229109/10000000000 : ℝ)*X 0 1+(3708699693/10000000000 : ℝ)*X 0 2+(539077597/1250000000 : ℝ)*X 1 0+(5015229109/10000000000 : ℝ)*X 1 1+(3708699693/10000000000 : ℝ)*X 1 2+(539077597/1250000000 : ℝ)*X 2 0+(5015229109/10000000000 : ℝ)*X 2 1+(3708699693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (274056912465275305043789883/41918750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (166837971/10000000000000 : ℝ)*(base19) + (62028209/5000000000000 : ℝ)*(base23) + (3667797/12500000000000 : ℝ)*(upper2) + (383253331/100000000000000 : ℝ)*(upper3) + (28891163/50000000000000 : ℝ)*(upper4) + (56201094920671/5000000000000 : ℝ)*(major0) + (56201094920671/5000000000000 : ℝ)*(major1) + (56201094920671/5000000000000 : ℝ)*(major2) + (1503156901834617/100000000000000 : ℝ)*(sp0) + (751581637443761/50000000000000 : ℝ)*(sp1) + (1503163702703053/100000000000000 : ℝ)*(sp2) + (148974478627197/20000000000000 : ℝ)*(sp3) + (1005179077/12500000000000 : ℝ)*(sp4) + (1248499309/20000000000000 : ℝ)*(sp7) + (74487863563253/10000000000000 : ℝ)*(f.failure) + (46973904477101/3125000000000 : ℝ)*(f.sum) + (37566602079009/6707000000000000000000000000 : ℝ)*base65 + (398877865700432539/83837500000000000000000000000000 : ℝ)*base68 + (520866154120307539/83837500000000000000000000000000 : ℝ)*base70 + (42761320739929961/83837500000000000000000000000000 : ℝ)*base71 + (3655082367471/1676750000000000000000000000 : ℝ)*base73 + (209687646583167461/83837500000000000000000000000000 : ℝ)*base75 + (159888292040845039/83837500000000000000000000000000 : ℝ)*base78 + (83634644932170039/83837500000000000000000000000000 : ℝ)*base80 + (669905836109/670700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (896747/200000000000000000000 : ℝ)*base90 + (896747/200000000000000000000 : ℝ)*base92 + (896747/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11173420918853754062315073/5515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (218331239/100000000000000 : ℝ)*(base19) + (95393847/100000000000000 : ℝ)*(base23) + (109956039/50000000000000 : ℝ)*(lower2) + (205304241/100000000000000 : ℝ)*(lower3) + (131503731/100000000000000 : ℝ)*(lower4) + (77615719/100000000000000 : ℝ)*(lower5) + (72185506462199/6250000000000 : ℝ)*(major0) + (72185506462199/6250000000000 : ℝ)*(major1) + (72185506462199/6250000000000 : ℝ)*(major2) + (604899621/10000000000000 : ℝ)*(sp0) + (193067962316847/12500000000000 : ℝ)*(sp4) + (1544549529199747/100000000000000 : ℝ)*(sp5) + (1544549652137139/100000000000000 : ℝ)*(sp6) + (765386391733509/100000000000000 : ℝ)*(sp7) + (765386391733509/100000000000000 : ℝ)*(f.failure) + (772274873765493/50000000000000 : ℝ)*(f.sum) + (323549722629/110312500000000000000000000 : ℝ)*base66 + (12321775255863557/2757812500000000000000000000000 : ℝ)*base68 + (28695111561832307/2757812500000000000000000000000 : ℝ)*base70 + (38293644341273989/5515625000000000000000000000000 : ℝ)*base72 + (9533272363479/1765000000000000000000000000 : ℝ)*base74 + (19409326218367739/5515625000000000000000000000000 : ℝ)*base76 + (2851636614644807/2757812500000000000000000000000 : ℝ)*base78 + (15832431639082307/2757812500000000000000000000000 : ℝ)*base80 + (5302082395257/882500000000000000000000000 : ℝ)*base82 + (13353509/2000000000000000000000 : ℝ)*base89 + (13353509/2000000000000000000000 : ℝ)*base91 + (13353509/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1215_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13769/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (189/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10057/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1215_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1215_s2_0 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058851347/5000000000 : ℝ)*x 0 + (2748729403/5000000000 : ℝ)*x 1 + (41365433/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058851347/5000000000 : ℝ)^1051 ≤ (3211626587497/25000000000000 : ℝ)^795 := by
    have hnat : (1058851347 : ℕ)^1051*25000000000000^795 ≤ 3211626587497^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058851347 5000000000 3211626587497 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748729403/5000000000 : ℝ)^1051 ≤ (22670488506411/50000000000000 : ℝ)^795 := by
    have hnat : (2748729403 : ℕ)^1051*50000000000000^795 ≤ 22670488506411^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748729403 5000000000 22670488506411 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41365433/80000000 : ℝ)^1051 ≤ (20906258314383/50000000000000 : ℝ)^795 := by
    have hnat : (41365433 : ℕ)^1051*50000000000000^795 ≤ 20906258314383^795*80000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41365433 80000000 20906258314383 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058851347/5000000000 : ℝ), (2748729403/5000000000 : ℝ), (41365433/80000000 : ℝ)] ![(3211626587497/25000000000000 : ℝ), (22670488506411/50000000000000 : ℝ), (20906258314383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058851347/5000000000 : ℝ)|^1051 ≤ (3211626587497/25000000000000 : ℝ)^795
        have hw : |(-1058851347/5000000000 : ℝ)|=(1058851347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748729403/5000000000 : ℝ)|^1051 ≤ (22670488506411/50000000000000 : ℝ)^795
        have hw : |(2748729403/5000000000 : ℝ)|=(2748729403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41365433/80000000 : ℝ)|^1051 ≤ (20906258314383/50000000000000 : ℝ)^795
        have hw : |(41365433/80000000 : ℝ)|=(41365433/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s2_1 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5370790319/10000000000 : ℝ)*x 0 + (-1143566867/5000000000 : ℝ)*x 1 + (5170679059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370790319/10000000000 : ℝ)^1051 ≤ (8793000480777/20000000000000 : ℝ)^795 := by
    have hnat : (5370790319 : ℕ)^1051*20000000000000^795 ≤ 8793000480777^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370790319 10000000000 8793000480777 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143566867/5000000000 : ℝ)^1051 ≤ (1422248166289/10000000000000 : ℝ)^795 := by
    have hnat : (1143566867 : ℕ)^1051*10000000000000^795 ≤ 1422248166289^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143566867 5000000000 1422248166289 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170679059/10000000000 : ℝ)^1051 ≤ (41812515923199/100000000000000 : ℝ)^795 := by
    have hnat : (5170679059 : ℕ)^1051*100000000000000^795 ≤ 41812515923199^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170679059 10000000000 41812515923199 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370790319/10000000000 : ℝ), (-1143566867/5000000000 : ℝ), (5170679059/10000000000 : ℝ)] ![(8793000480777/20000000000000 : ℝ), (1422248166289/10000000000000 : ℝ), (41812515923199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370790319/10000000000 : ℝ)|^1051 ≤ (8793000480777/20000000000000 : ℝ)^795
        have hw : |(5370790319/10000000000 : ℝ)|=(5370790319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1143566867/5000000000 : ℝ)|^1051 ≤ (1422248166289/10000000000000 : ℝ)^795
        have hw : |(-1143566867/5000000000 : ℝ)|=(1143566867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170679059/10000000000 : ℝ)|^1051 ≤ (41812515923199/100000000000000 : ℝ)^795
        have hw : |(5170679059/10000000000 : ℝ)|=(5170679059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s2_2 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2685395059/5000000000 : ℝ)*x 0 + (5170679237/10000000000 : ℝ)*x 1 + (-1143566883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685395059/5000000000 : ℝ)^1051 ≤ (21982500114339/50000000000000 : ℝ)^795 := by
    have hnat : (2685395059 : ℕ)^1051*50000000000000^795 ≤ 21982500114339^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685395059 5000000000 21982500114339 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5170679237/10000000000 : ℝ)^1051 ≤ (10453129456523/25000000000000 : ℝ)^795 := by
    have hnat : (5170679237 : ℕ)^1051*25000000000000^795 ≤ 10453129456523^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170679237 10000000000 10453129456523 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143566883/5000000000 : ℝ)^1051 ≤ (7111240962979/50000000000000 : ℝ)^795 := by
    have hnat : (1143566883 : ℕ)^1051*50000000000000^795 ≤ 7111240962979^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143566883 5000000000 7111240962979 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685395059/5000000000 : ℝ), (5170679237/10000000000 : ℝ), (-1143566883/5000000000 : ℝ)] ![(21982500114339/50000000000000 : ℝ), (10453129456523/25000000000000 : ℝ), (7111240962979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685395059/5000000000 : ℝ)|^1051 ≤ (21982500114339/50000000000000 : ℝ)^795
        have hw : |(2685395059/5000000000 : ℝ)|=(2685395059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5170679237/10000000000 : ℝ)|^1051 ≤ (10453129456523/25000000000000 : ℝ)^795
        have hw : |(5170679237/10000000000 : ℝ)|=(5170679237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1143566883/5000000000 : ℝ)|^1051 ≤ (7111240962979/50000000000000 : ℝ)^795
        have hw : |(-1143566883/5000000000 : ℝ)|=(1143566883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s2_3 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4345260687/10000000000 : ℝ)*x 0 + (4027730747/10000000000 : ℝ)*x 1 + (2343586229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345260687/10000000000 : ℝ)^1051 ≤ (33224035521221/100000000000000 : ℝ)^795 := by
    have hnat : (4345260687 : ℕ)^1051*100000000000000^795 ≤ 33224035521221^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345260687 10000000000 33224035521221 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4027730747/10000000000 : ℝ)^1051 ≤ (6010559722809/20000000000000 : ℝ)^795 := by
    have hnat : (4027730747 : ℕ)^1051*20000000000000^795 ≤ 6010559722809^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027730747 10000000000 6010559722809 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2343586229/5000000000 : ℝ)^1051 ≤ (18361582925491/50000000000000 : ℝ)^795 := by
    have hnat : (2343586229 : ℕ)^1051*50000000000000^795 ≤ 18361582925491^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2343586229 5000000000 18361582925491 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345260687/10000000000 : ℝ), (4027730747/10000000000 : ℝ), (2343586229/5000000000 : ℝ)] ![(33224035521221/100000000000000 : ℝ), (6010559722809/20000000000000 : ℝ), (18361582925491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345260687/10000000000 : ℝ)|^1051 ≤ (33224035521221/100000000000000 : ℝ)^795
        have hw : |(4345260687/10000000000 : ℝ)|=(4345260687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4027730747/10000000000 : ℝ)|^1051 ≤ (6010559722809/20000000000000 : ℝ)^795
        have hw : |(4027730747/10000000000 : ℝ)|=(4027730747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2343586229/5000000000 : ℝ)|^1051 ≤ (18361582925491/50000000000000 : ℝ)^795
        have hw : |(2343586229/5000000000 : ℝ)|=(2343586229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s2_4 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-423557387/2000000000 : ℝ)*x 0 + (2586409799/5000000000 : ℝ)*x 1 + (5495297919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423557387/2000000000 : ℝ)^1051 ≤ (12847181937991/100000000000000 : ℝ)^795 := by
    have hnat : (423557387 : ℕ)^1051*100000000000000^795 ≤ 12847181937991^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423557387 2000000000 12847181937991 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586409799/5000000000 : ℝ)^1051 ≤ (41835400684869/100000000000000 : ℝ)^795 := by
    have hnat : (2586409799 : ℕ)^1051*100000000000000^795 ≤ 41835400684869^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586409799 5000000000 41835400684869 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495297919/10000000000 : ℝ)^1051 ≤ (22658708675667/50000000000000 : ℝ)^795 := by
    have hnat : (5495297919 : ℕ)^1051*50000000000000^795 ≤ 22658708675667^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495297919 10000000000 22658708675667 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423557387/2000000000 : ℝ), (2586409799/5000000000 : ℝ), (5495297919/10000000000 : ℝ)] ![(12847181937991/100000000000000 : ℝ), (41835400684869/100000000000000 : ℝ), (22658708675667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423557387/2000000000 : ℝ)|^1051 ≤ (12847181937991/100000000000000 : ℝ)^795
        have hw : |(-423557387/2000000000 : ℝ)|=(423557387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586409799/5000000000 : ℝ)|^1051 ≤ (41835400684869/100000000000000 : ℝ)^795
        have hw : |(2586409799/5000000000 : ℝ)|=(2586409799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495297919/10000000000 : ℝ)|^1051 ≤ (22658708675667/50000000000000 : ℝ)^795
        have hw : |(5495297919/10000000000 : ℝ)|=(5495297919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s2_5 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5287480979/10000000000 : ℝ)*x 0 + (-981257363/5000000000 : ℝ)*x 1 + (5495297951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287480979/10000000000 : ℝ)^1051 ≤ (43065694606321/100000000000000 : ℝ)^795 := by
    have hnat : (5287480979 : ℕ)^1051*100000000000000^795 ≤ 43065694606321^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287480979 10000000000 43065694606321 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981257363/5000000000 : ℝ)^1051 ≤ (1161688768159/10000000000000 : ℝ)^795 := by
    have hnat : (981257363 : ℕ)^1051*10000000000000^795 ≤ 1161688768159^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981257363 5000000000 1161688768159 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495297951/10000000000 : ℝ)^1051 ≤ (226587088501/500000000000 : ℝ)^795 := by
    have hnat : (5495297951 : ℕ)^1051*500000000000^795 ≤ 226587088501^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495297951 10000000000 226587088501 500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287480979/10000000000 : ℝ), (-981257363/5000000000 : ℝ), (5495297951/10000000000 : ℝ)] ![(43065694606321/100000000000000 : ℝ), (1161688768159/10000000000000 : ℝ), (226587088501/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287480979/10000000000 : ℝ)|^1051 ≤ (43065694606321/100000000000000 : ℝ)^795
        have hw : |(5287480979/10000000000 : ℝ)|=(5287480979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-981257363/5000000000 : ℝ)|^1051 ≤ (1161688768159/10000000000000 : ℝ)^795
        have hw : |(-981257363/5000000000 : ℝ)|=(981257363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495297951/10000000000 : ℝ)|^1051 ≤ (226587088501/500000000000 : ℝ)^795
        have hw : |(5495297951/10000000000 : ℝ)|=(5495297951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s2_6 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (132187029/250000000 : ℝ)*x 0 + (5495297989/10000000000 : ℝ)*x 1 + (-245314303/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132187029/250000000 : ℝ)^1051 ≤ (21532848277627/50000000000000 : ℝ)^795 := by
    have hnat : (132187029 : ℕ)^1051*50000000000000^795 ≤ 21532848277627^795*250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132187029 250000000 21532848277627 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5495297989/10000000000 : ℝ)^1051 ≤ (566467726431/1250000000000 : ℝ)^795 := by
    have hnat : (5495297989 : ℕ)^1051*1250000000000^795 ≤ 566467726431^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495297989 10000000000 566467726431 1250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245314303/1250000000 : ℝ)^1051 ≤ (726055332393/6250000000000 : ℝ)^795 := by
    have hnat : (245314303 : ℕ)^1051*6250000000000^795 ≤ 726055332393^795*1250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245314303 1250000000 726055332393 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132187029/250000000 : ℝ), (5495297989/10000000000 : ℝ), (-245314303/1250000000 : ℝ)] ![(21532848277627/50000000000000 : ℝ), (566467726431/1250000000000 : ℝ), (726055332393/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132187029/250000000 : ℝ)|^1051 ≤ (21532848277627/50000000000000 : ℝ)^795
        have hw : |(132187029/250000000 : ℝ)|=(132187029/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5495297989/10000000000 : ℝ)|^1051 ≤ (566467726431/1250000000000 : ℝ)^795
        have hw : |(5495297989/10000000000 : ℝ)|=(5495297989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245314303/1250000000 : ℝ)|^1051 ≤ (726055332393/6250000000000 : ℝ)^795
        have hw : |(-245314303/1250000000 : ℝ)|=(245314303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s2_7 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2172715091/5000000000 : ℝ)*x 0 + (1170713273/2500000000 : ℝ)*x 1 + (50401139/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172715091/5000000000 : ℝ)^1051 ≤ (33225748814661/100000000000000 : ℝ)^795 := by
    have hnat : (2172715091 : ℕ)^1051*100000000000000^795 ≤ 33225748814661^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172715091 5000000000 33225748814661 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1170713273/2500000000 : ℝ)^1051 ≤ (916960841119/2500000000000 : ℝ)^795 := by
    have hnat : (1170713273 : ℕ)^1051*2500000000000^795 ≤ 916960841119^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170713273 2500000000 916960841119 2500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50401139/125000000 : ℝ)^1051 ≤ (15047908761611/50000000000000 : ℝ)^795 := by
    have hnat : (50401139 : ℕ)^1051*50000000000000^795 ≤ 15047908761611^795*125000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50401139 125000000 15047908761611 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2172715091/5000000000 : ℝ), (1170713273/2500000000 : ℝ), (50401139/125000000 : ℝ)] ![(33225748814661/100000000000000 : ℝ), (916960841119/2500000000000 : ℝ), (15047908761611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2172715091/5000000000 : ℝ)|^1051 ≤ (33225748814661/100000000000000 : ℝ)^795
        have hw : |(2172715091/5000000000 : ℝ)|=(2172715091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1170713273/2500000000 : ℝ)|^1051 ≤ (916960841119/2500000000000 : ℝ)^795
        have hw : |(1170713273/2500000000 : ℝ)|=(1170713273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50401139/125000000 : ℝ)|^1051 ≤ (15047908761611/50000000000000 : ℝ)^795
        have hw : |(50401139/125000000 : ℝ)|=(50401139/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1215_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2347/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3259/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (189/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (189/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (189/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (189/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (189/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (189/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (189/3125 : ℝ) ^ (8407/2048 : ℝ) ≤ (996644246050449/100000000000000000000 : ℝ) := by
    have hpowers : (189/3125 : ℝ)^8407 ≤ (996644246050449/100000000000000000000 : ℝ)^2048 := by
      have hnat : (189 : ℕ)^8407*100000000000000000000^2048 ≤ 996644246050449^2048*3125^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        189 3125 996644246050449 100000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (189/3125 : ℝ)) (X := (996644246050449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10057/50000 : ℝ) ^ (8407/2048 : ℝ) ≤ (138316733332058413/100000000000000000000 : ℝ) := by
    have hpowers : (10057/50000 : ℝ)^8407 ≤ (138316733332058413/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10057 : ℕ)^8407*100000000000000000000^2048 ≤ 138316733332058413^2048*50000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10057 50000 138316733332058413 100000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10057/50000 : ℝ)) (X := (138316733332058413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000996644246050449/50000000000000000000 : ℝ) ≤ (10000048557440917/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50000996644246050449/50000000000000000000 : ℝ)^2048 ≤ (10000048557440917/10000000000000000 : ℝ)^8407 := by
      have hnat : (50000996644246050449 : ℕ)^2048*10000000000000000^8407 ≤ 10000048557440917^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000996644246050449 50000000000000000000 10000048557440917 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000048557440917/10000000000000000 : ℝ)) (X := (50000996644246050449/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50069656688789054431/50000000000000000000 : ℝ) ≤ (2000678395608477/2000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50069656688789054431/50000000000000000000 : ℝ)^2048 ≤ (2000678395608477/2000000000000000 : ℝ)^8407 := by
      have hnat : (50069656688789054431 : ℕ)^2048*2000000000000000^8407 ≤ 2000678395608477^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50069656688789054431 50000000000000000000 2000678395608477 2000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000678395608477/2000000000000000 : ℝ)) (X := (50069656688789054431/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50138316733332058413/50000000000000000000 : ℝ) ≤ (10006735398643853/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50138316733332058413/50000000000000000000 : ℝ)^2048 ≤ (10006735398643853/10000000000000000 : ℝ)^8407 := by
      have hnat : (50138316733332058413 : ℕ)^2048*10000000000000000^8407 ≤ 10006735398643853^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50138316733332058413 50000000000000000000 10006735398643853 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006735398643853/10000000000000000 : ℝ)) (X := (50138316733332058413/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(996644246050449/100000000000000000000 : ℝ) ≤ ((70310120496684290797/70330000000000000000 : ℝ)+2*(835855150367/351650000000000 : ℝ)*(189/3125 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (70310120496684290797/70330000000000000000 : ℝ)+2*(835855150367/351650000000000 : ℝ)*(189/3125 : ℝ)=(10000048557440917/10000000000000000 : ℝ) by norm_num, show 1+2*(996644246050449/100000000000000000000 : ℝ)=(50000996644246050449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(138316733332058413/100000000000000000000 : ℝ)+(996644246050449/100000000000000000000 : ℝ) ≤ ((70310120496684290797/70330000000000000000 : ℝ)+(835855150367/351650000000000 : ℝ)*((10057/50000 : ℝ)+(189/3125 : ℝ)))^(8407/2048 : ℝ) := by
    rw [show (70310120496684290797/70330000000000000000 : ℝ)+(835855150367/351650000000000 : ℝ)*((10057/50000 : ℝ)+(189/3125 : ℝ))=(2000678395608477/2000000000000000 : ℝ) by norm_num, show 1+(138316733332058413/100000000000000000000 : ℝ)+(996644246050449/100000000000000000000 : ℝ)=(50069656688789054431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(138316733332058413/100000000000000000000 : ℝ) ≤ ((70310120496684290797/70330000000000000000 : ℝ)+2*(835855150367/351650000000000 : ℝ)*(10057/50000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (70310120496684290797/70330000000000000000 : ℝ)+2*(835855150367/351650000000000 : ℝ)*(10057/50000 : ℝ)=(10006735398643853/10000000000000000 : ℝ) by norm_num, show 1+2*(138316733332058413/100000000000000000000 : ℝ)=(50138316733332058413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70310120496684290797/70330000000000000000 : ℝ)*(X 1 0+X 2 0)+(835855150367/351650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (189/3125 : ℝ)) (hi := (10057/50000 : ℝ)) (c := (70310120496684290797/70330000000000000000 : ℝ)) (alpha := (835855150367/351650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70310120496684290797/70330000000000000000 : ℝ)*(X 0 1+X 2 1)+(835855150367/351650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (189/3125 : ℝ)) (hi := (10057/50000 : ℝ)) (c := (70310120496684290797/70330000000000000000 : ℝ)) (alpha := (835855150367/351650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70310120496684290797/70330000000000000000 : ℝ)*(X 0 2+X 1 2)+(835855150367/351650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (189/3125 : ℝ)) (hi := (10057/50000 : ℝ)) (c := (70310120496684290797/70330000000000000000 : ℝ)) (alpha := (835855150367/351650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1058851347/5000000000 : ℝ)*X 0 0+(2748729403/5000000000 : ℝ)*X 0 1+(41365433/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370790319/10000000000 : ℝ)*X 1 0+(-1143566867/5000000000 : ℝ)*X 1 1+(5170679059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685395059/5000000000 : ℝ)*X 2 0+(5170679237/10000000000 : ℝ)*X 2 1+(-1143566883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4345260687/10000000000 : ℝ)*X 0 0+(4027730747/10000000000 : ℝ)*X 0 1+(2343586229/5000000000 : ℝ)*X 0 2+(4345260687/10000000000 : ℝ)*X 1 0+(4027730747/10000000000 : ℝ)*X 1 1+(2343586229/5000000000 : ℝ)*X 1 2+(4345260687/10000000000 : ℝ)*X 2 0+(4027730747/10000000000 : ℝ)*X 2 1+(2343586229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-423557387/2000000000 : ℝ)*X 0 0+(2586409799/5000000000 : ℝ)*X 0 1+(5495297919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287480979/10000000000 : ℝ)*X 1 0+(-981257363/5000000000 : ℝ)*X 1 1+(5495297951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132187029/250000000 : ℝ)*X 2 0+(5495297989/10000000000 : ℝ)*X 2 1+(-245314303/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2172715091/5000000000 : ℝ)*X 0 0+(1170713273/2500000000 : ℝ)*X 0 1+(50401139/125000000 : ℝ)*X 0 2+(2172715091/5000000000 : ℝ)*X 1 0+(1170713273/2500000000 : ℝ)*X 1 1+(50401139/125000000 : ℝ)*X 1 2+(2172715091/5000000000 : ℝ)*X 2 0+(1170713273/2500000000 : ℝ)*X 2 1+(50401139/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10205139829993086685181306487/1758250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (588390469/50000000000000 : ℝ)*(base19) + (489184909/50000000000000 : ℝ)*(base23) + (2252633/5000000000000 : ℝ)*(lower2) + (6130663/3125000000000 : ℝ)*(upper3) + (78770363/100000000000000 : ℝ)*(upper5) + (1144159169007419/50000000000000 : ℝ)*(major0) + (1144159169007419/50000000000000 : ℝ)*(major1) + (1144159169007419/50000000000000 : ℝ)*(major2) + (765044703539819/25000000000000 : ℝ)*(sp0) + (3060188478611851/100000000000000 : ℝ)*(sp1) + (765047169255743/25000000000000 : ℝ)*(sp2) + (94777501537977/6250000000000 : ℝ)*(sp3) + (5420616757/50000000000000 : ℝ)*(sp4) + (6802557707/100000000000000 : ℝ)*(sp7) + (75822341358267/5000000000000 : ℝ)*(f.failure) + (306018965539279/10000000000000 : ℝ)*(f.sum) + (6340637257551/1098906250000000000000000000 : ℝ)*base65 + (49210817377102977057/3516500000000000000000000000000000 : ℝ)*base68 + (36987460514671977057/3516500000000000000000000000000000 : ℝ)*base70 + (24353077475894477057/3516500000000000000000000000000000 : ℝ)*base72 + (22755975990641/17582500000000000000000000000 : ℝ)*base73 + (21653260611331477057/3516500000000000000000000000000000 : ℝ)*base76 + (37600155754139977057/3516500000000000000000000000000000 : ℝ)*base78 + (25460518921946977057/3516500000000000000000000000000000 : ℝ)*base80 + (53628478527083/8791250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1418267/100000000000000000000 : ℝ)*base89 + (1418267/100000000000000000000 : ℝ)*base91 + (1418267/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (880448444990912367582301431/135250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1658098083/100000000000000 : ℝ)*(base19) + (75780507/4000000000000 : ℝ)*(base23) + (27281583/100000000000000 : ℝ)*(upper2) + (1769753/800000000000 : ℝ)*(upper3) + (13194689/10000000000000 : ℝ)*(upper5) + (2318821826683267/100000000000000 : ℝ)*(major0) + (2318821826683267/100000000000000 : ℝ)*(major1) + (2318821826683267/100000000000000 : ℝ)*(major2) + (3300040843/20000000000000 : ℝ)*(sp1) + (10746536433/50000000000000 : ℝ)*(sp2) + (775245559250777/25000000000000 : ℝ)*(sp4) + (310096407870081/10000000000000 : ℝ)*(sp5) + (96904964044299/3125000000000 : ℝ)*(sp6) + (1536661199370581/100000000000000 : ℝ)*(sp7) + (1536661199370581/100000000000000 : ℝ)*(f.failure) + (775245559250777/25000000000000 : ℝ)*(f.sum) + (41440641961/1098906250000000000000000000 : ℝ)*base66 + (49822039528251793799/7033000000000000000000000000000000 : ℝ)*base67 + (39874030270363793799/7033000000000000000000000000000000 : ℝ)*base69 + (7874651473978793799/7033000000000000000000000000000000 : ℝ)*base71 + (28700805941737/8791250000000000000000000000 : ℝ)*base73 + (15468523391844793799/7033000000000000000000000000000000 : ℝ)*base75 + (3740165329709793799/7033000000000000000000000000000000 : ℝ)*base77 + (55368033574278206201/7033000000000000000000000000000000 : ℝ)*base80 + (92350752410099/17582500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6049419/2000000000000000000000 : ℝ)*base90 + (6049419/2000000000000000000000 : ℝ)*base92 + (6049419/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1215_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2347/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1215_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1215_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2347/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1215_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1215_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1215_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2347/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1215_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
