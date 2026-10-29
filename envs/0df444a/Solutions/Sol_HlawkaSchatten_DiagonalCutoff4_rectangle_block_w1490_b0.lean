-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1490_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:15:40.10461+00:00
-- url     : https://prove2.me/submissions/28a4a262-cf68-40cf-9fe3-a40920d8fecd

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
theorem support_rectangle_w1490_s0_0 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-854709043/5000000000 : ℝ)*x 0 + (5929969623/10000000000 : ℝ)*x 1 + (4845795149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854709043/5000000000 : ℝ)^4477 ≤ (10123870971533/100000000000000 : ℝ)^3453 := by
    have hnat : (854709043 : ℕ)^4477*100000000000000^3453 ≤ 10123870971533^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854709043 5000000000 10123870971533 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5929969623/10000000000 : ℝ)^4477 ≤ (50786739682909/100000000000000 : ℝ)^3453 := by
    have hnat : (5929969623 : ℕ)^4477*100000000000000^3453 ≤ 50786739682909^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5929969623 10000000000 50786739682909 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4845795149/10000000000 : ℝ)^4477 ≤ (9772347332869/25000000000000 : ℝ)^3453 := by
    have hnat : (4845795149 : ℕ)^4477*25000000000000^3453 ≤ 9772347332869^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4845795149 10000000000 9772347332869 25000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-854709043/5000000000 : ℝ), (5929969623/10000000000 : ℝ), (4845795149/10000000000 : ℝ)] ![(10123870971533/100000000000000 : ℝ), (50786739682909/100000000000000 : ℝ), (9772347332869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-854709043/5000000000 : ℝ)|^4477 ≤ (10123870971533/100000000000000 : ℝ)^3453
        have hw : |(-854709043/5000000000 : ℝ)|=(854709043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5929969623/10000000000 : ℝ)|^4477 ≤ (50786739682909/100000000000000 : ℝ)^3453
        have hw : |(5929969623/10000000000 : ℝ)|=(5929969623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4845795149/10000000000 : ℝ)|^4477 ≤ (9772347332869/25000000000000 : ℝ)^3453
        have hw : |(4845795149/10000000000 : ℝ)|=(4845795149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s0_1 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2741391509/5000000000 : ℝ)*x 0 + (-2318864697/10000000000 : ℝ)*x 1 + (2422897581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2741391509/5000000000 : ℝ)^4477 ≤ (1433675532059/3125000000000 : ℝ)^3453 := by
    have hnat : (2741391509 : ℕ)^4477*3125000000000^3453 ≤ 1433675532059^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741391509 5000000000 1433675532059 3125000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2318864697/10000000000 : ℝ)^4477 ≤ (15032993484313/100000000000000 : ℝ)^3453 := by
    have hnat : (2318864697 : ℕ)^4477*100000000000000^3453 ≤ 15032993484313^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2318864697 10000000000 15032993484313 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2422897581/5000000000 : ℝ)^4477 ≤ (39089389467441/100000000000000 : ℝ)^3453 := by
    have hnat : (2422897581 : ℕ)^4477*100000000000000^3453 ≤ 39089389467441^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422897581 5000000000 39089389467441 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2741391509/5000000000 : ℝ), (-2318864697/10000000000 : ℝ), (2422897581/5000000000 : ℝ)] ![(1433675532059/3125000000000 : ℝ), (15032993484313/100000000000000 : ℝ), (39089389467441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2741391509/5000000000 : ℝ)|^4477 ≤ (1433675532059/3125000000000 : ℝ)^3453
        have hw : |(2741391509/5000000000 : ℝ)|=(2741391509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2318864697/10000000000 : ℝ)|^4477 ≤ (15032993484313/100000000000000 : ℝ)^3453
        have hw : |(-2318864697/10000000000 : ℝ)|=(2318864697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2422897581/5000000000 : ℝ)|^4477 ≤ (39089389467441/100000000000000 : ℝ)^3453
        have hw : |(2422897581/5000000000 : ℝ)|=(2422897581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s0_2 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5482783011/10000000000 : ℝ)*x 0 + (2422897599/5000000000 : ℝ)*x 1 + (-1159432331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5482783011/10000000000 : ℝ)^4477 ≤ (9175523389989/20000000000000 : ℝ)^3453 := by
    have hnat : (5482783011 : ℕ)^4477*20000000000000^3453 ≤ 9175523389989^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482783011 10000000000 9175523389989 20000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2422897599/5000000000 : ℝ)^4477 ≤ (977234746099/2500000000000 : ℝ)^3453 := by
    have hnat : (2422897599 : ℕ)^4477*2500000000000^3453 ≤ 977234746099^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422897599 5000000000 977234746099 2500000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1159432331/5000000000 : ℝ)^4477 ≤ (15032993190123/100000000000000 : ℝ)^3453 := by
    have hnat : (1159432331 : ℕ)^4477*100000000000000^3453 ≤ 15032993190123^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159432331 5000000000 15032993190123 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5482783011/10000000000 : ℝ), (2422897599/5000000000 : ℝ), (-1159432331/5000000000 : ℝ)] ![(9175523389989/20000000000000 : ℝ), (977234746099/2500000000000 : ℝ), (15032993190123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5482783011/10000000000 : ℝ)|^4477 ≤ (9175523389989/20000000000000 : ℝ)^3453
        have hw : |(5482783011/10000000000 : ℝ)|=(5482783011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2422897599/5000000000 : ℝ)|^4477 ≤ (977234746099/2500000000000 : ℝ)^3453
        have hw : |(2422897599/5000000000 : ℝ)|=(2422897599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1159432331/5000000000 : ℝ)|^4477 ≤ (15032993190123/100000000000000 : ℝ)^3453
        have hw : |(-1159432331/5000000000 : ℝ)|=(1159432331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s0_3 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (415112957/1000000000 : ℝ)*x 0 + (618262139/2000000000 : ℝ)*x 1 + (5511705131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415112957/1000000000 : ℝ)^4477 ≤ (6396789758369/20000000000000 : ℝ)^3453 := by
    have hnat : (415112957 : ℕ)^4477*20000000000000^3453 ≤ 6396789758369^3453*1000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415112957 1000000000 6396789758369 20000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618262139/2000000000 : ℝ)^4477 ≤ (21824412610923/100000000000000 : ℝ)^3453 := by
    have hnat : (618262139 : ℕ)^4477*100000000000000^3453 ≤ 21824412610923^3453*2000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618262139 2000000000 21824412610923 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5511705131/10000000000 : ℝ)^4477 ≤ (46191638587319/100000000000000 : ℝ)^3453 := by
    have hnat : (5511705131 : ℕ)^4477*100000000000000^3453 ≤ 46191638587319^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511705131 10000000000 46191638587319 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(415112957/1000000000 : ℝ), (618262139/2000000000 : ℝ), (5511705131/10000000000 : ℝ)] ![(6396789758369/20000000000000 : ℝ), (21824412610923/100000000000000 : ℝ), (46191638587319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(415112957/1000000000 : ℝ)|^4477 ≤ (6396789758369/20000000000000 : ℝ)^3453
        have hw : |(415112957/1000000000 : ℝ)|=(415112957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(618262139/2000000000 : ℝ)|^4477 ≤ (21824412610923/100000000000000 : ℝ)^3453
        have hw : |(618262139/2000000000 : ℝ)|=(618262139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5511705131/10000000000 : ℝ)|^4477 ≤ (46191638587319/100000000000000 : ℝ)^3453
        have hw : |(5511705131/10000000000 : ℝ)|=(5511705131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s0_4 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-214141379/1250000000 : ℝ)*x 0 + (2436780529/5000000000 : ℝ)*x 1 + (5901206167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214141379/1250000000 : ℝ)^4477 ≤ (5076195410647/50000000000000 : ℝ)^3453 := by
    have hnat : (214141379 : ℕ)^4477*50000000000000^3453 ≤ 5076195410647^3453*1250000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214141379 1250000000 5076195410647 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2436780529/5000000000 : ℝ)^4477 ≤ (7876007096711/20000000000000 : ℝ)^3453 := by
    have hnat : (2436780529 : ℕ)^4477*20000000000000^3453 ≤ 7876007096711^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436780529 5000000000 7876007096711 20000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5901206167/10000000000 : ℝ)^4477 ≤ (5046757367953/10000000000000 : ℝ)^3453 := by
    have hnat : (5901206167 : ℕ)^4477*10000000000000^3453 ≤ 5046757367953^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5901206167 10000000000 5046757367953 10000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214141379/1250000000 : ℝ), (2436780529/5000000000 : ℝ), (5901206167/10000000000 : ℝ)] ![(5076195410647/50000000000000 : ℝ), (7876007096711/20000000000000 : ℝ), (5046757367953/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214141379/1250000000 : ℝ)|^4477 ≤ (5076195410647/50000000000000 : ℝ)^3453
        have hw : |(-214141379/1250000000 : ℝ)|=(214141379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2436780529/5000000000 : ℝ)|^4477 ≤ (7876007096711/20000000000000 : ℝ)^3453
        have hw : |(2436780529/5000000000 : ℝ)|=(2436780529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5901206167/10000000000 : ℝ)|^4477 ≤ (5046757367953/10000000000000 : ℝ)^3453
        have hw : |(5901206167/10000000000 : ℝ)|=(5901206167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s0_5 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103733819/200000000 : ℝ)*x 0 + (-126345407/1000000000 : ℝ)*x 1 + (147530149/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103733819/200000000 : ℝ)^4477 ≤ (10672841466473/25000000000000 : ℝ)^3453 := by
    have hnat : (103733819 : ℕ)^4477*25000000000000^3453 ≤ 10672841466473^3453*200000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103733819 200000000 10672841466473 25000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126345407/1000000000 : ℝ)^4477 ≤ (6841062730447/100000000000000 : ℝ)^3453 := by
    have hnat : (126345407 : ℕ)^4477*100000000000000^3453 ≤ 6841062730447^3453*1000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126345407 1000000000 6841062730447 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147530149/250000000 : ℝ)^4477 ≤ (50467571384267/100000000000000 : ℝ)^3453 := by
    have hnat : (147530149 : ℕ)^4477*100000000000000^3453 ≤ 50467571384267^3453*250000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147530149 250000000 50467571384267 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103733819/200000000 : ℝ), (-126345407/1000000000 : ℝ), (147530149/250000000 : ℝ)] ![(10672841466473/25000000000000 : ℝ), (6841062730447/100000000000000 : ℝ), (50467571384267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103733819/200000000 : ℝ)|^4477 ≤ (10672841466473/25000000000000 : ℝ)^3453
        have hw : |(103733819/200000000 : ℝ)|=(103733819/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-126345407/1000000000 : ℝ)|^4477 ≤ (6841062730447/100000000000000 : ℝ)^3453
        have hw : |(-126345407/1000000000 : ℝ)|=(126345407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147530149/250000000 : ℝ)|^4477 ≤ (50467571384267/100000000000000 : ℝ)^3453
        have hw : |(147530149/250000000 : ℝ)|=(147530149/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s0_6 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5186690991/10000000000 : ℝ)*x 0 + (5901206041/10000000000 : ℝ)*x 1 + (-31586347/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5186690991/10000000000 : ℝ)^4477 ≤ (21345683151719/50000000000000 : ℝ)^3453 := by
    have hnat : (5186690991 : ℕ)^4477*50000000000000^3453 ≤ 21345683151719^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186690991 10000000000 21345683151719 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5901206041/10000000000 : ℝ)^4477 ≤ (50467572282413/100000000000000 : ℝ)^3453 := by
    have hnat : (5901206041 : ℕ)^4477*100000000000000^3453 ≤ 50467572282413^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5901206041 10000000000 50467572282413 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31586347/250000000 : ℝ)^4477 ≤ (6841061396593/100000000000000 : ℝ)^3453 := by
    have hnat : (31586347 : ℕ)^4477*100000000000000^3453 ≤ 6841061396593^3453*250000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31586347 250000000 6841061396593 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5186690991/10000000000 : ℝ), (5901206041/10000000000 : ℝ), (-31586347/250000000 : ℝ)] ![(21345683151719/50000000000000 : ℝ), (50467572282413/100000000000000 : ℝ), (6841061396593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5186690991/10000000000 : ℝ)|^4477 ≤ (21345683151719/50000000000000 : ℝ)^3453
        have hw : |(5186690991/10000000000 : ℝ)|=(5186690991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5901206041/10000000000 : ℝ)|^4477 ≤ (50467572282413/100000000000000 : ℝ)^3453
        have hw : |(5901206041/10000000000 : ℝ)|=(5901206041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31586347/250000000 : ℝ)|^4477 ≤ (6841061396593/100000000000000 : ℝ)^3453
        have hw : |(-31586347/250000000 : ℝ)|=(31586347/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s0_7 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4159418503/10000000000 : ℝ)*x 0 + (340607403/625000000 : ℝ)*x 1 + (3155524721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4159418503/10000000000 : ℝ)^4477 ≤ (32066777987337/100000000000000 : ℝ)^3453 := by
    have hnat : (4159418503 : ℕ)^4477*100000000000000^3453 ≤ 32066777987337^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159418503 10000000000 32066777987337 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340607403/625000000 : ℝ)^4477 ≤ (9103844046303/20000000000000 : ℝ)^3453 := by
    have hnat : (340607403 : ℕ)^4477*20000000000000^3453 ≤ 9103844046303^3453*625000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340607403 625000000 9103844046303 20000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3155524721/10000000000 : ℝ)^4477 ≤ (11207000882687/50000000000000 : ℝ)^3453 := by
    have hnat : (3155524721 : ℕ)^4477*50000000000000^3453 ≤ 11207000882687^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3155524721 10000000000 11207000882687 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4159418503/10000000000 : ℝ), (340607403/625000000 : ℝ), (3155524721/10000000000 : ℝ)] ![(32066777987337/100000000000000 : ℝ), (9103844046303/20000000000000 : ℝ), (11207000882687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4159418503/10000000000 : ℝ)|^4477 ≤ (32066777987337/100000000000000 : ℝ)^3453
        have hw : |(4159418503/10000000000 : ℝ)|=(4159418503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340607403/625000000 : ℝ)|^4477 ≤ (9103844046303/20000000000000 : ℝ)^3453
        have hw : |(340607403/625000000 : ℝ)|=(340607403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3155524721/10000000000 : ℝ)|^4477 ≤ (11207000882687/50000000000000 : ℝ)^3453
        have hw : |(3155524721/10000000000 : ℝ)|=(3155524721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1490_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80811927/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (127/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6443/25000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4475/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4475 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4475*1^1024 ≤ 0^1024*1^4475 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4475 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4475/1024 : ℝ) ≤ (364741789213568367/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4475 ≤ (364741789213568367/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4475*20000000000000000000^1024 ≤ 364741789213568367^1024*5^4475 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 364741789213568367 20000000000000000000 4475 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (364741789213568367/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4475/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4475 := by
      have hnat : (1 : ℕ)^1024*1^4475 ≤ 1^4475*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4475 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20364741789213568367/20000000000000000000 : ℝ) ≤ (10041441017413833/10000000000000000 : ℝ) ^ (4475/1024 : ℝ) := by
    have hpowers : (20364741789213568367/20000000000000000000 : ℝ)^1024 ≤ (10041441017413833/10000000000000000 : ℝ)^4475 := by
      have hnat : (20364741789213568367 : ℕ)^1024*10000000000000000^4475 ≤ 10041441017413833^4475*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20364741789213568367 20000000000000000000 10041441017413833 10000000000000000 1024 4475 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10041441017413833/10000000000000000 : ℝ)) (X := (20364741789213568367/20000000000000000000 : ℝ)) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10364741789213568367/10000000000000000000 : ℝ) ≤ (5041441017413833/5000000000000000 : ℝ) ^ (4475/1024 : ℝ) := by
    have hpowers : (10364741789213568367/10000000000000000000 : ℝ)^1024 ≤ (5041441017413833/5000000000000000 : ℝ)^4475 := by
      have hnat : (10364741789213568367 : ℕ)^1024*5000000000000000^4475 ≤ 5041441017413833^4475*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10364741789213568367 10000000000000000000 5041441017413833 5000000000000000 1024 4475 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5041441017413833/5000000000000000 : ℝ)) (X := (10364741789213568367/10000000000000000000 : ℝ)) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(41441017413833/4000000000000000 : ℝ)*(0 : ℝ))^(4475/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(41441017413833/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(364741789213568367/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(41441017413833/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4475/1024 : ℝ) := by
    rw [show (1 : ℝ)+(41441017413833/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10041441017413833/10000000000000000 : ℝ) by norm_num, show 1+(364741789213568367/20000000000000000000 : ℝ)+(0 : ℝ)=(20364741789213568367/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(364741789213568367/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(41441017413833/4000000000000000 : ℝ)*(2/5 : ℝ))^(4475/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(41441017413833/4000000000000000 : ℝ)*(2/5 : ℝ)=(5041441017413833/5000000000000000 : ℝ) by norm_num, show 1+2*(364741789213568367/20000000000000000000 : ℝ)=(10364741789213568367/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(41441017413833/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4475/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41441017413833/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(41441017413833/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4475/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41441017413833/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(41441017413833/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4475/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41441017413833/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-854709043/5000000000 : ℝ)*X 0 0+(5929969623/10000000000 : ℝ)*X 0 1+(4845795149/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2741391509/5000000000 : ℝ)*X 1 0+(-2318864697/10000000000 : ℝ)*X 1 1+(2422897581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5482783011/10000000000 : ℝ)*X 2 0+(2422897599/5000000000 : ℝ)*X 2 1+(-1159432331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((415112957/1000000000 : ℝ)*X 0 0+(618262139/2000000000 : ℝ)*X 0 1+(5511705131/10000000000 : ℝ)*X 0 2+(415112957/1000000000 : ℝ)*X 1 0+(618262139/2000000000 : ℝ)*X 1 1+(5511705131/10000000000 : ℝ)*X 1 2+(415112957/1000000000 : ℝ)*X 2 0+(618262139/2000000000 : ℝ)*X 2 1+(5511705131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214141379/1250000000 : ℝ)*X 0 0+(2436780529/5000000000 : ℝ)*X 0 1+(5901206167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((103733819/200000000 : ℝ)*X 1 0+(-126345407/1000000000 : ℝ)*X 1 1+(147530149/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5186690991/10000000000 : ℝ)*X 2 0+(5901206041/10000000000 : ℝ)*X 2 1+(-31586347/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4159418503/10000000000 : ℝ)*X 0 0+(340607403/625000000 : ℝ)*X 0 1+(3155524721/10000000000 : ℝ)*X 0 2+(4159418503/10000000000 : ℝ)*X 1 0+(340607403/625000000 : ℝ)*X 1 1+(3155524721/10000000000 : ℝ)*X 1 2+(4159418503/10000000000 : ℝ)*X 2 0+(340607403/625000000 : ℝ)*X 2 1+(3155524721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105386346588338630153367/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11109737/50000000000000 : ℝ)*(base1) + (234460043/50000000000000 : ℝ)*(base19) + (467742483/100000000000000 : ℝ)*(base23) + (26288371/50000000000000 : ℝ)*(upper3) + (31012329/50000000000000 : ℝ)*(upper5) + (667760653233867/100000000000000 : ℝ)*(major0) + (667760653233867/100000000000000 : ℝ)*(major1) + (667760653233867/100000000000000 : ℝ)*(major2) + (46118115896699/5000000000000 : ℝ)*(sp0) + (922363527991809/100000000000000 : ℝ)*(sp1) + (230590882292353/25000000000000 : ℝ)*(sp2) + (103289125861559/25000000000000 : ℝ)*(sp3) + (1701197389/100000000000000 : ℝ)*(sp4) + (8920407/1250000000000 : ℝ)*(sp7) + (41315723929827/10000000000000 : ℝ)*(f.failure) + (184472799382379/20000000000000 : ℝ)*(f.sum) + (111168775482211/200000000000000000000000000000 : ℝ)*base65 + (1361361269082211/400000000000000000000000000000 : ℝ)*base67 + (1113047006282211/400000000000000000000000000000 : ℝ)*base69 + (1341590165082211/400000000000000000000000000000 : ℝ)*base71 + (414833664482211/200000000000000000000000000000 : ℝ)*base73 + (956860176282211/400000000000000000000000000000 : ℝ)*base75 + (2531126177082211/400000000000000000000000000000 : ℝ)*base77 + (130594679482211/400000000000000000000000000000 : ℝ)*base79 + (265514316517789/200000000000000000000000000000 : ℝ)*base82 + (2353371/500000000000000000000 : ℝ)*base90 + (2353371/500000000000000000000 : ℝ)*base92 + (2353371/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1151019326806831514005353/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (147752933/12500000000000 : ℝ)*(base19) + (1206589383/100000000000000 : ℝ)*(base23) + (16913381/25000000000000 : ℝ)*(base32) + (3382481/2000000000000 : ℝ)*(upper3) + (26208807/20000000000000 : ℝ)*(upper5) + (704490705665049/100000000000000 : ℝ)*(major0) + (704490705665049/100000000000000 : ℝ)*(major1) + (704490705665049/100000000000000 : ℝ)*(major2) + (1398601793/50000000000000 : ℝ)*(sp1) + (618556789/20000000000000 : ℝ)*(sp2) + (486549170958577/50000000000000 : ℝ)*(sp4) + (973094362690103/100000000000000 : ℝ)*(sp5) + (486547021271913/50000000000000 : ℝ)*(sp6) + (217941404961429/50000000000000 : ℝ)*(sp7) + (435882877576381/100000000000000 : ℝ)*(f.failure) + (486549170958577/50000000000000 : ℝ)*(f.sum) + (141351411977183/200000000000000000000000000000 : ℝ)*base66 + (6204317009177183/400000000000000000000000000000 : ℝ)*base68 + (1729832217177183/400000000000000000000000000000 : ℝ)*base70 + (129307528422817/400000000000000000000000000000 : ℝ)*base71 + (2009530029177183/200000000000000000000000000000 : ℝ)*base74 + (864462654777183/400000000000000000000000000000 : ℝ)*base76 + (3583596296777183/400000000000000000000000000000 : ℝ)*base78 + (4338061026777183/400000000000000000000000000000 : ℝ)*base80 + (147957087622817/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (11703813/5000000000000000000000 : ℝ)*base90 + (11703813/5000000000000000000000 : ℝ)*base92 + (11703813/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1490_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80811927/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (127/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6443/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1490_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1490_s1_0 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1869082601/10000000000 : ℝ)*x 0 + (2792791021/5000000000 : ℝ)*x 1 + (5087658963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1869082601/10000000000 : ℝ)^4477 ≤ (710406999187/6250000000000 : ℝ)^3453 := by
    have hnat : (1869082601 : ℕ)^4477*6250000000000^3453 ≤ 710406999187^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869082601 10000000000 710406999187 6250000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2792791021/5000000000 : ℝ)^4477 ≤ (11748993054203/25000000000000 : ℝ)^3453 := by
    have hnat : (2792791021 : ℕ)^4477*25000000000000^3453 ≤ 11748993054203^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2792791021 5000000000 11748993054203 25000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5087658963/10000000000 : ℝ)^4477 ≤ (1040937894361/2500000000000 : ℝ)^3453 := by
    have hnat : (5087658963 : ℕ)^4477*2500000000000^3453 ≤ 1040937894361^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087658963 10000000000 1040937894361 2500000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1869082601/10000000000 : ℝ), (2792791021/5000000000 : ℝ), (5087658963/10000000000 : ℝ)] ![(710406999187/6250000000000 : ℝ), (11748993054203/25000000000000 : ℝ), (1040937894361/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1869082601/10000000000 : ℝ)|^4477 ≤ (710406999187/6250000000000 : ℝ)^3453
        have hw : |(-1869082601/10000000000 : ℝ)|=(1869082601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2792791021/5000000000 : ℝ)|^4477 ≤ (11748993054203/25000000000000 : ℝ)^3453
        have hw : |(2792791021/5000000000 : ℝ)|=(2792791021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5087658963/10000000000 : ℝ)|^4477 ≤ (1040937894361/2500000000000 : ℝ)^3453
        have hw : |(5087658963/10000000000 : ℝ)|=(5087658963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s1_1 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695341441/5000000000 : ℝ)*x 0 + (-2132015291/10000000000 : ℝ)*x 1 + (1271914523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695341441/5000000000 : ℝ)^4477 ≤ (22440459952727/50000000000000 : ℝ)^3453 := by
    have hnat : (2695341441 : ℕ)^4477*50000000000000^3453 ≤ 22440459952727^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695341441 5000000000 22440459952727 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132015291/10000000000 : ℝ)^4477 ≤ (13481573546757/100000000000000 : ℝ)^3453 := by
    have hnat : (2132015291 : ℕ)^4477*100000000000000^3453 ≤ 13481573546757^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132015291 10000000000 13481573546757 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271914523/2500000000 : ℝ)^4477 ≤ (41637506532237/100000000000000 : ℝ)^3453 := by
    have hnat : (1271914523 : ℕ)^4477*100000000000000^3453 ≤ 41637506532237^3453*2500000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271914523 2500000000 41637506532237 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695341441/5000000000 : ℝ), (-2132015291/10000000000 : ℝ), (1271914523/2500000000 : ℝ)] ![(22440459952727/50000000000000 : ℝ), (13481573546757/100000000000000 : ℝ), (41637506532237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695341441/5000000000 : ℝ)|^4477 ≤ (22440459952727/50000000000000 : ℝ)^3453
        have hw : |(2695341441/5000000000 : ℝ)|=(2695341441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132015291/10000000000 : ℝ)|^4477 ≤ (13481573546757/100000000000000 : ℝ)^3453
        have hw : |(-2132015291/10000000000 : ℝ)|=(2132015291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1271914523/2500000000 : ℝ)|^4477 ≤ (41637506532237/100000000000000 : ℝ)^3453
        have hw : |(1271914523/2500000000 : ℝ)|=(1271914523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s1_2 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390682241/10000000000 : ℝ)*x 0 + (5087658531/10000000000 : ℝ)*x 1 + (-2132015567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390682241/10000000000 : ℝ)^4477 ≤ (8976182597217/20000000000000 : ℝ)^3453 := by
    have hnat : (5390682241 : ℕ)^4477*20000000000000^3453 ≤ 8976182597217^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390682241 10000000000 8976182597217 20000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5087658531/10000000000 : ℝ)^4477 ≤ (41637511190477/100000000000000 : ℝ)^3453 := by
    have hnat : (5087658531 : ℕ)^4477*100000000000000^3453 ≤ 41637511190477^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087658531 10000000000 41637511190477 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132015567/10000000000 : ℝ)^4477 ≤ (1685196976197/12500000000000 : ℝ)^3453 := by
    have hnat : (2132015567 : ℕ)^4477*12500000000000^3453 ≤ 1685196976197^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132015567 10000000000 1685196976197 12500000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390682241/10000000000 : ℝ), (5087658531/10000000000 : ℝ), (-2132015567/10000000000 : ℝ)] ![(8976182597217/20000000000000 : ℝ), (41637511190477/100000000000000 : ℝ), (1685196976197/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390682241/10000000000 : ℝ)|^4477 ≤ (8976182597217/20000000000000 : ℝ)^3453
        have hw : |(5390682241/10000000000 : ℝ)|=(5390682241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5087658531/10000000000 : ℝ)|^4477 ≤ (41637511190477/100000000000000 : ℝ)^3453
        have hw : |(5087658531/10000000000 : ℝ)|=(5087658531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132015567/10000000000 : ℝ)|^4477 ≤ (1685196976197/12500000000000 : ℝ)^3453
        have hw : |(-2132015567/10000000000 : ℝ)|=(2132015567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s1_3 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66525467/156250000 : ℝ)*x 0 + (746603431/2000000000 : ℝ)*x 1 + (4844619851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66525467/156250000 : ℝ)^4477 ≤ (33051887692391/100000000000000 : ℝ)^3453 := by
    have hnat : (66525467 : ℕ)^4477*100000000000000^3453 ≤ 33051887692391^3453*156250000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66525467 156250000 33051887692391 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746603431/2000000000 : ℝ)^4477 ≤ (27871014802111/100000000000000 : ℝ)^3453 := by
    have hnat : (746603431 : ℕ)^4477*100000000000000^3453 ≤ 27871014802111^3453*2000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746603431 2000000000 27871014802111 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4844619851/10000000000 : ℝ)^4477 ≤ (9769274374073/25000000000000 : ℝ)^3453 := by
    have hnat : (4844619851 : ℕ)^4477*25000000000000^3453 ≤ 9769274374073^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844619851 10000000000 9769274374073 25000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66525467/156250000 : ℝ), (746603431/2000000000 : ℝ), (4844619851/10000000000 : ℝ)] ![(33051887692391/100000000000000 : ℝ), (27871014802111/100000000000000 : ℝ), (9769274374073/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66525467/156250000 : ℝ)|^4477 ≤ (33051887692391/100000000000000 : ℝ)^3453
        have hw : |(66525467/156250000 : ℝ)|=(66525467/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(746603431/2000000000 : ℝ)|^4477 ≤ (27871014802111/100000000000000 : ℝ)^3453
        have hw : |(746603431/2000000000 : ℝ)|=(746603431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4844619851/10000000000 : ℝ)|^4477 ≤ (9769274374073/25000000000000 : ℝ)^3453
        have hw : |(4844619851/10000000000 : ℝ)|=(4844619851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s1_4 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1869429531/10000000000 : ℝ)*x 0 + (2546701313/5000000000 : ℝ)*x 1 + (1394935659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1869429531/10000000000 : ℝ)^4477 ≤ (1136924752683/10000000000000 : ℝ)^3453 := by
    have hnat : (1869429531 : ℕ)^4477*10000000000000^3453 ≤ 1136924752683^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869429531 10000000000 1136924752683 10000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2546701313/5000000000 : ℝ)^4477 ≤ (1667938885003/4000000000000 : ℝ)^3453 := by
    have hnat : (2546701313 : ℕ)^4477*4000000000000^3453 ≤ 1667938885003^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2546701313 5000000000 1667938885003 4000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1394935659/2500000000 : ℝ)^4477 ≤ (46932280339903/100000000000000 : ℝ)^3453 := by
    have hnat : (1394935659 : ℕ)^4477*100000000000000^3453 ≤ 46932280339903^3453*2500000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394935659 2500000000 46932280339903 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1869429531/10000000000 : ℝ), (2546701313/5000000000 : ℝ), (1394935659/2500000000 : ℝ)] ![(1136924752683/10000000000000 : ℝ), (1667938885003/4000000000000 : ℝ), (46932280339903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1869429531/10000000000 : ℝ)|^4477 ≤ (1136924752683/10000000000000 : ℝ)^3453
        have hw : |(-1869429531/10000000000 : ℝ)|=(1869429531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2546701313/5000000000 : ℝ)|^4477 ≤ (1667938885003/4000000000000 : ℝ)^3453
        have hw : |(2546701313/5000000000 : ℝ)|=(2546701313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1394935659/2500000000 : ℝ)|^4477 ≤ (46932280339903/100000000000000 : ℝ)^3453
        have hw : |(1394935659/2500000000 : ℝ)|=(1394935659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s1_5 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051978161/2000000000 : ℝ)*x 0 + (-819965403/5000000000 : ℝ)*x 1 + (5579742711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051978161/2000000000 : ℝ)^4477 ≤ (10868543487399/25000000000000 : ℝ)^3453 := by
    have hnat : (1051978161 : ℕ)^4477*25000000000000^3453 ≤ 10868543487399^3453*2000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051978161 2000000000 10868543487399 25000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (819965403/5000000000 : ℝ)^4477 ≤ (959354487533/10000000000000 : ℝ)^3453 := by
    have hnat : (819965403 : ℕ)^4477*10000000000000^3453 ≤ 959354487533^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819965403 5000000000 959354487533 10000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5579742711/10000000000 : ℝ)^4477 ≤ (2346614057891/5000000000000 : ℝ)^3453 := by
    have hnat : (5579742711 : ℕ)^4477*5000000000000^3453 ≤ 2346614057891^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5579742711 10000000000 2346614057891 5000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051978161/2000000000 : ℝ), (-819965403/5000000000 : ℝ), (5579742711/10000000000 : ℝ)] ![(10868543487399/25000000000000 : ℝ), (959354487533/10000000000000 : ℝ), (2346614057891/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051978161/2000000000 : ℝ)|^4477 ≤ (10868543487399/25000000000000 : ℝ)^3453
        have hw : |(1051978161/2000000000 : ℝ)|=(1051978161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-819965403/5000000000 : ℝ)|^4477 ≤ (959354487533/10000000000000 : ℝ)^3453
        have hw : |(-819965403/5000000000 : ℝ)|=(819965403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5579742711/10000000000 : ℝ)|^4477 ≤ (2346614057891/5000000000000 : ℝ)^3453
        have hw : |(5579742711/10000000000 : ℝ)|=(5579742711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s1_6 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259890769/10000000000 : ℝ)*x 0 + (348733919/625000000 : ℝ)*x 1 + (-1639930867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259890769/10000000000 : ℝ)^4477 ≤ (43474173563809/100000000000000 : ℝ)^3453 := by
    have hnat : (5259890769 : ℕ)^4477*100000000000000^3453 ≤ 43474173563809^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259890769 10000000000 43474173563809 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (348733919/625000000 : ℝ)^4477 ≤ (46932281081481/100000000000000 : ℝ)^3453 := by
    have hnat : (348733919 : ℕ)^4477*100000000000000^3453 ≤ 46932281081481^3453*625000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348733919 625000000 46932281081481 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1639930867/10000000000 : ℝ)^4477 ≤ (4796772669001/50000000000000 : ℝ)^3453 := by
    have hnat : (1639930867 : ℕ)^4477*50000000000000^3453 ≤ 4796772669001^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639930867 10000000000 4796772669001 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259890769/10000000000 : ℝ), (348733919/625000000 : ℝ), (-1639930867/10000000000 : ℝ)] ![(43474173563809/100000000000000 : ℝ), (46932281081481/100000000000000 : ℝ), (4796772669001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259890769/10000000000 : ℝ)|^4477 ≤ (43474173563809/100000000000000 : ℝ)^3453
        have hw : |(5259890769/10000000000 : ℝ)|=(5259890769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(348733919/625000000 : ℝ)|^4477 ≤ (46932281081481/100000000000000 : ℝ)^3453
        have hw : |(348733919/625000000 : ℝ)|=(348733919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1639930867/10000000000 : ℝ)|^4477 ≤ (4796772669001/50000000000000 : ℝ)^3453
        have hw : |(-1639930867/10000000000 : ℝ)|=(1639930867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s1_7 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064600971/2500000000 : ℝ)*x 0 + (4831797087/10000000000 : ℝ)*x 1 + (468256677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064600971/2500000000 : ℝ)^4477 ≤ (1033114945737/3125000000000 : ℝ)^3453 := by
    have hnat : (1064600971 : ℕ)^4477*3125000000000^3453 ≤ 1033114945737^3453*2500000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064600971 2500000000 1033114945737 3125000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4831797087/10000000000 : ℝ)^4477 ≤ (9735762077909/25000000000000 : ℝ)^3453 := by
    have hnat : (4831797087 : ℕ)^4477*25000000000000^3453 ≤ 9735762077909^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4831797087 10000000000 9735762077909 25000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468256677/1250000000 : ℝ)^4477 ≤ (27997273410183/100000000000000 : ℝ)^3453 := by
    have hnat : (468256677 : ℕ)^4477*100000000000000^3453 ≤ 27997273410183^3453*1250000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468256677 1250000000 27997273410183 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064600971/2500000000 : ℝ), (4831797087/10000000000 : ℝ), (468256677/1250000000 : ℝ)] ![(1033114945737/3125000000000 : ℝ), (9735762077909/25000000000000 : ℝ), (27997273410183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064600971/2500000000 : ℝ)|^4477 ≤ (1033114945737/3125000000000 : ℝ)^3453
        have hw : |(1064600971/2500000000 : ℝ)|=(1064600971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4831797087/10000000000 : ℝ)|^4477 ≤ (9735762077909/25000000000000 : ℝ)^3453
        have hw : |(4831797087/10000000000 : ℝ)|=(4831797087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(468256677/1250000000 : ℝ)|^4477 ≤ (27997273410183/100000000000000 : ℝ)^3453
        have hw : |(468256677/1250000000 : ℝ)|=(468256677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1490_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80811927/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6443/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (127/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (8051/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18579/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6443/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (127/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6443/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (127/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6443/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (127/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6443/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (127/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6443/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (127/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6443/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (127/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (127/5000 : ℝ) ^ (4475/1024 : ℝ) ≤ (53444917673/500000000000000000 : ℝ) := by
    have hpowers : (127/5000 : ℝ)^4475 ≤ (53444917673/500000000000000000 : ℝ)^1024 := by
      have hnat : (127 : ℕ)^4475*500000000000000000^1024 ≤ 53444917673^1024*5000^4475 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127 5000 53444917673 500000000000000000 4475 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (127/5000 : ℝ)) (X := (53444917673/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6443/25000 : ℝ) ^ (4475/1024 : ℝ) ≤ (133542128580566363/50000000000000000000 : ℝ) := by
    have hpowers : (6443/25000 : ℝ)^4475 ≤ (133542128580566363/50000000000000000000 : ℝ)^1024 := by
      have hnat : (6443 : ℕ)^4475*50000000000000000000^1024 ≤ 133542128580566363^1024*25000^4475 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6443 25000 133542128580566363 50000000000000000000 4475 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6443/25000 : ℝ)) (X := (133542128580566363/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250000053444917673/250000000000000000 : ℝ) ≤ (10000000489185173/10000000000000000 : ℝ) ^ (4475/1024 : ℝ) := by
    have hpowers : (250000053444917673/250000000000000000 : ℝ)^1024 ≤ (10000000489185173/10000000000000000 : ℝ)^4475 := by
      have hnat : (250000053444917673 : ℕ)^1024*10000000000000000^4475 ≤ 10000000489185173^4475*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250000053444917673 250000000000000000 10000000489185173 10000000000000000 1024 4475 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000489185173/10000000000000000 : ℝ)) (X := (250000053444917673/250000000000000000 : ℝ)) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50133547473072333663/50000000000000000000 : ℝ) ≤ (10006105564022823/10000000000000000 : ℝ) ^ (4475/1024 : ℝ) := by
    have hpowers : (50133547473072333663/50000000000000000000 : ℝ)^1024 ≤ (10006105564022823/10000000000000000 : ℝ)^4475 := by
      have hnat : (50133547473072333663 : ℕ)^1024*10000000000000000^4475 ≤ 10006105564022823^4475*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50133547473072333663 50000000000000000000 10006105564022823 10000000000000000 1024 4475 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006105564022823/10000000000000000 : ℝ)) (X := (50133547473072333663/50000000000000000000 : ℝ)) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25133542128580566363/25000000000000000000 : ℝ) ≤ (10012210638860473/10000000000000000 : ℝ) ^ (4475/1024 : ℝ) := by
    have hpowers : (25133542128580566363/25000000000000000000 : ℝ)^1024 ≤ (10012210638860473/10000000000000000 : ℝ)^4475 := by
      have hnat : (25133542128580566363 : ℕ)^1024*10000000000000000^4475 ≤ 10012210638860473^4475*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25133542128580566363 25000000000000000000 10012210638860473 10000000000000000 1024 4475 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012210638860473/10000000000000000 : ℝ)) (X := (25133542128580566363/25000000000000000000 : ℝ)) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(53444917673/500000000000000000 : ℝ) ≤ ((14518062349035917321/14520000000000000000 : ℝ)+2*(122101496753/46464000000000 : ℝ)*(127/5000 : ℝ))^(4475/1024 : ℝ) := by
    rw [show (14518062349035917321/14520000000000000000 : ℝ)+2*(122101496753/46464000000000 : ℝ)*(127/5000 : ℝ)=(10000000489185173/10000000000000000 : ℝ) by norm_num, show 1+2*(53444917673/500000000000000000 : ℝ)=(250000053444917673/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(133542128580566363/50000000000000000000 : ℝ)+(53444917673/500000000000000000 : ℝ) ≤ ((14518062349035917321/14520000000000000000 : ℝ)+(122101496753/46464000000000 : ℝ)*((6443/25000 : ℝ)+(127/5000 : ℝ)))^(4475/1024 : ℝ) := by
    rw [show (14518062349035917321/14520000000000000000 : ℝ)+(122101496753/46464000000000 : ℝ)*((6443/25000 : ℝ)+(127/5000 : ℝ))=(10006105564022823/10000000000000000 : ℝ) by norm_num, show 1+(133542128580566363/50000000000000000000 : ℝ)+(53444917673/500000000000000000 : ℝ)=(50133547473072333663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(133542128580566363/50000000000000000000 : ℝ) ≤ ((14518062349035917321/14520000000000000000 : ℝ)+2*(122101496753/46464000000000 : ℝ)*(6443/25000 : ℝ))^(4475/1024 : ℝ) := by
    rw [show (14518062349035917321/14520000000000000000 : ℝ)+2*(122101496753/46464000000000 : ℝ)*(6443/25000 : ℝ)=(10012210638860473/10000000000000000 : ℝ) by norm_num, show 1+2*(133542128580566363/50000000000000000000 : ℝ)=(25133542128580566363/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14518062349035917321/14520000000000000000 : ℝ)*(X 1 0+X 2 0)+(122101496753/46464000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4475/1024 : ℝ)) (lo := (127/5000 : ℝ)) (hi := (6443/25000 : ℝ)) (c := (14518062349035917321/14520000000000000000 : ℝ)) (alpha := (122101496753/46464000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14518062349035917321/14520000000000000000 : ℝ)*(X 0 1+X 2 1)+(122101496753/46464000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4475/1024 : ℝ)) (lo := (127/5000 : ℝ)) (hi := (6443/25000 : ℝ)) (c := (14518062349035917321/14520000000000000000 : ℝ)) (alpha := (122101496753/46464000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14518062349035917321/14520000000000000000 : ℝ)*(X 0 2+X 1 2)+(122101496753/46464000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4475/1024 : ℝ)) (lo := (127/5000 : ℝ)) (hi := (6443/25000 : ℝ)) (c := (14518062349035917321/14520000000000000000 : ℝ)) (alpha := (122101496753/46464000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1869082601/10000000000 : ℝ)*X 0 0+(2792791021/5000000000 : ℝ)*X 0 1+(5087658963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2695341441/5000000000 : ℝ)*X 1 0+(-2132015291/10000000000 : ℝ)*X 1 1+(1271914523/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5390682241/10000000000 : ℝ)*X 2 0+(5087658531/10000000000 : ℝ)*X 2 1+(-2132015567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((66525467/156250000 : ℝ)*X 0 0+(746603431/2000000000 : ℝ)*X 0 1+(4844619851/10000000000 : ℝ)*X 0 2+(66525467/156250000 : ℝ)*X 1 0+(746603431/2000000000 : ℝ)*X 1 1+(4844619851/10000000000 : ℝ)*X 1 2+(66525467/156250000 : ℝ)*X 2 0+(746603431/2000000000 : ℝ)*X 2 1+(4844619851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1869429531/10000000000 : ℝ)*X 0 0+(2546701313/5000000000 : ℝ)*X 0 1+(1394935659/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051978161/2000000000 : ℝ)*X 1 0+(-819965403/5000000000 : ℝ)*X 1 1+(5579742711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259890769/10000000000 : ℝ)*X 2 0+(348733919/625000000 : ℝ)*X 2 1+(-1639930867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1064600971/2500000000 : ℝ)*X 0 0+(4831797087/10000000000 : ℝ)*X 0 1+(468256677/1250000000 : ℝ)*X 0 2+(1064600971/2500000000 : ℝ)*X 1 0+(4831797087/10000000000 : ℝ)*X 1 1+(468256677/1250000000 : ℝ)*X 1 2+(1064600971/2500000000 : ℝ)*X 2 0+(4831797087/10000000000 : ℝ)*X 2 1+(468256677/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20618158334456088863340501/2750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17338647/12500000000000 : ℝ)*(base1) + (32599289/2500000000000 : ℝ)*(base19) + (1065160831/100000000000000 : ℝ)*(base23) + (28634679/12500000000000 : ℝ)*(upper3) + (9308861/20000000000000 : ℝ)*(upper5) + (363494910007141/25000000000000 : ℝ)*(major0) + (363494910007141/25000000000000 : ℝ)*(major1) + (363494910007141/25000000000000 : ℝ)*(major2) + (502087177959593/25000000000000 : ℝ)*(sp0) + (25104383027023/1250000000000 : ℝ)*(sp1) + (200835088097257/10000000000000 : ℝ)*(sp2) + (224901023235687/25000000000000 : ℝ)*(sp3) + (674600841/20000000000000 : ℝ)*(sp4) + (1426177363/50000000000000 : ℝ)*(sp7) + (17992141680133/2000000000000 : ℝ)*(f.failure) + (2008351946133401/100000000000000 : ℝ)*(f.sum) + (825228070669/264000000000000000000000000 : ℝ)*base66 + (57294103783813583/11000000000000000000000000000000 : ℝ)*base68 + (55166309147813583/11000000000000000000000000000000 : ℝ)*base70 + (13445329935813583/11000000000000000000000000000000 : ℝ)*base72 + (1368900452053/264000000000000000000000000 : ℝ)*base74 + (53836027548186417/11000000000000000000000000000000 : ℝ)*base75 + (8445901325813583/11000000000000000000000000000000 : ℝ)*base78 + (86243207659813583/11000000000000000000000000000000 : ℝ)*base80 + (1602727288021/264000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1346291/100000000000000000000 : ℝ)*base89 + (1346291/100000000000000000000 : ℝ)*base91 + (1346291/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17671624962555670552930597/2420000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21919573/1562500000000 : ℝ)*(base19) + (295743247/20000000000000 : ℝ)*(base23) + (99264501/50000000000000 : ℝ)*(upper3) + (36938249/100000000000000 : ℝ)*(lower4) + (135263291/100000000000000 : ℝ)*(upper5) + (29772016611107/2000000000000 : ℝ)*(major0) + (29772016611107/2000000000000 : ℝ)*(major1) + (29772016611107/2000000000000 : ℝ)*(major2) + (8880368481/100000000000000 : ℝ)*(sp1) + (2418268533/25000000000000 : ℝ)*(sp2) + (2056173491614571/100000000000000 : ℝ)*(sp4) + (1028081604196709/50000000000000 : ℝ)*(sp5) + (514040584956051/25000000000000 : ℝ)*(sp6) + (921027926085311/100000000000000 : ℝ)*(sp7) + (921027926085311/100000000000000 : ℝ)*(f.failure) + (2056173491614571/100000000000000 : ℝ)*(f.sum) + (14294365839191/5808000000000000000000000000 : ℝ)*base65 + (92584991202966051/9680000000000000000000000000000 : ℝ)*base68 + (80844787403686051/9680000000000000000000000000000 : ℝ)*base70 + (5595772195993949/9680000000000000000000000000000 : ℝ)*base71 + (34902643475449/5808000000000000000000000000 : ℝ)*base74 + (82003728249606051/9680000000000000000000000000000 : ℝ)*base76 + (56467537698086051/9680000000000000000000000000000 : ℝ)*base78 + (40947653259126051/9680000000000000000000000000000 : ℝ)*base80 + (19021500842137/5808000000000000000000000000 : ℝ)*base82 + (48304297/5000000000000000000000 : ℝ)*base89 + (48304297/5000000000000000000000 : ℝ)*base91 + (48304297/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1490_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80811927/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6443/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (127/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18579/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1490_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1490_s2_0 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-948123011/5000000000 : ℝ)*x 0 + (5465311977/10000000000 : ℝ)*x 1 + (2595187587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (948123011/5000000000 : ℝ)^4477 ≤ (5790574692927/50000000000000 : ℝ)^3453 := by
    have hnat : (948123011 : ℕ)^4477*50000000000000^3453 ≤ 5790574692927^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948123011 5000000000 5790574692927 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465311977/10000000000 : ℝ)^4477 ≤ (45688163064539/100000000000000 : ℝ)^3453 := by
    have hnat : (5465311977 : ℕ)^4477*100000000000000^3453 ≤ 45688163064539^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465311977 10000000000 45688163064539 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2595187587/5000000000 : ℝ)^4477 ≤ (2670667970991/6250000000000 : ℝ)^3453 := by
    have hnat : (2595187587 : ℕ)^4477*6250000000000^3453 ≤ 2670667970991^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595187587 5000000000 2670667970991 6250000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-948123011/5000000000 : ℝ), (5465311977/10000000000 : ℝ), (2595187587/5000000000 : ℝ)] ![(5790574692927/50000000000000 : ℝ), (45688163064539/100000000000000 : ℝ), (2670667970991/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-948123011/5000000000 : ℝ)|^4477 ≤ (5790574692927/50000000000000 : ℝ)^3453
        have hw : |(-948123011/5000000000 : ℝ)|=(948123011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465311977/10000000000 : ℝ)|^4477 ≤ (45688163064539/100000000000000 : ℝ)^3453
        have hw : |(5465311977/10000000000 : ℝ)|=(5465311977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2595187587/5000000000 : ℝ)|^4477 ≤ (2670667970991/6250000000000 : ℝ)^3453
        have hw : |(2595187587/5000000000 : ℝ)|=(2595187587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s2_1 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340085053/2500000000 : ℝ)*x 0 + (-2037974049/10000000000 : ℝ)*x 1 + (5190374831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340085053/2500000000 : ℝ)^4477 ≤ (22276827597229/50000000000000 : ℝ)^3453 := by
    have hnat : (1340085053 : ℕ)^4477*50000000000000^3453 ≤ 22276827597229^3453*2500000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340085053 2500000000 22276827597229 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2037974049/10000000000 : ℝ)^4477 ≤ (12715660917877/100000000000000 : ℝ)^3453 := by
    have hnat : (2037974049 : ℕ)^4477*100000000000000^3453 ≤ 12715660917877^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037974049 10000000000 12715660917877 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190374831/10000000000 : ℝ)^4477 ≤ (42730683874637/100000000000000 : ℝ)^3453 := by
    have hnat : (5190374831 : ℕ)^4477*100000000000000^3453 ≤ 42730683874637^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190374831 10000000000 42730683874637 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340085053/2500000000 : ℝ), (-2037974049/10000000000 : ℝ), (5190374831/10000000000 : ℝ)] ![(22276827597229/50000000000000 : ℝ), (12715660917877/100000000000000 : ℝ), (42730683874637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340085053/2500000000 : ℝ)|^4477 ≤ (22276827597229/50000000000000 : ℝ)^3453
        have hw : |(1340085053/2500000000 : ℝ)|=(1340085053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2037974049/10000000000 : ℝ)|^4477 ≤ (12715660917877/100000000000000 : ℝ)^3453
        have hw : |(-2037974049/10000000000 : ℝ)|=(2037974049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190374831/10000000000 : ℝ)|^4477 ≤ (42730683874637/100000000000000 : ℝ)^3453
        have hw : |(5190374831/10000000000 : ℝ)|=(5190374831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s2_2 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360340299/10000000000 : ℝ)*x 0 + (129759363/250000000 : ℝ)*x 1 + (-254746793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360340299/10000000000 : ℝ)^4477 ≤ (22276828066011/50000000000000 : ℝ)^3453 := by
    have hnat : (5360340299 : ℕ)^4477*50000000000000^3453 ≤ 22276828066011^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360340299 10000000000 22276828066011 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129759363/250000000 : ℝ)^4477 ≤ (42730680554989/100000000000000 : ℝ)^3453 := by
    have hnat : (129759363 : ℕ)^4477*100000000000000^3453 ≤ 42730680554989^3453*250000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129759363 250000000 42730680554989 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254746793/1250000000 : ℝ)^4477 ≤ (1271566330433/10000000000000 : ℝ)^3453 := by
    have hnat : (254746793 : ℕ)^4477*10000000000000^3453 ≤ 1271566330433^3453*1250000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254746793 1250000000 1271566330433 10000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360340299/10000000000 : ℝ), (129759363/250000000 : ℝ), (-254746793/1250000000 : ℝ)] ![(22276828066011/50000000000000 : ℝ), (42730680554989/100000000000000 : ℝ), (1271566330433/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360340299/10000000000 : ℝ)|^4477 ≤ (22276828066011/50000000000000 : ℝ)^3453
        have hw : |(5360340299/10000000000 : ℝ)|=(5360340299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129759363/250000000 : ℝ)|^4477 ≤ (42730680554989/100000000000000 : ℝ)^3453
        have hw : |(129759363/250000000 : ℝ)|=(129759363/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254746793/1250000000 : ℝ)|^4477 ≤ (1271566330433/10000000000000 : ℝ)^3453
        have hw : |(-254746793/1250000000 : ℝ)|=(254746793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s2_3 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138525321/5000000000 : ℝ)*x 0 + (3979666069/10000000000 : ℝ)*x 1 + (4593456701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138525321/5000000000 : ℝ)^4477 ≤ (8311872985759/25000000000000 : ℝ)^3453 := by
    have hnat : (2138525321 : ℕ)^4477*25000000000000^3453 ≤ 8311872985759^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138525321 5000000000 8311872985759 25000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979666069/10000000000 : ℝ)^4477 ≤ (15140829407263/50000000000000 : ℝ)^3453 := by
    have hnat : (3979666069 : ℕ)^4477*50000000000000^3453 ≤ 15140829407263^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979666069 10000000000 15140829407263 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4593456701/10000000000 : ℝ)^4477 ≤ (145883396913/400000000000 : ℝ)^3453 := by
    have hnat : (4593456701 : ℕ)^4477*400000000000^3453 ≤ 145883396913^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4593456701 10000000000 145883396913 400000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138525321/5000000000 : ℝ), (3979666069/10000000000 : ℝ), (4593456701/10000000000 : ℝ)] ![(8311872985759/25000000000000 : ℝ), (15140829407263/50000000000000 : ℝ), (145883396913/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138525321/5000000000 : ℝ)|^4477 ≤ (8311872985759/25000000000000 : ℝ)^3453
        have hw : |(2138525321/5000000000 : ℝ)|=(2138525321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979666069/10000000000 : ℝ)|^4477 ≤ (15140829407263/50000000000000 : ℝ)^3453
        have hw : |(3979666069/10000000000 : ℝ)|=(3979666069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4593456701/10000000000 : ℝ)|^4477 ≤ (145883396913/400000000000 : ℝ)^3453
        have hw : |(4593456701/10000000000 : ℝ)|=(4593456701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s2_4 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-379260589/2000000000 : ℝ)*x 0 + (162254297/312500000 : ℝ)*x 1 + (5463534657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (379260589/2000000000 : ℝ)^4477 ≤ (2316320027477/20000000000000 : ℝ)^3453 := by
    have hnat : (379260589 : ℕ)^4477*20000000000000^3453 ≤ 2316320027477^3453*2000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379260589 2000000000 2316320027477 20000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162254297/312500000 : ℝ)^4477 ≤ (427494997859/1000000000000 : ℝ)^3453 := by
    have hnat : (162254297 : ℕ)^4477*1000000000000^3453 ≤ 427494997859^3453*312500000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162254297 312500000 427494997859 1000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463534657/10000000000 : ℝ)^4477 ≤ (45668900063871/100000000000000 : ℝ)^3453 := by
    have hnat : (5463534657 : ℕ)^4477*100000000000000^3453 ≤ 45668900063871^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463534657 10000000000 45668900063871 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-379260589/2000000000 : ℝ), (162254297/312500000 : ℝ), (5463534657/10000000000 : ℝ)] ![(2316320027477/20000000000000 : ℝ), (427494997859/1000000000000 : ℝ), (45668900063871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-379260589/2000000000 : ℝ)|^4477 ≤ (2316320027477/20000000000000 : ℝ)^3453
        have hw : |(-379260589/2000000000 : ℝ)|=(379260589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162254297/312500000 : ℝ)|^4477 ≤ (427494997859/1000000000000 : ℝ)^3453
        have hw : |(162254297/312500000 : ℝ)|=(162254297/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463534657/10000000000 : ℝ)|^4477 ≤ (45668900063871/100000000000000 : ℝ)^3453
        have hw : |(5463534657/10000000000 : ℝ)|=(5463534657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s2_5 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644194319/5000000000 : ℝ)*x 0 + (-1764814177/10000000000 : ℝ)*x 1 + (1365884097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644194319/5000000000 : ℝ)^4477 ≤ (342029769453/781250000000 : ℝ)^3453 := by
    have hnat : (2644194319 : ℕ)^4477*781250000000^3453 ≤ 342029769453^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644194319 5000000000 342029769453 781250000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1764814177/10000000000 : ℝ)^4477 ≤ (2637817668243/25000000000000 : ℝ)^3453 := by
    have hnat : (1764814177 : ℕ)^4477*25000000000000^3453 ≤ 2637817668243^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764814177 10000000000 2637817668243 25000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365884097/2500000000 : ℝ)^4477 ≤ (45668918823941/100000000000000 : ℝ)^3453 := by
    have hnat : (1365884097 : ℕ)^4477*100000000000000^3453 ≤ 45668918823941^3453*2500000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365884097 2500000000 45668918823941 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644194319/5000000000 : ℝ), (-1764814177/10000000000 : ℝ), (1365884097/2500000000 : ℝ)] ![(342029769453/781250000000 : ℝ), (2637817668243/25000000000000 : ℝ), (45668918823941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644194319/5000000000 : ℝ)|^4477 ≤ (342029769453/781250000000 : ℝ)^3453
        have hw : |(2644194319/5000000000 : ℝ)|=(2644194319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1764814177/10000000000 : ℝ)|^4477 ≤ (2637817668243/25000000000000 : ℝ)^3453
        have hw : |(-1764814177/10000000000 : ℝ)|=(1764814177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365884097/2500000000 : ℝ)|^4477 ≤ (45668918823941/100000000000000 : ℝ)^3453
        have hw : |(1365884097/2500000000 : ℝ)|=(1365884097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s2_6 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644195061/5000000000 : ℝ)*x 0 + (5463533883/10000000000 : ℝ)*x 1 + (-220601953/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644195061/5000000000 : ℝ)^4477 ≤ (43779826418487/100000000000000 : ℝ)^3453 := by
    have hnat : (2644195061 : ℕ)^4477*100000000000000^3453 ≤ 43779826418487^3453*5000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644195061 5000000000 43779826418487 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463533883/10000000000 : ℝ)^4477 ≤ (45668891675487/100000000000000 : ℝ)^3453 := by
    have hnat : (5463533883 : ℕ)^4477*100000000000000^3453 ≤ 45668891675487^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463533883 10000000000 45668891675487 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220601953/1250000000 : ℝ)^4477 ≤ (5275640944833/50000000000000 : ℝ)^3453 := by
    have hnat : (220601953 : ℕ)^4477*50000000000000^3453 ≤ 5275640944833^3453*1250000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220601953 1250000000 5275640944833 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644195061/5000000000 : ℝ), (5463533883/10000000000 : ℝ), (-220601953/1250000000 : ℝ)] ![(43779826418487/100000000000000 : ℝ), (45668891675487/100000000000000 : ℝ), (5275640944833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644195061/5000000000 : ℝ)|^4477 ≤ (43779826418487/100000000000000 : ℝ)^3453
        have hw : |(2644195061/5000000000 : ℝ)|=(2644195061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463533883/10000000000 : ℝ)|^4477 ≤ (45668891675487/100000000000000 : ℝ)^3453
        have hw : |(5463533883/10000000000 : ℝ)|=(5463533883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220601953/1250000000 : ℝ)|^4477 ≤ (5275640944833/50000000000000 : ℝ)^3453
        have hw : |(-220601953/1250000000 : ℝ)|=(220601953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1490_s2_7 (p : ℝ) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4277183673/10000000000 : ℝ)*x 0 + (4589527743/10000000000 : ℝ)*x 1 + (796725749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4277183673/10000000000 : ℝ)^4477 ≤ (16624416365143/50000000000000 : ℝ)^3453 := by
    have hnat : (4277183673 : ℕ)^4477*50000000000000^3453 ≤ 16624416365143^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4277183673 10000000000 16624416365143 50000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4589527743/10000000000 : ℝ)^4477 ≤ (36430408491717/100000000000000 : ℝ)^3453 := by
    have hnat : (4589527743 : ℕ)^4477*100000000000000^3453 ≤ 36430408491717^3453*10000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4589527743 10000000000 36430408491717 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796725749/2000000000 : ℝ)^4477 ≤ (30320758765379/100000000000000 : ℝ)^3453 := by
    have hnat : (796725749 : ℕ)^4477*100000000000000^3453 ≤ 30320758765379^3453*2000000000^4477 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796725749 2000000000 30320758765379 100000000000000 4477 3453 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4477/1024 : ℝ)) 4477 3453 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4277183673/10000000000 : ℝ), (4589527743/10000000000 : ℝ), (796725749/2000000000 : ℝ)] ![(16624416365143/50000000000000 : ℝ), (36430408491717/100000000000000 : ℝ), (30320758765379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4277183673/10000000000 : ℝ)|^4477 ≤ (16624416365143/50000000000000 : ℝ)^3453
        have hw : |(4277183673/10000000000 : ℝ)|=(4277183673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4589527743/10000000000 : ℝ)|^4477 ≤ (36430408491717/100000000000000 : ℝ)^3453
        have hw : |(4589527743/10000000000 : ℝ)|=(4589527743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796725749/2000000000 : ℝ)|^4477 ≤ (30320758765379/100000000000000 : ℝ)^3453
        have hw : |(796725749/2000000000 : ℝ)|=(796725749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1490_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80811927/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18579/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8043/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18579/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18579/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18579/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18579/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18579/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18579/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8051/100000 : ℝ) ^ (4475/1024 : ℝ) ≤ (826809629522351/50000000000000000000 : ℝ) := by
    have hpowers : (8051/100000 : ℝ)^4475 ≤ (826809629522351/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8051 : ℕ)^4475*50000000000000000000^1024 ≤ 826809629522351^1024*100000^4475 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8051 100000 826809629522351 50000000000000000000 4475 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8051/100000 : ℝ)) (X := (826809629522351/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18579/100000 : ℝ) ^ (4475/1024 : ℝ) ≤ (31953022532418961/50000000000000000000 : ℝ) := by
    have hpowers : (18579/100000 : ℝ)^4475 ≤ (31953022532418961/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18579 : ℕ)^4475*50000000000000000000^1024 ≤ 31953022532418961^1024*100000^4475 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18579 100000 31953022532418961 50000000000000000000 4475 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18579/100000 : ℝ)) (X := (31953022532418961/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000826809629522351/25000000000000000000 : ℝ) ≤ (10000075677520813/10000000000000000 : ℝ) ^ (4475/1024 : ℝ) := by
    have hpowers : (25000826809629522351/25000000000000000000 : ℝ)^1024 ≤ (10000075677520813/10000000000000000 : ℝ)^4475 := by
      have hnat : (25000826809629522351 : ℕ)^1024*10000000000000000^4475 ≤ 10000075677520813^4475*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000826809629522351 25000000000000000000 10000075677520813 10000000000000000 1024 4475 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000075677520813/10000000000000000 : ℝ)) (X := (25000826809629522351/25000000000000000000 : ℝ)) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (781762184877530333/781250000000000000 : ℝ) ≤ (2500374950459813/2500000000000000 : ℝ) ^ (4475/1024 : ℝ) := by
    have hpowers : (781762184877530333/781250000000000000 : ℝ)^1024 ≤ (2500374950459813/2500000000000000 : ℝ)^4475 := by
      have hnat : (781762184877530333 : ℕ)^1024*2500000000000000^4475 ≤ 2500374950459813^4475*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781762184877530333 781250000000000000 2500374950459813 2500000000000000 1024 4475 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500374950459813/2500000000000000 : ℝ)) (X := (781762184877530333/781250000000000000 : ℝ)) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25031953022532418961/25000000000000000000 : ℝ) ≤ (10002923926157691/10000000000000000 : ℝ) ^ (4475/1024 : ℝ) := by
    have hpowers : (25031953022532418961/25000000000000000000 : ℝ)^1024 ≤ (10002923926157691/10000000000000000 : ℝ)^4475 := by
      have hnat : (25031953022532418961 : ℕ)^1024*10000000000000000^4475 ≤ 10002923926157691^4475*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25031953022532418961 25000000000000000000 10002923926157691 10000000000000000 1024 4475 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002923926157691/10000000000000000 : ℝ)) (X := (25031953022532418961/25000000000000000000 : ℝ)) (by norm_num) 4475 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(826809629522351/50000000000000000000 : ℝ) ≤ ((52628932741581807243/52640000000000000000 : ℝ)+2*(1424124318439/1052800000000000 : ℝ)*(8051/100000 : ℝ))^(4475/1024 : ℝ) := by
    rw [show (52628932741581807243/52640000000000000000 : ℝ)+2*(1424124318439/1052800000000000 : ℝ)*(8051/100000 : ℝ)=(10000075677520813/10000000000000000 : ℝ) by norm_num, show 1+2*(826809629522351/50000000000000000000 : ℝ)=(25000826809629522351/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31953022532418961/50000000000000000000 : ℝ)+(826809629522351/50000000000000000000 : ℝ) ≤ ((52628932741581807243/52640000000000000000 : ℝ)+(1424124318439/1052800000000000 : ℝ)*((18579/100000 : ℝ)+(8051/100000 : ℝ)))^(4475/1024 : ℝ) := by
    rw [show (52628932741581807243/52640000000000000000 : ℝ)+(1424124318439/1052800000000000 : ℝ)*((18579/100000 : ℝ)+(8051/100000 : ℝ))=(2500374950459813/2500000000000000 : ℝ) by norm_num, show 1+(31953022532418961/50000000000000000000 : ℝ)+(826809629522351/50000000000000000000 : ℝ)=(781762184877530333/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31953022532418961/50000000000000000000 : ℝ) ≤ ((52628932741581807243/52640000000000000000 : ℝ)+2*(1424124318439/1052800000000000 : ℝ)*(18579/100000 : ℝ))^(4475/1024 : ℝ) := by
    rw [show (52628932741581807243/52640000000000000000 : ℝ)+2*(1424124318439/1052800000000000 : ℝ)*(18579/100000 : ℝ)=(10002923926157691/10000000000000000 : ℝ) by norm_num, show 1+2*(31953022532418961/50000000000000000000 : ℝ)=(25031953022532418961/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52628932741581807243/52640000000000000000 : ℝ)*(X 1 0+X 2 0)+(1424124318439/1052800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4475/1024 : ℝ)) (lo := (8051/100000 : ℝ)) (hi := (18579/100000 : ℝ)) (c := (52628932741581807243/52640000000000000000 : ℝ)) (alpha := (1424124318439/1052800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52628932741581807243/52640000000000000000 : ℝ)*(X 0 1+X 2 1)+(1424124318439/1052800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4475/1024 : ℝ)) (lo := (8051/100000 : ℝ)) (hi := (18579/100000 : ℝ)) (c := (52628932741581807243/52640000000000000000 : ℝ)) (alpha := (1424124318439/1052800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52628932741581807243/52640000000000000000 : ℝ)*(X 0 2+X 1 2)+(1424124318439/1052800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4475/1024 : ℝ)) (lo := (8051/100000 : ℝ)) (hi := (18579/100000 : ℝ)) (c := (52628932741581807243/52640000000000000000 : ℝ)) (alpha := (1424124318439/1052800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-948123011/5000000000 : ℝ)*X 0 0+(5465311977/10000000000 : ℝ)*X 0 1+(2595187587/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340085053/2500000000 : ℝ)*X 1 0+(-2037974049/10000000000 : ℝ)*X 1 1+(5190374831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360340299/10000000000 : ℝ)*X 2 0+(129759363/250000000 : ℝ)*X 2 1+(-254746793/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2138525321/5000000000 : ℝ)*X 0 0+(3979666069/10000000000 : ℝ)*X 0 1+(4593456701/10000000000 : ℝ)*X 0 2+(2138525321/5000000000 : ℝ)*X 1 0+(3979666069/10000000000 : ℝ)*X 1 1+(4593456701/10000000000 : ℝ)*X 1 2+(2138525321/5000000000 : ℝ)*X 2 0+(3979666069/10000000000 : ℝ)*X 2 1+(4593456701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-379260589/2000000000 : ℝ)*X 0 0+(162254297/312500000 : ℝ)*X 0 1+(5463534657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644194319/5000000000 : ℝ)*X 1 0+(-1764814177/10000000000 : ℝ)*X 1 1+(1365884097/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644195061/5000000000 : ℝ)*X 2 0+(5463533883/10000000000 : ℝ)*X 2 1+(-220601953/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4277183673/10000000000 : ℝ)*X 0 0+(4589527743/10000000000 : ℝ)*X 0 1+(796725749/2000000000 : ℝ)*X 0 2+(4277183673/10000000000 : ℝ)*X 1 0+(4589527743/10000000000 : ℝ)*X 1 1+(796725749/2000000000 : ℝ)*X 1 2+(4277183673/10000000000 : ℝ)*X 2 0+(4589527743/10000000000 : ℝ)*X 2 1+(796725749/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1490_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9367216396977588890847577257/1316000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (293273269/12500000000000 : ℝ)*(base19) + (1106094121/50000000000000 : ℝ)*(base23) + (191851011/50000000000000 : ℝ)*(upper3) + (20694301/20000000000000 : ℝ)*(upper4) + (4781151/20000000000000 : ℝ)*(upper5) + (1316624039895389/50000000000000 : ℝ)*(major0) + (1316624039895389/50000000000000 : ℝ)*(major1) + (1316624039895389/50000000000000 : ℝ)*(major2) + (3637228523308739/100000000000000 : ℝ)*(sp0) + (909312218327287/25000000000000 : ℝ)*(sp1) + (181862450365353/5000000000000 : ℝ)*(sp2) + (1629230446967351/100000000000000 : ℝ)*(sp3) + (11348093281/50000000000000 : ℝ)*(sp4) + (14255854039/100000000000000 : ℝ)*(sp7) + (1629244702821391/100000000000000 : ℝ)*(f.failure) + (3637251219495301/100000000000000 : ℝ)*(f.sum) + (115170996874651/26320000000000000000000000000 : ℝ)*base65 + (29366026559667052527/2632000000000000000000000000000000 : ℝ)*base67 + (25391339450939052527/2632000000000000000000000000000000 : ℝ)*base69 + (34908890860291052527/2632000000000000000000000000000000 : ℝ)*base71 + (34541421811691/26320000000000000000000000000 : ℝ)*base73 + (59623844280763052527/2632000000000000000000000000000000 : ℝ)*base75 + (9501269543843052527/2632000000000000000000000000000000 : ℝ)*base77 + (11537850957899052527/2632000000000000000000000000000000 : ℝ)*base79 + (19867113192651/26320000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (43530457/5000000000000000000000 : ℝ)*base89 + (43530457/5000000000000000000000 : ℝ)*base91 + (43530457/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10990859961954262694446706019/1316000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113913749/12500000000000 : ℝ)*(base23) + (13518231/3125000000000 : ℝ)*(lower2) + (300065543/100000000000000 : ℝ)*(upper3) + (22594963/5000000000000 : ℝ)*(lower4) + (1333775455976989/50000000000000 : ℝ)*(major0) + (1333775455976989/50000000000000 : ℝ)*(major1) + (1333775455976989/50000000000000 : ℝ)*(major2) + (6182136861/50000000000000 : ℝ)*(sp1) + (166218021/25000000000000 : ℝ)*(sp2) + (1211760981/10000000000000 : ℝ)*(sp3) + (921158243869861/25000000000000 : ℝ)*(sp4) + (1842310305602861/50000000000000 : ℝ)*(sp5) + (460578924912171/12500000000000 : ℝ)*(sp6) + (103153528276757/6250000000000 : ℝ)*(sp7) + (1650468570037921/100000000000000 : ℝ)*(f.failure) + (921158243869861/25000000000000 : ℝ)*(f.sum) + (151995053076949/26320000000000000000000000000 : ℝ)*base66 + (4040932492573918673/2632000000000000000000000000000000 : ℝ)*base68 + (13146576204605918673/2632000000000000000000000000000000 : ℝ)*base70 + (19576284568178081327/2632000000000000000000000000000000 : ℝ)*base71 + (93655091702709/26320000000000000000000000000 : ℝ)*base74 + (14544136732274081327/2632000000000000000000000000000000 : ℝ)*base75 + (113538115234994081327/2632000000000000000000000000000000 : ℝ)*base77 + (41386987843490081327/2632000000000000000000000000000000 : ℝ)*base79 + (156742520602869/26320000000000000000000000000 : ℝ)*base82 + (40916233/5000000000000000000000 : ℝ)*base90 + (40916233/5000000000000000000000 : ℝ)*base92 + (40916233/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1490_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80811927/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18579/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8043/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1490_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1490_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80811927/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8043/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1490_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1490_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1490_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4475/1024 : ℝ) ≤ p) (hpb : p ≤ (4477/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80811927/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8043/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1490_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
