-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1184_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:50:29.593269+00:00
-- url     : https://prove2.me/submissions/a015da0a-f045-490c-8f37-e589411b6aa6

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
theorem support_rectangle_w1184_s3_0 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143593239/10000000000 : ℝ)*x 0 + (5424995577/10000000000 : ℝ)*x 1 + (1308968419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143593239/10000000000 : ℝ)^8377 ≤ (6511437292731/50000000000000 : ℝ)^6329 := by
    have hnat : (2143593239 : ℕ)^8377*50000000000000^6329 ≤ 6511437292731^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143593239 10000000000 6511437292731 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424995577/10000000000 : ℝ)^8377 ≤ (22254802139737/50000000000000 : ℝ)^6329 := by
    have hnat : (5424995577 : ℕ)^8377*50000000000000^6329 ≤ 22254802139737^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424995577 10000000000 22254802139737 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308968419/2500000000 : ℝ)^8377 ≤ (2123376056243/5000000000000 : ℝ)^6329 := by
    have hnat : (1308968419 : ℕ)^8377*5000000000000^6329 ≤ 2123376056243^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308968419 2500000000 2123376056243 5000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143593239/10000000000 : ℝ), (5424995577/10000000000 : ℝ), (1308968419/2500000000 : ℝ)] ![(6511437292731/50000000000000 : ℝ), (22254802139737/50000000000000 : ℝ), (2123376056243/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143593239/10000000000 : ℝ)|^8377 ≤ (6511437292731/50000000000000 : ℝ)^6329
        have hw : |(-2143593239/10000000000 : ℝ)|=(2143593239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424995577/10000000000 : ℝ)|^8377 ≤ (22254802139737/50000000000000 : ℝ)^6329
        have hw : |(5424995577/10000000000 : ℝ)|=(5424995577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308968419/2500000000 : ℝ)|^8377 ≤ (2123376056243/5000000000000 : ℝ)^6329
        have hw : |(1308968419/2500000000 : ℝ)|=(1308968419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s3_1 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352803499/10000000000 : ℝ)*x 0 + (-89607207/400000000 : ℝ)*x 1 + (2617936741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352803499/10000000000 : ℝ)^8377 ≤ (10931832787779/25000000000000 : ℝ)^6329 := by
    have hnat : (5352803499 : ℕ)^8377*25000000000000^6329 ≤ 10931832787779^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352803499 10000000000 10931832787779 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89607207/400000000 : ℝ)^8377 ≤ (13805149786247/100000000000000 : ℝ)^6329 := by
    have hnat : (89607207 : ℕ)^8377*100000000000000^6329 ≤ 13805149786247^6329*400000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89607207 400000000 13805149786247 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617936741/5000000000 : ℝ)^8377 ≤ (21233759521089/50000000000000 : ℝ)^6329 := by
    have hnat : (2617936741 : ℕ)^8377*50000000000000^6329 ≤ 21233759521089^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617936741 5000000000 21233759521089 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352803499/10000000000 : ℝ), (-89607207/400000000 : ℝ), (2617936741/5000000000 : ℝ)] ![(10931832787779/25000000000000 : ℝ), (13805149786247/100000000000000 : ℝ), (21233759521089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352803499/10000000000 : ℝ)|^8377 ≤ (10931832787779/25000000000000 : ℝ)^6329
        have hw : |(5352803499/10000000000 : ℝ)|=(5352803499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89607207/400000000 : ℝ)|^8377 ≤ (13805149786247/100000000000000 : ℝ)^6329
        have hw : |(-89607207/400000000 : ℝ)|=(89607207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617936741/5000000000 : ℝ)|^8377 ≤ (21233759521089/50000000000000 : ℝ)^6329
        have hw : |(2617936741/5000000000 : ℝ)|=(2617936741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s3_2 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352803587/10000000000 : ℝ)*x 0 + (5235873441/10000000000 : ℝ)*x 1 + (-140011257/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352803587/10000000000 : ℝ)^8377 ≤ (43727332102613/100000000000000 : ℝ)^6329 := by
    have hnat : (5352803587 : ℕ)^8377*100000000000000^6329 ≤ 43727332102613^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352803587 10000000000 43727332102613 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235873441/10000000000 : ℝ)^8377 ≤ (5308439825253/12500000000000 : ℝ)^6329 := by
    have hnat : (5235873441 : ℕ)^8377*12500000000000^6329 ≤ 5308439825253^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235873441 10000000000 5308439825253 12500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140011257/625000000 : ℝ)^8377 ≤ (13805149272379/100000000000000 : ℝ)^6329 := by
    have hnat : (140011257 : ℕ)^8377*100000000000000^6329 ≤ 13805149272379^6329*625000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140011257 625000000 13805149272379 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352803587/10000000000 : ℝ), (5235873441/10000000000 : ℝ), (-140011257/625000000 : ℝ)] ![(43727332102613/100000000000000 : ℝ), (5308439825253/12500000000000 : ℝ), (13805149272379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352803587/10000000000 : ℝ)|^8377 ≤ (43727332102613/100000000000000 : ℝ)^6329
        have hw : |(5352803587/10000000000 : ℝ)|=(5352803587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235873441/10000000000 : ℝ)|^8377 ≤ (5308439825253/12500000000000 : ℝ)^6329
        have hw : |(5235873441/10000000000 : ℝ)|=(5235873441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-140011257/625000000 : ℝ)|^8377 ≤ (13805149272379/100000000000000 : ℝ)^6329
        have hw : |(-140011257/625000000 : ℝ)|=(140011257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s3_3 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178392897/5000000000 : ℝ)*x 0 + (4171171601/10000000000 : ℝ)*x 1 + (2275263473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178392897/5000000000 : ℝ)^8377 ≤ (2081057508357/6250000000000 : ℝ)^6329 := by
    have hnat : (2178392897 : ℕ)^8377*6250000000000^6329 ≤ 2081057508357^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178392897 5000000000 2081057508357 6250000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171171601/10000000000 : ℝ)^8377 ≤ (7858097931757/25000000000000 : ℝ)^6329 := by
    have hnat : (4171171601 : ℕ)^8377*25000000000000^6329 ≤ 7858097931757^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171171601 10000000000 7858097931757 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2275263473/5000000000 : ℝ)^8377 ≤ (35270688124579/100000000000000 : ℝ)^6329 := by
    have hnat : (2275263473 : ℕ)^8377*100000000000000^6329 ≤ 35270688124579^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275263473 5000000000 35270688124579 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178392897/5000000000 : ℝ), (4171171601/10000000000 : ℝ), (2275263473/5000000000 : ℝ)] ![(2081057508357/6250000000000 : ℝ), (7858097931757/25000000000000 : ℝ), (35270688124579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178392897/5000000000 : ℝ)|^8377 ≤ (2081057508357/6250000000000 : ℝ)^6329
        have hw : |(2178392897/5000000000 : ℝ)|=(2178392897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171171601/10000000000 : ℝ)|^8377 ≤ (7858097931757/25000000000000 : ℝ)^6329
        have hw : |(4171171601/10000000000 : ℝ)|=(4171171601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2275263473/5000000000 : ℝ)|^8377 ≤ (35270688124579/100000000000000 : ℝ)^6329
        have hw : |(2275263473/5000000000 : ℝ)|=(2275263473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s3_4 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143609413/10000000000 : ℝ)*x 0 + (5236586941/10000000000 : ℝ)*x 1 + (5424278447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143609413/10000000000 : ℝ)^8377 ≤ (6511502321551/50000000000000 : ℝ)^6329 := by
    have hnat : (2143609413 : ℕ)^8377*50000000000000^6329 ≤ 6511502321551^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143609413 10000000000 6511502321551 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236586941/10000000000 : ℝ)^8377 ≤ (5309397316319/12500000000000 : ℝ)^6329 := by
    have hnat : (5236586941 : ℕ)^8377*12500000000000^6329 ≤ 5309397316319^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236586941 10000000000 5309397316319 12500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424278447/10000000000 : ℝ)^8377 ≤ (11125454202459/25000000000000 : ℝ)^6329 := by
    have hnat : (5424278447 : ℕ)^8377*25000000000000^6329 ≤ 11125454202459^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424278447 10000000000 11125454202459 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143609413/10000000000 : ℝ), (5236586941/10000000000 : ℝ), (5424278447/10000000000 : ℝ)] ![(6511502321551/50000000000000 : ℝ), (5309397316319/12500000000000 : ℝ), (11125454202459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143609413/10000000000 : ℝ)|^8377 ≤ (6511502321551/50000000000000 : ℝ)^6329
        have hw : |(-2143609413/10000000000 : ℝ)|=(2143609413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236586941/10000000000 : ℝ)|^8377 ≤ (5309397316319/12500000000000 : ℝ)^6329
        have hw : |(5236586941/10000000000 : ℝ)|=(5236586941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424278447/10000000000 : ℝ)|^8377 ≤ (11125454202459/25000000000000 : ℝ)^6329
        have hw : |(5424278447/10000000000 : ℝ)|=(5424278447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s3_5 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663093239/1250000000 : ℝ)*x 0 + (-2051774969/10000000000 : ℝ)*x 1 + (1084855679/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663093239/1250000000 : ℝ)^8377 ≤ (1080211651473/2500000000000 : ℝ)^6329 := by
    have hnat : (663093239 : ℕ)^8377*2500000000000^6329 ≤ 1080211651473^6329*1250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663093239 1250000000 1080211651473 2500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051774969/10000000000 : ℝ)^8377 ≤ (768107354957/6250000000000 : ℝ)^6329 := by
    have hnat : (2051774969 : ℕ)^8377*6250000000000^6329 ≤ 768107354957^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051774969 10000000000 768107354957 6250000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084855679/2000000000 : ℝ)^8377 ≤ (44501816245169/100000000000000 : ℝ)^6329 := by
    have hnat : (1084855679 : ℕ)^8377*100000000000000^6329 ≤ 44501816245169^6329*2000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084855679 2000000000 44501816245169 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663093239/1250000000 : ℝ), (-2051774969/10000000000 : ℝ), (1084855679/2000000000 : ℝ)] ![(1080211651473/2500000000000 : ℝ), (768107354957/6250000000000 : ℝ), (44501816245169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663093239/1250000000 : ℝ)|^8377 ≤ (1080211651473/2500000000000 : ℝ)^6329
        have hw : |(663093239/1250000000 : ℝ)|=(663093239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051774969/10000000000 : ℝ)|^8377 ≤ (768107354957/6250000000000 : ℝ)^6329
        have hw : |(-2051774969/10000000000 : ℝ)|=(2051774969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084855679/2000000000 : ℝ)|^8377 ≤ (44501816245169/100000000000000 : ℝ)^6329
        have hw : |(1084855679/2000000000 : ℝ)|=(1084855679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s3_6 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304745571/10000000000 : ℝ)*x 0 + (5424278769/10000000000 : ℝ)*x 1 + (-51294373/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304745571/10000000000 : ℝ)^8377 ≤ (4320846238261/10000000000000 : ℝ)^6329 := by
    have hnat : (5304745571 : ℕ)^8377*10000000000000^6329 ≤ 4320846238261^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304745571 10000000000 4320846238261 10000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424278769/10000000000 : ℝ)^8377 ≤ (44501820306429/100000000000000 : ℝ)^6329 := by
    have hnat : (5424278769 : ℕ)^8377*100000000000000^6329 ≤ 44501820306429^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424278769 10000000000 44501820306429 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51294373/250000000 : ℝ)^8377 ≤ (12289717290839/100000000000000 : ℝ)^6329 := by
    have hnat : (51294373 : ℕ)^8377*100000000000000^6329 ≤ 12289717290839^6329*250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51294373 250000000 12289717290839 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304745571/10000000000 : ℝ), (5424278769/10000000000 : ℝ), (-51294373/250000000 : ℝ)] ![(4320846238261/10000000000000 : ℝ), (44501820306429/100000000000000 : ℝ), (12289717290839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304745571/10000000000 : ℝ)|^8377 ≤ (4320846238261/10000000000000 : ℝ)^6329
        have hw : |(5304745571/10000000000 : ℝ)|=(5304745571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424278769/10000000000 : ℝ)|^8377 ≤ (44501820306429/100000000000000 : ℝ)^6329
        have hw : |(5424278769/10000000000 : ℝ)|=(5424278769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51294373/250000000 : ℝ)|^8377 ≤ (12289717290839/100000000000000 : ℝ)^6329
        have hw : |(-51294373/250000000 : ℝ)|=(51294373/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s3_7 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356818513/10000000000 : ℝ)*x 0 + (2274547929/5000000000 : ℝ)*x 1 + (4172610233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356818513/10000000000 : ℝ)^8377 ≤ (8324312776537/25000000000000 : ℝ)^6329 := by
    have hnat : (4356818513 : ℕ)^8377*25000000000000^6329 ≤ 8324312776537^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356818513 10000000000 8324312776537 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2274547929/5000000000 : ℝ)^8377 ≤ (70512014637/200000000000 : ℝ)^6329 := by
    have hnat : (2274547929 : ℕ)^8377*200000000000^6329 ≤ 70512014637^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274547929 5000000000 70512014637 200000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172610233/10000000000 : ℝ)^8377 ≤ (31446741556483/100000000000000 : ℝ)^6329 := by
    have hnat : (4172610233 : ℕ)^8377*100000000000000^6329 ≤ 31446741556483^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172610233 10000000000 31446741556483 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356818513/10000000000 : ℝ), (2274547929/5000000000 : ℝ), (4172610233/10000000000 : ℝ)] ![(8324312776537/25000000000000 : ℝ), (70512014637/200000000000 : ℝ), (31446741556483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356818513/10000000000 : ℝ)|^8377 ≤ (8324312776537/25000000000000 : ℝ)^6329
        have hw : |(4356818513/10000000000 : ℝ)|=(4356818513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2274547929/5000000000 : ℝ)|^8377 ≤ (70512014637/200000000000 : ℝ)^6329
        have hw : |(2274547929/5000000000 : ℝ)|=(2274547929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172610233/10000000000 : ℝ)|^8377 ≤ (31446741556483/100000000000000 : ℝ)^6329
        have hw : |(4172610233/10000000000 : ℝ)|=(4172610233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1184_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16381/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1157/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2689/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16381/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1157/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16381/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1157/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16381/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1157/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16381/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1157/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16381/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1157/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16381/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1157/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1157/12500 : ℝ) ^ (1047/256 : ℝ) ≤ (2963486721244441/50000000000000000000 : ℝ) := by
    have hpowers : (1157/12500 : ℝ)^1047 ≤ (2963486721244441/50000000000000000000 : ℝ)^256 := by
      have hnat : (1157 : ℕ)^1047*50000000000000000000^256 ≤ 2963486721244441^256*12500^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1157 12500 2963486721244441 50000000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1157/12500 : ℝ)) (X := (2963486721244441/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16381/100000 : ℝ) ^ (1047/256 : ℝ) ≤ (7650415990815319/12500000000000000000 : ℝ) := by
    have hpowers : (16381/100000 : ℝ)^1047 ≤ (7650415990815319/12500000000000000000 : ℝ)^256 := by
      have hnat : (16381 : ℕ)^1047*12500000000000000000^256 ≤ 7650415990815319^256*100000^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16381 100000 7650415990815319 12500000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16381/100000 : ℝ)) (X := (7650415990815319/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002963486721244441/25000000000000000000 : ℝ) ≤ (200005796512949/200000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (25002963486721244441/25000000000000000000 : ℝ)^256 ≤ (200005796512949/200000000000000 : ℝ)^1047 := by
      have hnat : (25002963486721244441 : ℕ)^256*200000000000000^1047 ≤ 200005796512949^1047*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002963486721244441 25000000000000000000 200005796512949 200000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200005796512949/200000000000000 : ℝ)) (X := (25002963486721244441/25000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50033565150684505717/50000000000000000000 : ℝ) ≤ (10001640974304157/10000000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (50033565150684505717/50000000000000000000 : ℝ)^256 ≤ (10001640974304157/10000000000000000 : ℝ)^1047 := by
      have hnat : (50033565150684505717 : ℕ)^256*10000000000000000^1047 ≤ 10001640974304157^1047*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033565150684505717 50000000000000000000 10001640974304157 10000000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001640974304157/10000000000000000 : ℝ)) (X := (50033565150684505717/50000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6257650415990815319/6250000000000000000 : ℝ) ≤ (312593503842527/312500000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (6257650415990815319/6250000000000000000 : ℝ)^256 ≤ (312593503842527/312500000000000 : ℝ)^1047 := by
      have hnat : (6257650415990815319 : ℕ)^256*312500000000000^1047 ≤ 312593503842527^1047*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6257650415990815319 6250000000000000000 312593503842527 312500000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312593503842527/312500000000000 : ℝ)) (X := (6257650415990815319/6250000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2963486721244441/50000000000000000000 : ℝ) ≤ ((11871175423967520211/11875000000000000000 : ℝ)+2*(450382885569/237500000000000 : ℝ)*(1157/12500 : ℝ))^(1047/256 : ℝ) := by
    rw [show (11871175423967520211/11875000000000000000 : ℝ)+2*(450382885569/237500000000000 : ℝ)*(1157/12500 : ℝ)=(200005796512949/200000000000000 : ℝ) by norm_num, show 1+2*(2963486721244441/50000000000000000000 : ℝ)=(25002963486721244441/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7650415990815319/12500000000000000000 : ℝ)+(2963486721244441/50000000000000000000 : ℝ) ≤ ((11871175423967520211/11875000000000000000 : ℝ)+(450382885569/237500000000000 : ℝ)*((16381/100000 : ℝ)+(1157/12500 : ℝ)))^(1047/256 : ℝ) := by
    rw [show (11871175423967520211/11875000000000000000 : ℝ)+(450382885569/237500000000000 : ℝ)*((16381/100000 : ℝ)+(1157/12500 : ℝ))=(10001640974304157/10000000000000000 : ℝ) by norm_num, show 1+(7650415990815319/12500000000000000000 : ℝ)+(2963486721244441/50000000000000000000 : ℝ)=(50033565150684505717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7650415990815319/12500000000000000000 : ℝ) ≤ ((11871175423967520211/11875000000000000000 : ℝ)+2*(450382885569/237500000000000 : ℝ)*(16381/100000 : ℝ))^(1047/256 : ℝ) := by
    rw [show (11871175423967520211/11875000000000000000 : ℝ)+2*(450382885569/237500000000000 : ℝ)*(16381/100000 : ℝ)=(312593503842527/312500000000000 : ℝ) by norm_num, show 1+2*(7650415990815319/12500000000000000000 : ℝ)=(6257650415990815319/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11871175423967520211/11875000000000000000 : ℝ)*(X 1 0+X 2 0)+(450382885569/237500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (1157/12500 : ℝ)) (hi := (16381/100000 : ℝ)) (c := (11871175423967520211/11875000000000000000 : ℝ)) (alpha := (450382885569/237500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11871175423967520211/11875000000000000000 : ℝ)*(X 0 1+X 2 1)+(450382885569/237500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (1157/12500 : ℝ)) (hi := (16381/100000 : ℝ)) (c := (11871175423967520211/11875000000000000000 : ℝ)) (alpha := (450382885569/237500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11871175423967520211/11875000000000000000 : ℝ)*(X 0 2+X 1 2)+(450382885569/237500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (1157/12500 : ℝ)) (hi := (16381/100000 : ℝ)) (c := (11871175423967520211/11875000000000000000 : ℝ)) (alpha := (450382885569/237500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2143593239/10000000000 : ℝ)*X 0 0+(5424995577/10000000000 : ℝ)*X 0 1+(1308968419/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352803499/10000000000 : ℝ)*X 1 0+(-89607207/400000000 : ℝ)*X 1 1+(2617936741/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352803587/10000000000 : ℝ)*X 2 0+(5235873441/10000000000 : ℝ)*X 2 1+(-140011257/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178392897/5000000000 : ℝ)*X 0 0+(4171171601/10000000000 : ℝ)*X 0 1+(2275263473/5000000000 : ℝ)*X 0 2+(2178392897/5000000000 : ℝ)*X 1 0+(4171171601/10000000000 : ℝ)*X 1 1+(2275263473/5000000000 : ℝ)*X 1 2+(2178392897/5000000000 : ℝ)*X 2 0+(4171171601/10000000000 : ℝ)*X 2 1+(2275263473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2143609413/10000000000 : ℝ)*X 0 0+(5236586941/10000000000 : ℝ)*X 0 1+(5424278447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663093239/1250000000 : ℝ)*X 1 0+(-2051774969/10000000000 : ℝ)*X 1 1+(1084855679/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304745571/10000000000 : ℝ)*X 2 0+(5424278769/10000000000 : ℝ)*X 2 1+(-51294373/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356818513/10000000000 : ℝ)*X 0 0+(2274547929/5000000000 : ℝ)*X 0 1+(4172610233/10000000000 : ℝ)*X 0 2+(4356818513/10000000000 : ℝ)*X 1 0+(2274547929/5000000000 : ℝ)*X 1 1+(4172610233/10000000000 : ℝ)*X 1 2+(4356818513/10000000000 : ℝ)*X 2 0+(2274547929/5000000000 : ℝ)*X 2 1+(4172610233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (496814159425125211589488719/118750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (269920487/25000000000000 : ℝ)*(base19) + (1079927659/100000000000000 : ℝ)*(base23) + (2319979/5000000000000 : ℝ)*(lower2) + (5675449/6250000000000 : ℝ)*(upper3) + (22012147/20000000000000 : ℝ)*(upper5) + (792369450405543/20000000000000 : ℝ)*(major0) + (792369450405543/20000000000000 : ℝ)*(major1) + (792369450405543/20000000000000 : ℝ)*(major2) + (1321902413566157/25000000000000 : ℝ)*(sp0) + (5287625611677733/100000000000000 : ℝ)*(sp1) + (5287625611432021/100000000000000 : ℝ)*(sp2) + (52721181397891/2000000000000 : ℝ)*(sp3) + (4259273763/25000000000000 : ℝ)*(sp4) + (8603344583/100000000000000 : ℝ)*(sp7) + (2636067673239133/100000000000000 : ℝ)*(f.failure) + (5287626691359681/100000000000000 : ℝ)*(f.sum) + (1983953283579/1187500000000000000000000000 : ℝ)*base66 + (926911842097279573/237500000000000000000000000000000 : ℝ)*base67 + (1338187611915220427/237500000000000000000000000000000 : ℝ)*base70 + (2947353812727720427/237500000000000000000000000000000 : ℝ)*base72 + (148957856551/296875000000000000000000000 : ℝ)*base74 + (104968751240220427/237500000000000000000000000000000 : ℝ)*base76 + (4313613308227720427/237500000000000000000000000000000 : ℝ)*base78 + (6445369698509779573/237500000000000000000000000000000 : ℝ)*base79 + (8171045092579/1187500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (17123321/10000000000000000000000 : ℝ)*base89 + (17123321/10000000000000000000000 : ℝ)*base91 + (17123321/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2319812937813244115643/742187500000000000000000000 : ℝ) := by norm_num
    linear_combination (30559007/2500000000000 : ℝ)*(base19) + (1104546717/100000000000000 : ℝ)*(base23) + (14539479/25000000000000 : ℝ)*(upper3) + (112260797/100000000000000 : ℝ)*(lower4) + (31393339/20000000000000 : ℝ)*(upper5) + (1996007823909911/50000000000000 : ℝ)*(major0) + (1996007823909911/50000000000000 : ℝ)*(major1) + (1996007823909911/50000000000000 : ℝ)*(major2) + (785301787/3125000000000 : ℝ)*(sp1) + (13285005479/50000000000000 : ℝ)*(sp2) + (133197264387653/2500000000000 : ℝ)*(sp4) + (332991513968041/6250000000000 : ℝ)*(sp5) + (1065572580189689/20000000000000 : ℝ)*(sp6) + (2656140615945431/100000000000000 : ℝ)*(sp7) + (2656140615945431/100000000000000 : ℝ)*(f.failure) + (133197264387653/2500000000000 : ℝ)*(f.sum) + (58895109500593/11875000000000000000000000000 : ℝ)*base65 + (3311955862908838779/593750000000000000000000000000000 : ℝ)*base68 + (1056626650997411221/593750000000000000000000000000000 : ℝ)*base69 + (794109512497411221/593750000000000000000000000000000 : ℝ)*base71 + (3355574495617/2968750000000000000000000000 : ℝ)*base73 + (2901891113747411221/593750000000000000000000000000000 : ℝ)*base75 + (657450322096338779/593750000000000000000000000000000 : ℝ)*base78 + (3187655347190088779/593750000000000000000000000000000 : ℝ)*base80 + (55866127315593/11875000000000000000000000000 : ℝ)*base81 + (7608747/10000000000000000000000 : ℝ)*base89 + (7608747/10000000000000000000000 : ℝ)*base91 + (7608747/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1184_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16381/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1157/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1184_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1184_s4_0 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-26828457/125000000 : ℝ)*x 0 + (1079990141/2000000000 : ℝ)*x 1 + (5259161803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26828457/125000000 : ℝ)^8377 ≤ (2608891185561/20000000000000 : ℝ)^6329 := by
    have hnat : (26828457 : ℕ)^8377*20000000000000^6329 ≤ 2608891185561^6329*125000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26828457 125000000 2608891185561 20000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079990141/2000000000 : ℝ)^8377 ≤ (8847566828877/20000000000000 : ℝ)^6329 := by
    have hnat : (1079990141 : ℕ)^8377*20000000000000^6329 ≤ 8847566828877^6329*2000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079990141 2000000000 8847566828877 20000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259161803/10000000000 : ℝ)^8377 ≤ (42717709910521/100000000000000 : ℝ)^6329 := by
    have hnat : (5259161803 : ℕ)^8377*100000000000000^6329 ≤ 42717709910521^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259161803 10000000000 42717709910521 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26828457/125000000 : ℝ), (1079990141/2000000000 : ℝ), (5259161803/10000000000 : ℝ)] ![(2608891185561/20000000000000 : ℝ), (8847566828877/20000000000000 : ℝ), (42717709910521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26828457/125000000 : ℝ)|^8377 ≤ (2608891185561/20000000000000 : ℝ)^6329
        have hw : |(-26828457/125000000 : ℝ)|=(26828457/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079990141/2000000000 : ℝ)|^8377 ≤ (8847566828877/20000000000000 : ℝ)^6329
        have hw : |(1079990141/2000000000 : ℝ)|=(1079990141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259161803/10000000000 : ℝ)|^8377 ≤ (42717709910521/100000000000000 : ℝ)^6329
        have hw : |(5259161803/10000000000 : ℝ)|=(5259161803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s4_1 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (133663073/250000000 : ℝ)*x 0 + (-2217794153/10000000000 : ℝ)*x 1 + (5259162157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133663073/250000000 : ℝ)^8377 ≤ (43659435446781/100000000000000 : ℝ)^6329 := by
    have hnat : (133663073 : ℕ)^8377*100000000000000^6329 ≤ 43659435446781^6329*250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133663073 250000000 43659435446781 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217794153/10000000000 : ℝ)^8377 ≤ (6811425413637/50000000000000 : ℝ)^6329 := by
    have hnat : (2217794153 : ℕ)^8377*50000000000000^6329 ≤ 6811425413637^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217794153 10000000000 6811425413637 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259162157/10000000000 : ℝ)^8377 ≤ (2135885685817/5000000000000 : ℝ)^6329 := by
    have hnat : (5259162157 : ℕ)^8377*5000000000000^6329 ≤ 2135885685817^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259162157 10000000000 2135885685817 5000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133663073/250000000 : ℝ), (-2217794153/10000000000 : ℝ), (5259162157/10000000000 : ℝ)] ![(43659435446781/100000000000000 : ℝ), (6811425413637/50000000000000 : ℝ), (2135885685817/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133663073/250000000 : ℝ)|^8377 ≤ (43659435446781/100000000000000 : ℝ)^6329
        have hw : |(133663073/250000000 : ℝ)|=(133663073/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2217794153/10000000000 : ℝ)|^8377 ≤ (6811425413637/50000000000000 : ℝ)^6329
        have hw : |(-2217794153/10000000000 : ℝ)|=(2217794153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259162157/10000000000 : ℝ)|^8377 ≤ (2135885685817/5000000000000 : ℝ)^6329
        have hw : |(5259162157/10000000000 : ℝ)|=(5259162157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s4_2 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346522767/10000000000 : ℝ)*x 0 + (5259162871/10000000000 : ℝ)*x 1 + (-554448353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346522767/10000000000 : ℝ)^8377 ≤ (436594337931/1000000000000 : ℝ)^6329 := by
    have hnat : (5346522767 : ℕ)^8377*1000000000000^6329 ≤ 436594337931^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346522767 10000000000 436594337931 1000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259162871/10000000000 : ℝ)^8377 ≤ (42717721392483/100000000000000 : ℝ)^6329 := by
    have hnat : (5259162871 : ℕ)^8377*100000000000000^6329 ≤ 42717721392483^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259162871 10000000000 42717721392483 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554448353/2500000000 : ℝ)^8377 ≤ (13622844802811/100000000000000 : ℝ)^6329 := by
    have hnat : (554448353 : ℕ)^8377*100000000000000^6329 ≤ 13622844802811^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554448353 2500000000 13622844802811 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346522767/10000000000 : ℝ), (5259162871/10000000000 : ℝ), (-554448353/2500000000 : ℝ)] ![(436594337931/1000000000000 : ℝ), (42717721392483/100000000000000 : ℝ), (13622844802811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346522767/10000000000 : ℝ)|^8377 ≤ (436594337931/1000000000000 : ℝ)^6329
        have hw : |(5346522767/10000000000 : ℝ)|=(5346522767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259162871/10000000000 : ℝ)|^8377 ≤ (42717721392483/100000000000000 : ℝ)^6329
        have hw : |(5259162871/10000000000 : ℝ)|=(5259162871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554448353/2500000000 : ℝ)|^8377 ≤ (13622844802811/100000000000000 : ℝ)^6329
        have hw : |(-554448353/2500000000 : ℝ)|=(554448353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s4_3 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179195223/5000000000 : ℝ)*x 0 + (843888037/2000000000 : ℝ)*x 1 + (562730571/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179195223/5000000000 : ℝ)^8377 ≤ (33313153104797/100000000000000 : ℝ)^6329 := by
    have hnat : (2179195223 : ℕ)^8377*100000000000000^6329 ≤ 33313153104797^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179195223 5000000000 33313153104797 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (843888037/2000000000 : ℝ)^8377 ≤ (3989340678017/12500000000000 : ℝ)^6329 := by
    have hnat : (843888037 : ℕ)^8377*12500000000000^6329 ≤ 3989340678017^6329*2000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843888037 2000000000 3989340678017 12500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562730571/1250000000 : ℝ)^8377 ≤ (34772121451069/100000000000000 : ℝ)^6329 := by
    have hnat : (562730571 : ℕ)^8377*100000000000000^6329 ≤ 34772121451069^6329*1250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562730571 1250000000 34772121451069 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179195223/5000000000 : ℝ), (843888037/2000000000 : ℝ), (562730571/1250000000 : ℝ)] ![(33313153104797/100000000000000 : ℝ), (3989340678017/12500000000000 : ℝ), (34772121451069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179195223/5000000000 : ℝ)|^8377 ≤ (33313153104797/100000000000000 : ℝ)^6329
        have hw : |(2179195223/5000000000 : ℝ)|=(2179195223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(843888037/2000000000 : ℝ)|^8377 ≤ (3989340678017/12500000000000 : ℝ)^6329
        have hw : |(843888037/2000000000 : ℝ)|=(843888037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562730571/1250000000 : ℝ)|^8377 ≤ (34772121451069/100000000000000 : ℝ)^6329
        have hw : |(562730571/1250000000 : ℝ)|=(562730571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s4_4 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2146283019/10000000000 : ℝ)*x 0 + (5259558161/10000000000 : ℝ)*x 1 + (134988823/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146283019/10000000000 : ℝ)^8377 ≤ (1630563485827/12500000000000 : ℝ)^6329 := by
    have hnat : (2146283019 : ℕ)^8377*12500000000000^6329 ≤ 1630563485827^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146283019 10000000000 1630563485827 12500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259558161/10000000000 : ℝ)^8377 ≤ (42721971167969/100000000000000 : ℝ)^6329 := by
    have hnat : (5259558161 : ℕ)^8377*100000000000000^6329 ≤ 42721971167969^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259558161 10000000000 42721971167969 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134988823/250000000 : ℝ)^8377 ≤ (552919011667/1250000000000 : ℝ)^6329 := by
    have hnat : (134988823 : ℕ)^8377*1250000000000^6329 ≤ 552919011667^6329*250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134988823 250000000 552919011667 1250000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2146283019/10000000000 : ℝ), (5259558161/10000000000 : ℝ), (134988823/250000000 : ℝ)] ![(1630563485827/12500000000000 : ℝ), (42721971167969/100000000000000 : ℝ), (552919011667/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2146283019/10000000000 : ℝ)|^8377 ≤ (1630563485827/12500000000000 : ℝ)^6329
        have hw : |(-2146283019/10000000000 : ℝ)|=(2146283019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259558161/10000000000 : ℝ)|^8377 ≤ (42721971167969/100000000000000 : ℝ)^6329
        have hw : |(5259558161/10000000000 : ℝ)|=(5259558161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134988823/250000000 : ℝ)|^8377 ≤ (552919011667/1250000000000 : ℝ)^6329
        have hw : |(134988823/250000000 : ℝ)|=(134988823/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s4_5 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663843327/1250000000 : ℝ)*x 0 + (-2077403077/10000000000 : ℝ)*x 1 + (5399552927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663843327/1250000000 : ℝ)^8377 ≤ (43273171282781/100000000000000 : ℝ)^6329 := by
    have hnat : (663843327 : ℕ)^8377*100000000000000^6329 ≤ 43273171282781^6329*1250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663843327 1250000000 43273171282781 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077403077/10000000000 : ℝ)^8377 ≤ (249866153979/2000000000000 : ℝ)^6329 := by
    have hnat : (2077403077 : ℕ)^8377*2000000000000^6329 ≤ 249866153979^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077403077 10000000000 249866153979 2000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399552927/10000000000 : ℝ)^8377 ≤ (2211676050463/5000000000000 : ℝ)^6329 := by
    have hnat : (5399552927 : ℕ)^8377*5000000000000^6329 ≤ 2211676050463^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399552927 10000000000 2211676050463 5000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663843327/1250000000 : ℝ), (-2077403077/10000000000 : ℝ), (5399552927/10000000000 : ℝ)] ![(43273171282781/100000000000000 : ℝ), (249866153979/2000000000000 : ℝ), (2211676050463/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663843327/1250000000 : ℝ)|^8377 ≤ (43273171282781/100000000000000 : ℝ)^6329
        have hw : |(663843327/1250000000 : ℝ)|=(663843327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077403077/10000000000 : ℝ)|^8377 ≤ (249866153979/2000000000000 : ℝ)^6329
        have hw : |(-2077403077/10000000000 : ℝ)|=(2077403077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399552927/10000000000 : ℝ)|^8377 ≤ (2211676050463/5000000000000 : ℝ)^6329
        have hw : |(5399552927/10000000000 : ℝ)|=(5399552927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s4_6 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5186276/9765625 : ℝ)*x 0 + (5399552917/10000000000 : ℝ)*x 1 + (-2077403079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5186276/9765625 : ℝ)^8377 ≤ (2163658568453/5000000000000 : ℝ)^6329 := by
    have hnat : (5186276 : ℕ)^8377*5000000000000^6329 ≤ 2163658568453^6329*9765625^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186276 9765625 2163658568453 5000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399552917/10000000000 : ℝ)^8377 ≤ (44233520900831/100000000000000 : ℝ)^6329 := by
    have hnat : (5399552917 : ℕ)^8377*100000000000000^6329 ≤ 44233520900831^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399552917 10000000000 44233520900831 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077403079/10000000000 : ℝ)^8377 ≤ (1249330771487/10000000000000 : ℝ)^6329 := by
    have hnat : (2077403079 : ℕ)^8377*10000000000000^6329 ≤ 1249330771487^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077403079 10000000000 1249330771487 10000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5186276/9765625 : ℝ), (5399552917/10000000000 : ℝ), (-2077403079/10000000000 : ℝ)] ![(2163658568453/5000000000000 : ℝ), (44233520900831/100000000000000 : ℝ), (1249330771487/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5186276/9765625 : ℝ)|^8377 ≤ (2163658568453/5000000000000 : ℝ)^6329
        have hw : |(5186276/9765625 : ℝ)|=(5186276/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399552917/10000000000 : ℝ)|^8377 ≤ (44233520900831/100000000000000 : ℝ)^6329
        have hw : |(5399552917/10000000000 : ℝ)|=(5399552917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2077403079/10000000000 : ℝ)|^8377 ≤ (1249330771487/10000000000000 : ℝ)^6329
        have hw : |(-2077403079/10000000000 : ℝ)|=(2077403079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s4_7 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871680597/2000000000 : ℝ)*x 0 + (4501050551/10000000000 : ℝ)*x 1 + (844047661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871680597/2000000000 : ℝ)^8377 ≤ (33313279959371/100000000000000 : ℝ)^6329 := by
    have hnat : (871680597 : ℕ)^8377*100000000000000^6329 ≤ 33313279959371^6329*2000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871680597 2000000000 33313279959371 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501050551/10000000000 : ℝ)^8377 ≤ (34764004152543/100000000000000 : ℝ)^6329 := by
    have hnat : (4501050551 : ℕ)^8377*100000000000000^6329 ≤ 34764004152543^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501050551 10000000000 34764004152543 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844047661/2000000000 : ℝ)^8377 ≤ (3990339484137/12500000000000 : ℝ)^6329 := by
    have hnat : (844047661 : ℕ)^8377*12500000000000^6329 ≤ 3990339484137^6329*2000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844047661 2000000000 3990339484137 12500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871680597/2000000000 : ℝ), (4501050551/10000000000 : ℝ), (844047661/2000000000 : ℝ)] ![(33313279959371/100000000000000 : ℝ), (34764004152543/100000000000000 : ℝ), (3990339484137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871680597/2000000000 : ℝ)|^8377 ≤ (33313279959371/100000000000000 : ℝ)^6329
        have hw : |(871680597/2000000000 : ℝ)|=(871680597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501050551/10000000000 : ℝ)|^8377 ≤ (34764004152543/100000000000000 : ℝ)^6329
        have hw : |(4501050551/10000000000 : ℝ)|=(4501050551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844047661/2000000000 : ℝ)|^8377 ≤ (3990339484137/12500000000000 : ℝ)^6329
        have hw : |(844047661/2000000000 : ℝ)|=(844047661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1184_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11253/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2689/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2689/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2689/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2689/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2689/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2689/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2689/25000 : ℝ) ^ (1047/256 : ℝ) ≤ (5477382305931691/50000000000000000000 : ℝ) := by
    have hpowers : (2689/25000 : ℝ)^1047 ≤ (5477382305931691/50000000000000000000 : ℝ)^256 := by
      have hnat : (2689 : ℕ)^1047*50000000000000000000^256 ≤ 5477382305931691^256*25000^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2689 25000 5477382305931691 50000000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2689/25000 : ℝ)) (X := (5477382305931691/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7379/50000 : ℝ) ^ (1047/256 : ℝ) ≤ (499300903628799/1250000000000000000 : ℝ) := by
    have hpowers : (7379/50000 : ℝ)^1047 ≤ (499300903628799/1250000000000000000 : ℝ)^256 := by
      have hnat : (7379 : ℕ)^1047*1250000000000000000^256 ≤ 499300903628799^256*50000^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7379 50000 499300903628799 1250000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7379/50000 : ℝ)) (X := (499300903628799/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005477382305931691/25000000000000000000 : ℝ) ≤ (10000535661446037/10000000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (25005477382305931691/25000000000000000000 : ℝ)^256 ≤ (10000535661446037/10000000000000000 : ℝ)^1047 := by
      have hnat : (25005477382305931691 : ℕ)^256*10000000000000000^1047 ≤ 10000535661446037^1047*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005477382305931691 25000000000000000000 10000535661446037 10000000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000535661446037/10000000000000000 : ℝ)) (X := (25005477382305931691/25000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025449418451083651/50000000000000000000 : ℝ) ≤ (5000622139337029/5000000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (50025449418451083651/50000000000000000000 : ℝ)^256 ≤ (5000622139337029/5000000000000000 : ℝ)^1047 := by
      have hnat : (50025449418451083651 : ℕ)^256*5000000000000000^1047 ≤ 5000622139337029^1047*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025449418451083651 50000000000000000000 5000622139337029 5000000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000622139337029/5000000000000000 : ℝ)) (X := (50025449418451083651/50000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (625499300903628799/625000000000000000 : ℝ) ≤ (10001952895902079/10000000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (625499300903628799/625000000000000000 : ℝ)^256 ≤ (10001952895902079/10000000000000000 : ℝ)^1047 := by
      have hnat : (625499300903628799 : ℕ)^256*10000000000000000^1047 ≤ 10001952895902079^1047*625000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625499300903628799 625000000000000000 10001952895902079 10000000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001952895902079/10000000000000000 : ℝ)) (X := (625499300903628799/625000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5477382305931691/50000000000000000000 : ℝ) ≤ ((20003449971648926161/20010000000000000000 : ℝ)+2*(708617228021/400200000000000 : ℝ)*(2689/25000 : ℝ))^(1047/256 : ℝ) := by
    rw [show (20003449971648926161/20010000000000000000 : ℝ)+2*(708617228021/400200000000000 : ℝ)*(2689/25000 : ℝ)=(10000535661446037/10000000000000000 : ℝ) by norm_num, show 1+2*(5477382305931691/50000000000000000000 : ℝ)=(25005477382305931691/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(499300903628799/1250000000000000000 : ℝ)+(5477382305931691/50000000000000000000 : ℝ) ≤ ((20003449971648926161/20010000000000000000 : ℝ)+(708617228021/400200000000000 : ℝ)*((7379/50000 : ℝ)+(2689/25000 : ℝ)))^(1047/256 : ℝ) := by
    rw [show (20003449971648926161/20010000000000000000 : ℝ)+(708617228021/400200000000000 : ℝ)*((7379/50000 : ℝ)+(2689/25000 : ℝ))=(5000622139337029/5000000000000000 : ℝ) by norm_num, show 1+(499300903628799/1250000000000000000 : ℝ)+(5477382305931691/50000000000000000000 : ℝ)=(50025449418451083651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(499300903628799/1250000000000000000 : ℝ) ≤ ((20003449971648926161/20010000000000000000 : ℝ)+2*(708617228021/400200000000000 : ℝ)*(7379/50000 : ℝ))^(1047/256 : ℝ) := by
    rw [show (20003449971648926161/20010000000000000000 : ℝ)+2*(708617228021/400200000000000 : ℝ)*(7379/50000 : ℝ)=(10001952895902079/10000000000000000 : ℝ) by norm_num, show 1+2*(499300903628799/1250000000000000000 : ℝ)=(625499300903628799/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20003449971648926161/20010000000000000000 : ℝ)*(X 1 0+X 2 0)+(708617228021/400200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (20003449971648926161/20010000000000000000 : ℝ)) (alpha := (708617228021/400200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20003449971648926161/20010000000000000000 : ℝ)*(X 0 1+X 2 1)+(708617228021/400200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (20003449971648926161/20010000000000000000 : ℝ)) (alpha := (708617228021/400200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20003449971648926161/20010000000000000000 : ℝ)*(X 0 2+X 1 2)+(708617228021/400200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (20003449971648926161/20010000000000000000 : ℝ)) (alpha := (708617228021/400200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-26828457/125000000 : ℝ)*X 0 0+(1079990141/2000000000 : ℝ)*X 0 1+(5259161803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133663073/250000000 : ℝ)*X 1 0+(-2217794153/10000000000 : ℝ)*X 1 1+(5259162157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346522767/10000000000 : ℝ)*X 2 0+(5259162871/10000000000 : ℝ)*X 2 1+(-554448353/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179195223/5000000000 : ℝ)*X 0 0+(843888037/2000000000 : ℝ)*X 0 1+(562730571/1250000000 : ℝ)*X 0 2+(2179195223/5000000000 : ℝ)*X 1 0+(843888037/2000000000 : ℝ)*X 1 1+(562730571/1250000000 : ℝ)*X 1 2+(2179195223/5000000000 : ℝ)*X 2 0+(843888037/2000000000 : ℝ)*X 2 1+(562730571/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2146283019/10000000000 : ℝ)*X 0 0+(5259558161/10000000000 : ℝ)*X 0 1+(134988823/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663843327/1250000000 : ℝ)*X 1 0+(-2077403077/10000000000 : ℝ)*X 1 1+(5399552927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5186276/9765625 : ℝ)*X 2 0+(5399552917/10000000000 : ℝ)*X 2 1+(-2077403079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871680597/2000000000 : ℝ)*X 0 0+(4501050551/10000000000 : ℝ)*X 0 1+(844047661/2000000000 : ℝ)*X 0 2+(871680597/2000000000 : ℝ)*X 1 0+(4501050551/10000000000 : ℝ)*X 1 1+(844047661/2000000000 : ℝ)*X 1 2+(871680597/2000000000 : ℝ)*X 2 0+(4501050551/10000000000 : ℝ)*X 2 1+(844047661/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4228242858041675115462823/1334000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (538184527/50000000000000 : ℝ)*(base19) + (296513393/50000000000000 : ℝ)*(base23) + (87016573/50000000000000 : ℝ)*(lower2) + (15404291/2500000000000 : ℝ)*(upper5) + (42575922130943/800000000000 : ℝ)*(major0) + (42575922130943/800000000000 : ℝ)*(major1) + (42575922130943/800000000000 : ℝ)*(major2) + (1775715623261629/25000000000000 : ℝ)*(sp0) + (1775728918638169/25000000000000 : ℝ)*(sp1) + (7102922946694541/100000000000000 : ℝ)*(sp2) + (177052217437697/5000000000000 : ℝ)*(sp3) + (15261668703/25000000000000 : ℝ)*(sp4) + (6788799597/100000000000000 : ℝ)*(sp5) + (12538607233/100000000000000 : ℝ)*(sp7) + (3541056887361173/100000000000000 : ℝ)*(f.failure) + (7102923539721327/100000000000000 : ℝ)*(f.sum) + (2002088286361/4002000000000000000000000000 : ℝ)*base65 + (12117416560089823/16008000000000000000000000000000 : ℝ)*base67 + (31409753396534177/16008000000000000000000000000000 : ℝ)*base70 + (127860483364886177/16008000000000000000000000000000 : ℝ)*base72 + (18597239599303/4002000000000000000000000000 : ℝ)*base73 + (173009688589838177/16008000000000000000000000000000 : ℝ)*base76 + (150269558703086177/16008000000000000000000000000000 : ℝ)*base78 + (6545553445502177/16008000000000000000000000000000 : ℝ)*base80 + (11012476284889/4002000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5009199/10000000000000000000000 : ℝ)*base90 + (5009199/10000000000000000000000 : ℝ)*base92 + (5009199/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1175575460686579808355280431/333500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120177781/20000000000000 : ℝ)*(base19) + (10565057/1562500000000 : ℝ)*(base23) + (68649559/100000000000000 : ℝ)*(upper3) + (28973293/100000000000000 : ℝ)*(lower4) + (6521501/10000000000000 : ℝ)*(upper5) + (5352111044543071/100000000000000 : ℝ)*(major0) + (5352111044543071/100000000000000 : ℝ)*(major1) + (5352111044543071/100000000000000 : ℝ)*(major2) + (3789180503/25000000000000 : ℝ)*(sp1) + (8317535389/50000000000000 : ℝ)*(sp2) + (892890478066691/12500000000000 : ℝ)*(sp4) + (1785777016730653/25000000000000 : ℝ)*(sp5) + (7143106513299101/100000000000000 : ℝ)*(sp6) + (222568634190863/6250000000000 : ℝ)*(sp7) + (222568634190863/6250000000000 : ℝ)*(f.failure) + (892890478066691/12500000000000 : ℝ)*(f.sum) + (27264556925989/20010000000000000000000000000 : ℝ)*base66 + (28010193696528269569/2001000000000000000000000000000000 : ℝ)*base68 + (6412114888487730431/2001000000000000000000000000000000 : ℝ)*base69 + (21244497931224269569/2001000000000000000000000000000000 : ℝ)*base72 + (18762696119989/20010000000000000000000000000 : ℝ)*base74 + (18472488090960269569/2001000000000000000000000000000000 : ℝ)*base76 + (10303013358942269569/2001000000000000000000000000000000 : ℝ)*base78 + (6002425620224730431/2001000000000000000000000000000000 : ℝ)*base79 + (13755681403241/20010000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (3138669/625000000000000000000 : ℝ)*base90 + (3138669/625000000000000000000 : ℝ)*base92 + (3138669/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1184_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1184_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1184_s5_0 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073413373/5000000000 : ℝ)*x 0 + (5393830977/10000000000 : ℝ)*x 1 + (5264920223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073413373/5000000000 : ℝ)^8377 ≤ (4175642249/32000000000 : ℝ)^6329 := by
    have hnat : (1073413373 : ℕ)^8377*32000000000^6329 ≤ 4175642249^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073413373 5000000000 4175642249 32000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393830977/10000000000 : ℝ)^8377 ≤ (8834297775669/20000000000000 : ℝ)^6329 := by
    have hnat : (5393830977 : ℕ)^8377*20000000000000^6329 ≤ 8834297775669^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393830977 10000000000 8834297775669 20000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264920223/10000000000 : ℝ)^8377 ≤ (42779629076573/100000000000000 : ℝ)^6329 := by
    have hnat : (5264920223 : ℕ)^8377*100000000000000^6329 ≤ 42779629076573^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264920223 10000000000 42779629076573 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073413373/5000000000 : ℝ), (5393830977/10000000000 : ℝ), (5264920223/10000000000 : ℝ)] ![(4175642249/32000000000 : ℝ), (8834297775669/20000000000000 : ℝ), (42779629076573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073413373/5000000000 : ℝ)|^8377 ≤ (4175642249/32000000000 : ℝ)^6329
        have hw : |(-1073413373/5000000000 : ℝ)|=(1073413373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393830977/10000000000 : ℝ)|^8377 ≤ (8834297775669/20000000000000 : ℝ)^6329
        have hw : |(5393830977/10000000000 : ℝ)|=(5393830977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264920223/10000000000 : ℝ)|^8377 ≤ (42779629076573/100000000000000 : ℝ)^6329
        have hw : |(5264920223/10000000000 : ℝ)|=(5264920223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s5_1 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672491287/5000000000 : ℝ)*x 0 + (-553056013/2500000000 : ℝ)*x 1 + (5264920223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672491287/5000000000 : ℝ)^8377 ≤ (21821393798627/50000000000000 : ℝ)^6329 := by
    have hnat : (2672491287 : ℕ)^8377*50000000000000^6329 ≤ 21821393798627^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672491287 5000000000 21821393798627 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553056013/2500000000 : ℝ)^8377 ≤ (6788791656739/50000000000000 : ℝ)^6329 := by
    have hnat : (553056013 : ℕ)^8377*50000000000000^6329 ≤ 6788791656739^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553056013 2500000000 6788791656739 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264920223/10000000000 : ℝ)^8377 ≤ (42779629076573/100000000000000 : ℝ)^6329 := by
    have hnat : (5264920223 : ℕ)^8377*100000000000000^6329 ≤ 42779629076573^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264920223 10000000000 42779629076573 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672491287/5000000000 : ℝ), (-553056013/2500000000 : ℝ), (5264920223/10000000000 : ℝ)] ![(21821393798627/50000000000000 : ℝ), (6788791656739/50000000000000 : ℝ), (42779629076573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672491287/5000000000 : ℝ)|^8377 ≤ (21821393798627/50000000000000 : ℝ)^6329
        have hw : |(2672491287/5000000000 : ℝ)|=(2672491287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553056013/2500000000 : ℝ)|^8377 ≤ (6788791656739/50000000000000 : ℝ)^6329
        have hw : |(-553056013/2500000000 : ℝ)|=(553056013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264920223/10000000000 : ℝ)|^8377 ≤ (42779629076573/100000000000000 : ℝ)^6329
        have hw : |(5264920223/10000000000 : ℝ)|=(5264920223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s5_2 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672491287/5000000000 : ℝ)*x 0 + (5264920223/10000000000 : ℝ)*x 1 + (-553056013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672491287/5000000000 : ℝ)^8377 ≤ (21821393798627/50000000000000 : ℝ)^6329 := by
    have hnat : (2672491287 : ℕ)^8377*50000000000000^6329 ≤ 21821393798627^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672491287 5000000000 21821393798627 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264920223/10000000000 : ℝ)^8377 ≤ (42779629076573/100000000000000 : ℝ)^6329 := by
    have hnat : (5264920223 : ℕ)^8377*100000000000000^6329 ≤ 42779629076573^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264920223 10000000000 42779629076573 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553056013/2500000000 : ℝ)^8377 ≤ (6788791656739/50000000000000 : ℝ)^6329 := by
    have hnat : (553056013 : ℕ)^8377*50000000000000^6329 ≤ 6788791656739^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553056013 2500000000 6788791656739 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672491287/5000000000 : ℝ), (5264920223/10000000000 : ℝ), (-553056013/2500000000 : ℝ)] ![(21821393798627/50000000000000 : ℝ), (42779629076573/100000000000000 : ℝ), (6788791656739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672491287/5000000000 : ℝ)|^8377 ≤ (21821393798627/50000000000000 : ℝ)^6329
        have hw : |(2672491287/5000000000 : ℝ)|=(2672491287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264920223/10000000000 : ℝ)|^8377 ≤ (42779629076573/100000000000000 : ℝ)^6329
        have hw : |(5264920223/10000000000 : ℝ)|=(5264920223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-553056013/2500000000 : ℝ)|^8377 ≤ (6788791656739/50000000000000 : ℝ)^6329
        have hw : |(-553056013/2500000000 : ℝ)|=(553056013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s5_3 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358711871/10000000000 : ℝ)*x 0 + (4231311723/10000000000 : ℝ)*x 1 + (897978161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358711871/10000000000 : ℝ)^8377 ≤ (16658202467503/50000000000000 : ℝ)^6329 := by
    have hnat : (4358711871 : ℕ)^8377*50000000000000^6329 ≤ 16658202467503^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358711871 10000000000 16658202467503 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231311723/10000000000 : ℝ)^8377 ≤ (16016814403653/50000000000000 : ℝ)^6329 := by
    have hnat : (4231311723 : ℕ)^8377*50000000000000^6329 ≤ 16016814403653^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231311723 10000000000 16016814403653 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897978161/2000000000 : ℝ)^8377 ≤ (34649966233613/100000000000000 : ℝ)^6329 := by
    have hnat : (897978161 : ℕ)^8377*100000000000000^6329 ≤ 34649966233613^6329*2000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897978161 2000000000 34649966233613 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358711871/10000000000 : ℝ), (4231311723/10000000000 : ℝ), (897978161/2000000000 : ℝ)] ![(16658202467503/50000000000000 : ℝ), (16016814403653/50000000000000 : ℝ), (34649966233613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358711871/10000000000 : ℝ)|^8377 ≤ (16658202467503/50000000000000 : ℝ)^6329
        have hw : |(4358711871/10000000000 : ℝ)|=(4358711871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231311723/10000000000 : ℝ)|^8377 ≤ (16016814403653/50000000000000 : ℝ)^6329
        have hw : |(4231311723/10000000000 : ℝ)|=(4231311723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897978161/2000000000 : ℝ)|^8377 ≤ (34649966233613/100000000000000 : ℝ)^6329
        have hw : |(897978161/2000000000 : ℝ)|=(897978161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s5_4 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-429366371/2000000000 : ℝ)*x 0 + (5265252371/10000000000 : ℝ)*x 1 + (269674881/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429366371/2000000000 : ℝ)^8377 ≤ (6524461565197/50000000000000 : ℝ)^6329 := by
    have hnat : (429366371 : ℕ)^8377*50000000000000^6329 ≤ 6524461565197^6329*2000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429366371 2000000000 6524461565197 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265252371/10000000000 : ℝ)^8377 ≤ (534790015849/1250000000000 : ℝ)^6329 := by
    have hnat : (5265252371 : ℕ)^8377*1250000000000^6329 ≤ 534790015849^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265252371 10000000000 534790015849 1250000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269674881/500000000 : ℝ)^8377 ≤ (11041968895959/25000000000000 : ℝ)^6329 := by
    have hnat : (269674881 : ℕ)^8377*25000000000000^6329 ≤ 11041968895959^6329*500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269674881 500000000 11041968895959 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429366371/2000000000 : ℝ), (5265252371/10000000000 : ℝ), (269674881/500000000 : ℝ)] ![(6524461565197/50000000000000 : ℝ), (534790015849/1250000000000 : ℝ), (11041968895959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429366371/2000000000 : ℝ)|^8377 ≤ (6524461565197/50000000000000 : ℝ)^6329
        have hw : |(-429366371/2000000000 : ℝ)|=(429366371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265252371/10000000000 : ℝ)|^8377 ≤ (534790015849/1250000000000 : ℝ)^6329
        have hw : |(5265252371/10000000000 : ℝ)|=(5265252371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269674881/500000000 : ℝ)|^8377 ≤ (11041968895959/25000000000000 : ℝ)^6329
        have hw : |(269674881/500000000 : ℝ)|=(269674881/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s5_5 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312222899/10000000000 : ℝ)*x 0 + (-260455839/1250000000 : ℝ)*x 1 + (5393497617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312222899/10000000000 : ℝ)^8377 ≤ (21644546789737/50000000000000 : ℝ)^6329 := by
    have hnat : (5312222899 : ℕ)^8377*50000000000000^6329 ≤ 21644546789737^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312222899 10000000000 21644546789737 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260455839/1250000000 : ℝ)^8377 ≤ (1567878855411/12500000000000 : ℝ)^6329 := by
    have hnat : (260455839 : ℕ)^8377*12500000000000^6329 ≤ 1567878855411^6329*1250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260455839 1250000000 1567878855411 12500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393497617/10000000000 : ℝ)^8377 ≤ (44167875551319/100000000000000 : ℝ)^6329 := by
    have hnat : (5393497617 : ℕ)^8377*100000000000000^6329 ≤ 44167875551319^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393497617 10000000000 44167875551319 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312222899/10000000000 : ℝ), (-260455839/1250000000 : ℝ), (5393497617/10000000000 : ℝ)] ![(21644546789737/50000000000000 : ℝ), (1567878855411/12500000000000 : ℝ), (44167875551319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312222899/10000000000 : ℝ)|^8377 ≤ (21644546789737/50000000000000 : ℝ)^6329
        have hw : |(5312222899/10000000000 : ℝ)|=(5312222899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260455839/1250000000 : ℝ)|^8377 ≤ (1567878855411/12500000000000 : ℝ)^6329
        have hw : |(-260455839/1250000000 : ℝ)|=(260455839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393497617/10000000000 : ℝ)|^8377 ≤ (44167875551319/100000000000000 : ℝ)^6329
        have hw : |(5393497617/10000000000 : ℝ)|=(5393497617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s5_6 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132805573/250000000 : ℝ)*x 0 + (5393497653/10000000000 : ℝ)*x 1 + (-520911659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132805573/250000000 : ℝ)^8377 ≤ (43289093805977/100000000000000 : ℝ)^6329 := by
    have hnat : (132805573 : ℕ)^8377*100000000000000^6329 ≤ 43289093805977^6329*250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132805573 250000000 43289093805977 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393497653/10000000000 : ℝ)^8377 ≤ (44167875941523/100000000000000 : ℝ)^6329 := by
    have hnat : (5393497653 : ℕ)^8377*100000000000000^6329 ≤ 44167875941523^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393497653 10000000000 44167875941523 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520911659/2500000000 : ℝ)^8377 ≤ (783939389859/6250000000000 : ℝ)^6329 := by
    have hnat : (520911659 : ℕ)^8377*6250000000000^6329 ≤ 783939389859^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520911659 2500000000 783939389859 6250000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132805573/250000000 : ℝ), (5393497653/10000000000 : ℝ), (-520911659/2500000000 : ℝ)] ![(43289093805977/100000000000000 : ℝ), (44167875941523/100000000000000 : ℝ), (783939389859/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132805573/250000000 : ℝ)|^8377 ≤ (43289093805977/100000000000000 : ℝ)^6329
        have hw : |(132805573/250000000 : ℝ)|=(132805573/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393497653/10000000000 : ℝ)|^8377 ≤ (44167875941523/100000000000000 : ℝ)^6329
        have hw : |(5393497653/10000000000 : ℝ)|=(5393497653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520911659/2500000000 : ℝ)|^8377 ≤ (783939389859/6250000000000 : ℝ)^6329
        have hw : |(-520911659/2500000000 : ℝ)|=(520911659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s5_7 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544840261/1250000000 : ℝ)*x 0 + (4489224581/10000000000 : ℝ)*x 1 + (423198051/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544840261/1250000000 : ℝ)^8377 ≤ (1332660332033/4000000000000 : ℝ)^6329 := by
    have hnat : (544840261 : ℕ)^8377*4000000000000^6329 ≤ 1332660332033^6329*1250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544840261 1250000000 1332660332033 4000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489224581/10000000000 : ℝ)^8377 ≤ (34643161199553/100000000000000 : ℝ)^6329 := by
    have hnat : (4489224581 : ℕ)^8377*100000000000000^6329 ≤ 34643161199553^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489224581 10000000000 34643161199553 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423198051/1000000000 : ℝ)^8377 ≤ (8010082620973/25000000000000 : ℝ)^6329 := by
    have hnat : (423198051 : ℕ)^8377*25000000000000^6329 ≤ 8010082620973^6329*1000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423198051 1000000000 8010082620973 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544840261/1250000000 : ℝ), (4489224581/10000000000 : ℝ), (423198051/1000000000 : ℝ)] ![(1332660332033/4000000000000 : ℝ), (34643161199553/100000000000000 : ℝ), (8010082620973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544840261/1250000000 : ℝ)|^8377 ≤ (1332660332033/4000000000000 : ℝ)^6329
        have hw : |(544840261/1250000000 : ℝ)|=(544840261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489224581/10000000000 : ℝ)|^8377 ≤ (34643161199553/100000000000000 : ℝ)^6329
        have hw : |(4489224581/10000000000 : ℝ)|=(4489224581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423198051/1000000000 : ℝ)|^8377 ≤ (8010082620973/25000000000000 : ℝ)^6329
        have hw : |(423198051/1000000000 : ℝ)|=(423198051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1184_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (91/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7053/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11253/100000 : ℝ) ^ (1047/256 : ℝ) ≤ (13177580062023629/100000000000000000000 : ℝ) := by
    have hpowers : (11253/100000 : ℝ)^1047 ≤ (13177580062023629/100000000000000000000 : ℝ)^256 := by
      have hnat : (11253 : ℕ)^1047*100000000000000000000^256 ≤ 13177580062023629^256*100000^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11253 100000 13177580062023629 100000000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11253/100000 : ℝ)) (X := (13177580062023629/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (1047/256 : ℝ) ≤ (34453993318476329/100000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^1047 ≤ (34453993318476329/100000000000000000000 : ℝ)^256 := by
      have hnat : (7117 : ℕ)^1047*100000000000000000000^256 ≤ 34453993318476329^256*50000^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 34453993318476329 100000000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (34453993318476329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013177580062023629/50000000000000000000 : ℝ) ≤ (10000644340917089/10000000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (50013177580062023629/50000000000000000000 : ℝ)^256 ≤ (10000644340917089/10000000000000000 : ℝ)^1047 := by
      have hnat : (50013177580062023629 : ℕ)^256*10000000000000000^1047 ≤ 10000644340917089^1047*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013177580062023629 50000000000000000000 10000644340917089 10000000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000644340917089/10000000000000000 : ℝ)) (X := (50013177580062023629/50000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023815786690249979/50000000000000000000 : ℝ) ≤ (2000232884229839/2000000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (50023815786690249979/50000000000000000000 : ℝ)^256 ≤ (2000232884229839/2000000000000000 : ℝ)^1047 := by
      have hnat : (50023815786690249979 : ℕ)^256*2000000000000000^1047 ≤ 2000232884229839^1047*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023815786690249979 50000000000000000000 2000232884229839 2000000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000232884229839/2000000000000000 : ℝ)) (X := (50023815786690249979/50000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034453993318476329/50000000000000000000 : ℝ) ≤ (10001684501381301/10000000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (50034453993318476329/50000000000000000000 : ℝ)^256 ≤ (10001684501381301/10000000000000000 : ℝ)^1047 := by
      have hnat : (50034453993318476329 : ℕ)^256*10000000000000000^1047 ≤ 10001684501381301^1047*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034453993318476329 50000000000000000000 10001684501381301 10000000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001684501381301/10000000000000000 : ℝ)) (X := (50034453993318476329/50000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13177580062023629/100000000000000000000 : ℝ) ≤ ((2709110532233642243/2710000000000000000 : ℝ)+2*(260040116053/149050000000000 : ℝ)*(11253/100000 : ℝ))^(1047/256 : ℝ) := by
    rw [show (2709110532233642243/2710000000000000000 : ℝ)+2*(260040116053/149050000000000 : ℝ)*(11253/100000 : ℝ)=(10000644340917089/10000000000000000 : ℝ) by norm_num, show 1+2*(13177580062023629/100000000000000000000 : ℝ)=(50013177580062023629/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34453993318476329/100000000000000000000 : ℝ)+(13177580062023629/100000000000000000000 : ℝ) ≤ ((2709110532233642243/2710000000000000000 : ℝ)+(260040116053/149050000000000 : ℝ)*((7117/50000 : ℝ)+(11253/100000 : ℝ)))^(1047/256 : ℝ) := by
    rw [show (2709110532233642243/2710000000000000000 : ℝ)+(260040116053/149050000000000 : ℝ)*((7117/50000 : ℝ)+(11253/100000 : ℝ))=(2000232884229839/2000000000000000 : ℝ) by norm_num, show 1+(34453993318476329/100000000000000000000 : ℝ)+(13177580062023629/100000000000000000000 : ℝ)=(50023815786690249979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34453993318476329/100000000000000000000 : ℝ) ≤ ((2709110532233642243/2710000000000000000 : ℝ)+2*(260040116053/149050000000000 : ℝ)*(7117/50000 : ℝ))^(1047/256 : ℝ) := by
    rw [show (2709110532233642243/2710000000000000000 : ℝ)+2*(260040116053/149050000000000 : ℝ)*(7117/50000 : ℝ)=(10001684501381301/10000000000000000 : ℝ) by norm_num, show 1+2*(34453993318476329/100000000000000000000 : ℝ)=(50034453993318476329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2709110532233642243/2710000000000000000 : ℝ)*(X 1 0+X 2 0)+(260040116053/149050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (2709110532233642243/2710000000000000000 : ℝ)) (alpha := (260040116053/149050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2709110532233642243/2710000000000000000 : ℝ)*(X 0 1+X 2 1)+(260040116053/149050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (2709110532233642243/2710000000000000000 : ℝ)) (alpha := (260040116053/149050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2709110532233642243/2710000000000000000 : ℝ)*(X 0 2+X 1 2)+(260040116053/149050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (2709110532233642243/2710000000000000000 : ℝ)) (alpha := (260040116053/149050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1073413373/5000000000 : ℝ)*X 0 0+(5393830977/10000000000 : ℝ)*X 0 1+(5264920223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672491287/5000000000 : ℝ)*X 1 0+(-553056013/2500000000 : ℝ)*X 1 1+(5264920223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672491287/5000000000 : ℝ)*X 2 0+(5264920223/10000000000 : ℝ)*X 2 1+(-553056013/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358711871/10000000000 : ℝ)*X 0 0+(4231311723/10000000000 : ℝ)*X 0 1+(897978161/2000000000 : ℝ)*X 0 2+(4358711871/10000000000 : ℝ)*X 1 0+(4231311723/10000000000 : ℝ)*X 1 1+(897978161/2000000000 : ℝ)*X 1 2+(4358711871/10000000000 : ℝ)*X 2 0+(4231311723/10000000000 : ℝ)*X 2 1+(897978161/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-429366371/2000000000 : ℝ)*X 0 0+(5265252371/10000000000 : ℝ)*X 0 1+(269674881/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312222899/10000000000 : ℝ)*X 1 0+(-260455839/1250000000 : ℝ)*X 1 1+(5393497617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132805573/250000000 : ℝ)*X 2 0+(5393497653/10000000000 : ℝ)*X 2 1+(-520911659/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544840261/1250000000 : ℝ)*X 0 0+(4489224581/10000000000 : ℝ)*X 0 1+(423198051/1000000000 : ℝ)*X 0 2+(544840261/1250000000 : ℝ)*X 1 0+(4489224581/10000000000 : ℝ)*X 1 1+(423198051/1000000000 : ℝ)*X 1 2+(544840261/1250000000 : ℝ)*X 2 0+(4489224581/10000000000 : ℝ)*X 2 1+(423198051/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3131457762538847133793208679/298100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2060128227/100000000000000 : ℝ)*(base19) + (1918702669/100000000000000 : ℝ)*(base23) + (15118343/20000000000000 : ℝ)*(lower2) + (66387649/25000000000000 : ℝ)*(upper3) + (40227429/25000000000000 : ℝ)*(upper5) + (1162476350863953/20000000000000 : ℝ)*(major0) + (1162476350863953/20000000000000 : ℝ)*(major1) + (1162476350863953/20000000000000 : ℝ)*(major2) + (969670321078871/12500000000000 : ℝ)*(sp0) + (1551483144645459/20000000000000 : ℝ)*(sp1) + (7757415864652853/100000000000000 : ℝ)*(sp2) + (3867315616049517/100000000000000 : ℝ)*(sp3) + (11042944911/20000000000000 : ℝ)*(sp4) + (7439769263/25000000000000 : ℝ)*(sp7) + (3867345375126569/100000000000000 : ℝ)*(f.failure) + (7757417783355523/100000000000000 : ℝ)*(f.sum) + (514477334597/745250000000000000000000000 : ℝ)*base65 + (10025586576583432369/596200000000000000000000000000000 : ℝ)*base67 + (13361025076878432369/596200000000000000000000000000000 : ℝ)*base69 + (13457594247545632369/596200000000000000000000000000000 : ℝ)*base71 + (177255931123/596200000000000000000000000 : ℝ)*base73 + (24643655879198232369/596200000000000000000000000000000 : ℝ)*base75 + (17614165732255232369/596200000000000000000000000000000 : ℝ)*base77 + (18593707595979832369/596200000000000000000000000000000 : ℝ)*base79 + (8225132947649/2981000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (84344747/10000000000000000000000 : ℝ)*base90 + (84344747/10000000000000000000000 : ℝ)*base92 + (84344747/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90229396747269251031857673/13550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (956136783/100000000000000 : ℝ)*(base19) + (272384969/25000000000000 : ℝ)*(base23) + (5557201/6250000000000 : ℝ)*(upper3) + (36011183/100000000000000 : ℝ)*(lower4) + (24186513/20000000000000 : ℝ)*(upper5) + (1168491931599663/20000000000000 : ℝ)*(major0) + (1168491931599663/20000000000000 : ℝ)*(major1) + (1168491931599663/20000000000000 : ℝ)*(major2) + (13578987133/50000000000000 : ℝ)*(sp1) + (16399635591/50000000000000 : ℝ)*(sp2) + (243673780822703/3125000000000 : ℝ)*(sp4) + (7797532872215447/100000000000000 : ℝ)*(sp5) + (7797527097515439/100000000000000 : ℝ)*(sp6) + (971839526925897/25000000000000 : ℝ)*(sp7) + (971839526925897/25000000000000 : ℝ)*(f.failure) + (243673780822703/3125000000000 : ℝ)*(f.sum) + (804581831823/135500000000000000000000000 : ℝ)*base66 + (515193844066364109/54200000000000000000000000000000 : ℝ)*base67 + (553150605091164109/54200000000000000000000000000000 : ℝ)*base69 + (102501585259035891/54200000000000000000000000000000 : ℝ)*base72 + (78704113437/135500000000000000000000000 : ℝ)*base74 + (2235348872533764109/54200000000000000000000000000000 : ℝ)*base75 + (305370606384764109/54200000000000000000000000000000 : ℝ)*base77 + (704538496020964109/54200000000000000000000000000000 : ℝ)*base79 + (672153013577/135500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (203211/2500000000000000000000 : ℝ)*base90 + (203211/2500000000000000000000 : ℝ)*base92 + (203211/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1184_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1184_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1184_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16381/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1157/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1184_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1184_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1184_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16381/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1157/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1184_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
