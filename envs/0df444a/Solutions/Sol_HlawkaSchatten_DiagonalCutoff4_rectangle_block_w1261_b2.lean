-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1261_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:54:22.125572+00:00
-- url     : https://prove2.me/submissions/d505238f-3343-41af-90c2-817b268d619b

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
theorem support_rectangle_w1261_s6_0 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16493999/78125000 : ℝ)*x 0 + (1078203059/2000000000 : ℝ)*x 1 + (2633649861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16493999/78125000 : ℝ)^4227 ≤ (12840734951691/100000000000000 : ℝ)^3203 := by
    have hnat : (16493999 : ℕ)^4227*100000000000000^3203 ≤ 12840734951691^3203*78125000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16493999 78125000 12840734951691 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078203059/2000000000 : ℝ)^4227 ≤ (2765448564107/6250000000000 : ℝ)^3203 := by
    have hnat : (1078203059 : ℕ)^4227*6250000000000^3203 ≤ 2765448564107^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078203059 2000000000 2765448564107 6250000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633649861/5000000000 : ℝ)^4227 ≤ (42912088010361/100000000000000 : ℝ)^3203 := by
    have hnat : (2633649861 : ℕ)^4227*100000000000000^3203 ≤ 42912088010361^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633649861 5000000000 42912088010361 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16493999/78125000 : ℝ), (1078203059/2000000000 : ℝ), (2633649861/5000000000 : ℝ)] ![(12840734951691/100000000000000 : ℝ), (2765448564107/6250000000000 : ℝ), (42912088010361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16493999/78125000 : ℝ)|^4227 ≤ (12840734951691/100000000000000 : ℝ)^3203
        have hw : |(-16493999/78125000 : ℝ)|=(16493999/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078203059/2000000000 : ℝ)|^4227 ≤ (2765448564107/6250000000000 : ℝ)^3203
        have hw : |(1078203059/2000000000 : ℝ)|=(1078203059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633649861/5000000000 : ℝ)|^4227 ≤ (42912088010361/100000000000000 : ℝ)^3203
        have hw : |(2633649861/5000000000 : ℝ)|=(2633649861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s6_1 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068849921/2000000000 : ℝ)*x 0 + (-2173956867/10000000000 : ℝ)*x 1 + (1053459943/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068849921/2000000000 : ℝ)^4227 ≤ (21870668126361/50000000000000 : ℝ)^3203 := by
    have hnat : (1068849921 : ℕ)^4227*50000000000000^3203 ≤ 21870668126361^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068849921 2000000000 21870668126361 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173956867/10000000000 : ℝ)^4227 ≤ (41708049343/312500000000 : ℝ)^3203 := by
    have hnat : (2173956867 : ℕ)^4227*312500000000^3203 ≤ 41708049343^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173956867 10000000000 41708049343 312500000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053459943/2000000000 : ℝ)^4227 ≤ (429120879351/1000000000000 : ℝ)^3203 := by
    have hnat : (1053459943 : ℕ)^4227*1000000000000^3203 ≤ 429120879351^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053459943 2000000000 429120879351 1000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068849921/2000000000 : ℝ), (-2173956867/10000000000 : ℝ), (1053459943/2000000000 : ℝ)] ![(21870668126361/50000000000000 : ℝ), (41708049343/312500000000 : ℝ), (429120879351/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068849921/2000000000 : ℝ)|^4227 ≤ (21870668126361/50000000000000 : ℝ)^3203
        have hw : |(1068849921/2000000000 : ℝ)|=(1068849921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173956867/10000000000 : ℝ)|^4227 ≤ (41708049343/312500000000 : ℝ)^3203
        have hw : |(-2173956867/10000000000 : ℝ)|=(2173956867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053459943/2000000000 : ℝ)|^4227 ≤ (429120879351/1000000000000 : ℝ)^3203
        have hw : |(1053459943/2000000000 : ℝ)|=(1053459943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s6_2 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344249613/10000000000 : ℝ)*x 0 + (1053459943/2000000000 : ℝ)*x 1 + (-1086978429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344249613/10000000000 : ℝ)^4227 ≤ (43741336339133/100000000000000 : ℝ)^3203 := by
    have hnat : (5344249613 : ℕ)^4227*100000000000000^3203 ≤ 43741336339133^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344249613 10000000000 43741336339133 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053459943/2000000000 : ℝ)^4227 ≤ (429120879351/1000000000000 : ℝ)^3203 := by
    have hnat : (1053459943 : ℕ)^4227*1000000000000^3203 ≤ 429120879351^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053459943 2000000000 429120879351 1000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086978429/5000000000 : ℝ)^4227 ≤ (13346575716841/100000000000000 : ℝ)^3203 := by
    have hnat : (1086978429 : ℕ)^4227*100000000000000^3203 ≤ 13346575716841^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086978429 5000000000 13346575716841 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344249613/10000000000 : ℝ), (1053459943/2000000000 : ℝ), (-1086978429/5000000000 : ℝ)] ![(43741336339133/100000000000000 : ℝ), (429120879351/1000000000000 : ℝ), (13346575716841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344249613/10000000000 : ℝ)|^4227 ≤ (43741336339133/100000000000000 : ℝ)^3203
        have hw : |(5344249613/10000000000 : ℝ)|=(5344249613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053459943/2000000000 : ℝ)|^4227 ≤ (429120879351/1000000000000 : ℝ)^3203
        have hw : |(1053459943/2000000000 : ℝ)|=(1053459943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086978429/5000000000 : ℝ)|^4227 ≤ (13346575716841/100000000000000 : ℝ)^3203
        have hw : |(-1086978429/5000000000 : ℝ)|=(1086978429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s6_3 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (869633081/2000000000 : ℝ)*x 0 + (4223987607/10000000000 : ℝ)*x 1 + (559484303/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869633081/2000000000 : ℝ)^4227 ≤ (16658749791613/50000000000000 : ℝ)^3203 := by
    have hnat : (869633081 : ℕ)^4227*50000000000000^3203 ≤ 16658749791613^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869633081 2000000000 16658749791613 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223987607/10000000000 : ℝ)^4227 ≤ (32067570387199/100000000000000 : ℝ)^3203 := by
    have hnat : (4223987607 : ℕ)^4227*100000000000000^3203 ≤ 32067570387199^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223987607 10000000000 32067570387199 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559484303/1250000000 : ℝ)^4227 ≤ (8653732501879/25000000000000 : ℝ)^3203 := by
    have hnat : (559484303 : ℕ)^4227*25000000000000^3203 ≤ 8653732501879^3203*1250000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559484303 1250000000 8653732501879 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869633081/2000000000 : ℝ), (4223987607/10000000000 : ℝ), (559484303/1250000000 : ℝ)] ![(16658749791613/50000000000000 : ℝ), (32067570387199/100000000000000 : ℝ), (8653732501879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869633081/2000000000 : ℝ)|^4227 ≤ (16658749791613/50000000000000 : ℝ)^3203
        have hw : |(869633081/2000000000 : ℝ)|=(869633081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223987607/10000000000 : ℝ)|^4227 ≤ (32067570387199/100000000000000 : ℝ)^3203
        have hw : |(4223987607/10000000000 : ℝ)|=(4223987607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559484303/1250000000 : ℝ)|^4227 ≤ (8653732501879/25000000000000 : ℝ)^3203
        have hw : |(559484303/1250000000 : ℝ)|=(559484303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s6_4 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2111236523/10000000000 : ℝ)*x 0 + (2633806389/5000000000 : ℝ)*x 1 + (5390701101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111236523/10000000000 : ℝ)^4227 ≤ (12840772283217/100000000000000 : ℝ)^3203 := by
    have hnat : (2111236523 : ℕ)^4227*100000000000000^3203 ≤ 12840772283217^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111236523 10000000000 12840772283217 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633806389/5000000000 : ℝ)^4227 ≤ (42915453847377/100000000000000 : ℝ)^3203 := by
    have hnat : (2633806389 : ℕ)^4227*100000000000000^3203 ≤ 42915453847377^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633806389 5000000000 42915453847377 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390701101/10000000000 : ℝ)^4227 ≤ (8848754770343/20000000000000 : ℝ)^3203 := by
    have hnat : (5390701101 : ℕ)^4227*20000000000000^3203 ≤ 8848754770343^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390701101 10000000000 8848754770343 20000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2111236523/10000000000 : ℝ), (2633806389/5000000000 : ℝ), (5390701101/10000000000 : ℝ)] ![(12840772283217/100000000000000 : ℝ), (42915453847377/100000000000000 : ℝ), (8848754770343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2111236523/10000000000 : ℝ)|^4227 ≤ (12840772283217/100000000000000 : ℝ)^3203
        have hw : |(-2111236523/10000000000 : ℝ)|=(2111236523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633806389/5000000000 : ℝ)|^4227 ≤ (42915453847377/100000000000000 : ℝ)^3203
        have hw : |(2633806389/5000000000 : ℝ)|=(2633806389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390701101/10000000000 : ℝ)|^4227 ≤ (8848754770343/20000000000000 : ℝ)^3203
        have hw : |(5390701101/10000000000 : ℝ)|=(5390701101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s6_5 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212505713/400000000 : ℝ)*x 0 + (-512638869/2500000000 : ℝ)*x 1 + (2695350551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212505713/400000000 : ℝ)^4227 ≤ (10850065378549/25000000000000 : ℝ)^3203 := by
    have hnat : (212505713 : ℕ)^4227*25000000000000^3203 ≤ 10850065378549^3203*400000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212505713 400000000 10850065378549 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512638869/2500000000 : ℝ)^4227 ≤ (12355964614143/100000000000000 : ℝ)^3203 := by
    have hnat : (512638869 : ℕ)^4227*100000000000000^3203 ≤ 12355964614143^3203*2500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512638869 2500000000 12355964614143 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695350551/5000000000 : ℝ)^4227 ≤ (22121886931273/50000000000000 : ℝ)^3203 := by
    have hnat : (2695350551 : ℕ)^4227*50000000000000^3203 ≤ 22121886931273^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695350551 5000000000 22121886931273 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212505713/400000000 : ℝ), (-512638869/2500000000 : ℝ), (2695350551/5000000000 : ℝ)] ![(10850065378549/25000000000000 : ℝ), (12355964614143/100000000000000 : ℝ), (22121886931273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212505713/400000000 : ℝ)|^4227 ≤ (10850065378549/25000000000000 : ℝ)^3203
        have hw : |(212505713/400000000 : ℝ)|=(212505713/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-512638869/2500000000 : ℝ)|^4227 ≤ (12355964614143/100000000000000 : ℝ)^3203
        have hw : |(-512638869/2500000000 : ℝ)|=(512638869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695350551/5000000000 : ℝ)|^4227 ≤ (22121886931273/50000000000000 : ℝ)^3203
        have hw : |(2695350551/5000000000 : ℝ)|=(2695350551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s6_6 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664080353/1250000000 : ℝ)*x 0 + (2695350551/5000000000 : ℝ)*x 1 + (-512638869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664080353/1250000000 : ℝ)^4227 ≤ (8680052300683/20000000000000 : ℝ)^3203 := by
    have hnat : (664080353 : ℕ)^4227*20000000000000^3203 ≤ 8680052300683^3203*1250000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664080353 1250000000 8680052300683 20000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695350551/5000000000 : ℝ)^4227 ≤ (22121886931273/50000000000000 : ℝ)^3203 := by
    have hnat : (2695350551 : ℕ)^4227*50000000000000^3203 ≤ 22121886931273^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695350551 5000000000 22121886931273 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512638869/2500000000 : ℝ)^4227 ≤ (12355964614143/100000000000000 : ℝ)^3203 := by
    have hnat : (512638869 : ℕ)^4227*100000000000000^3203 ≤ 12355964614143^3203*2500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512638869 2500000000 12355964614143 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664080353/1250000000 : ℝ), (2695350551/5000000000 : ℝ), (-512638869/2500000000 : ℝ)] ![(8680052300683/20000000000000 : ℝ), (22121886931273/50000000000000 : ℝ), (12355964614143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664080353/1250000000 : ℝ)|^4227 ≤ (8680052300683/20000000000000 : ℝ)^3203
        have hw : |(664080353/1250000000 : ℝ)|=(664080353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695350551/5000000000 : ℝ)|^4227 ≤ (22121886931273/50000000000000 : ℝ)^3203
        have hw : |(2695350551/5000000000 : ℝ)|=(2695350551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512638869/2500000000 : ℝ)|^4227 ≤ (12355964614143/100000000000000 : ℝ)^3203
        have hw : |(-512638869/2500000000 : ℝ)|=(512638869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s6_7 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1087043717/2500000000 : ℝ)*x 0 + (895047407/2000000000 : ℝ)*x 1 + (33004901/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087043717/2500000000 : ℝ)^4227 ≤ (33317595274127/100000000000000 : ℝ)^3203 := by
    have hnat : (1087043717 : ℕ)^4227*100000000000000^3203 ≤ 33317595274127^3203*2500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087043717 2500000000 33317595274127 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895047407/2000000000 : ℝ)^4227 ≤ (17304212441969/50000000000000 : ℝ)^3203 := by
    have hnat : (895047407 : ℕ)^4227*50000000000000^3203 ≤ 17304212441969^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895047407 2000000000 17304212441969 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33004901/78125000 : ℝ)^4227 ≤ (32073979823731/100000000000000 : ℝ)^3203 := by
    have hnat : (33004901 : ℕ)^4227*100000000000000^3203 ≤ 32073979823731^3203*78125000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33004901 78125000 32073979823731 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087043717/2500000000 : ℝ), (895047407/2000000000 : ℝ), (33004901/78125000 : ℝ)] ![(33317595274127/100000000000000 : ℝ), (17304212441969/50000000000000 : ℝ), (32073979823731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087043717/2500000000 : ℝ)|^4227 ≤ (33317595274127/100000000000000 : ℝ)^3203
        have hw : |(1087043717/2500000000 : ℝ)|=(1087043717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895047407/2000000000 : ℝ)|^4227 ≤ (17304212441969/50000000000000 : ℝ)^3203
        have hw : |(895047407/2000000000 : ℝ)|=(895047407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33004901/78125000 : ℝ)|^4227 ≤ (32073979823731/100000000000000 : ℝ)^3203
        have hw : |(33004901/78125000 : ℝ)|=(33004901/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1261_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11497/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7059/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7069/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5739/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7069/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5739/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7069/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5739/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7069/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5739/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7069/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5739/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7069/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5739/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5739/50000 : ℝ) ^ (8453/2048 : ℝ) ≤ (823252253249581/6250000000000000000 : ℝ) := by
    have hpowers : (5739/50000 : ℝ)^8453 ≤ (823252253249581/6250000000000000000 : ℝ)^2048 := by
      have hnat : (5739 : ℕ)^8453*6250000000000000000^2048 ≤ 823252253249581^2048*50000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5739 50000 823252253249581 6250000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5739/50000 : ℝ)) (X := (823252253249581/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7069/50000 : ℝ) ^ (8453/2048 : ℝ) ≤ (311369563871309/1000000000000000000 : ℝ) := by
    have hpowers : (7069/50000 : ℝ)^8453 ≤ (311369563871309/1000000000000000000 : ℝ)^2048 := by
      have hnat : (7069 : ℕ)^8453*1000000000000000000^2048 ≤ 311369563871309^2048*50000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7069 50000 311369563871309 1000000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7069/50000 : ℝ)) (X := (311369563871309/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125823252253249581/3125000000000000000 : ℝ) ≤ (400025528108669/400000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (3125823252253249581/3125000000000000000 : ℝ)^2048 ≤ (400025528108669/400000000000000 : ℝ)^8453 := by
      have hnat : (3125823252253249581 : ℕ)^2048*400000000000000^8453 ≤ 400025528108669^8453*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125823252253249581 3125000000000000000 400025528108669 400000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400025528108669/400000000000000 : ℝ)) (X := (3125823252253249581/3125000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011077248109781049/25000000000000000000 : ℝ) ≤ (50005366709289/50000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (25011077248109781049/25000000000000000000 : ℝ)^2048 ≤ (50005366709289/50000000000000 : ℝ)^8453 := by
      have hnat : (25011077248109781049 : ℕ)^2048*50000000000000^8453 ≤ 50005366709289^8453*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011077248109781049 25000000000000000000 50005366709289 50000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50005366709289/50000000000000 : ℝ)) (X := (25011077248109781049/25000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (500311369563871309/500000000000000000 : ℝ) ≤ (80012067847991/80000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (500311369563871309/500000000000000000 : ℝ)^2048 ≤ (80012067847991/80000000000000 : ℝ)^8453 := by
      have hnat : (500311369563871309 : ℕ)^2048*80000000000000^8453 ≤ 80012067847991^8453*500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500311369563871309 500000000000000000 80012067847991 80000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80012067847991/80000000000000 : ℝ)) (X := (500311369563871309/500000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(823252253249581/6250000000000000000 : ℝ) ≤ ((66479271412759927/66500000000000000 : ℝ)+2*(17405565643/10640000000000 : ℝ)*(5739/50000 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (66479271412759927/66500000000000000 : ℝ)+2*(17405565643/10640000000000 : ℝ)*(5739/50000 : ℝ)=(400025528108669/400000000000000 : ℝ) by norm_num, show 1+2*(823252253249581/6250000000000000000 : ℝ)=(3125823252253249581/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(311369563871309/1000000000000000000 : ℝ)+(823252253249581/6250000000000000000 : ℝ) ≤ ((66479271412759927/66500000000000000 : ℝ)+(17405565643/10640000000000 : ℝ)*((7069/50000 : ℝ)+(5739/50000 : ℝ)))^(8453/2048 : ℝ) := by
    rw [show (66479271412759927/66500000000000000 : ℝ)+(17405565643/10640000000000 : ℝ)*((7069/50000 : ℝ)+(5739/50000 : ℝ))=(50005366709289/50000000000000 : ℝ) by norm_num, show 1+(311369563871309/1000000000000000000 : ℝ)+(823252253249581/6250000000000000000 : ℝ)=(25011077248109781049/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(311369563871309/1000000000000000000 : ℝ) ≤ ((66479271412759927/66500000000000000 : ℝ)+2*(17405565643/10640000000000 : ℝ)*(7069/50000 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (66479271412759927/66500000000000000 : ℝ)+2*(17405565643/10640000000000 : ℝ)*(7069/50000 : ℝ)=(80012067847991/80000000000000 : ℝ) by norm_num, show 1+2*(311369563871309/1000000000000000000 : ℝ)=(500311369563871309/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (66479271412759927/66500000000000000 : ℝ)*(X 1 0+X 2 0)+(17405565643/10640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (5739/50000 : ℝ)) (hi := (7069/50000 : ℝ)) (c := (66479271412759927/66500000000000000 : ℝ)) (alpha := (17405565643/10640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (66479271412759927/66500000000000000 : ℝ)*(X 0 1+X 2 1)+(17405565643/10640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (5739/50000 : ℝ)) (hi := (7069/50000 : ℝ)) (c := (66479271412759927/66500000000000000 : ℝ)) (alpha := (17405565643/10640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (66479271412759927/66500000000000000 : ℝ)*(X 0 2+X 1 2)+(17405565643/10640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (5739/50000 : ℝ)) (hi := (7069/50000 : ℝ)) (c := (66479271412759927/66500000000000000 : ℝ)) (alpha := (17405565643/10640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16493999/78125000 : ℝ)*X 0 0+(1078203059/2000000000 : ℝ)*X 0 1+(2633649861/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068849921/2000000000 : ℝ)*X 1 0+(-2173956867/10000000000 : ℝ)*X 1 1+(1053459943/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344249613/10000000000 : ℝ)*X 2 0+(1053459943/2000000000 : ℝ)*X 2 1+(-1086978429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869633081/2000000000 : ℝ)*X 0 0+(4223987607/10000000000 : ℝ)*X 0 1+(559484303/1250000000 : ℝ)*X 0 2+(869633081/2000000000 : ℝ)*X 1 0+(4223987607/10000000000 : ℝ)*X 1 1+(559484303/1250000000 : ℝ)*X 1 2+(869633081/2000000000 : ℝ)*X 2 0+(4223987607/10000000000 : ℝ)*X 2 1+(559484303/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2111236523/10000000000 : ℝ)*X 0 0+(2633806389/5000000000 : ℝ)*X 0 1+(5390701101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212505713/400000000 : ℝ)*X 1 0+(-512638869/2500000000 : ℝ)*X 1 1+(2695350551/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664080353/1250000000 : ℝ)*X 2 0+(2695350551/5000000000 : ℝ)*X 2 1+(-512638869/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087043717/2500000000 : ℝ)*X 0 0+(895047407/2000000000 : ℝ)*X 0 1+(33004901/78125000 : ℝ)*X 0 2+(1087043717/2500000000 : ℝ)*X 1 0+(895047407/2000000000 : ℝ)*X 1 1+(33004901/78125000 : ℝ)*X 1 2+(1087043717/2500000000 : ℝ)*X 2 0+(895047407/2000000000 : ℝ)*X 2 1+(33004901/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33544875892201736715729831/3325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (979644087/50000000000000 : ℝ)*(base19) + (1832309599/100000000000000 : ℝ)*(base23) + (74327053/100000000000000 : ℝ)*(lower2) + (31297493/12500000000000 : ℝ)*(upper3) + (20831041/12500000000000 : ℝ)*(upper5) + (6026629636735483/100000000000000 : ℝ)*(major0) + (6026629636735483/100000000000000 : ℝ)*(major1) + (6026629636735483/100000000000000 : ℝ)*(major2) + (8083112800020899/100000000000000 : ℝ)*(sp0) + (8083165235117511/100000000000000 : ℝ)*(sp1) + (4041582681048043/50000000000000 : ℝ)*(sp2) + (496257884164353/12500000000000 : ℝ)*(sp3) + (27197192393/50000000000000 : ℝ)*(sp4) + (28669460967/100000000000000 : ℝ)*(sp7) + (3970091742775791/100000000000000 : ℝ)*(f.failure) + (1616633438881137/20000000000000 : ℝ)*(f.sum) + (1854076585329/532000000000000000000000000 : ℝ)*base65 + (76229933869545991/6650000000000000000000000000000 : ℝ)*base67 + (28818344641045991/6650000000000000000000000000000 : ℝ)*base69 + (70316557661295991/6650000000000000000000000000000 : ℝ)*base71 + (2267376308663/532000000000000000000000000 : ℝ)*base74 + (50915829799395991/6650000000000000000000000000000 : ℝ)*base75 + (122293080267345991/6650000000000000000000000000000 : ℝ)*base77 + (59077124852495991/6650000000000000000000000000000 : ℝ)*base79 + (1758895383879/532000000000000000000000000 : ℝ)*base82 + (543977/2000000000000000000000 : ℝ)*base90 + (543977/2000000000000000000000 : ℝ)*base92 + (543977/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (129003397643076281344791/43750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133170181/25000000000000 : ℝ)*(base19) + (288960747/50000000000000 : ℝ)*(base23) + (59982233/100000000000000 : ℝ)*(upper3) + (859923/4000000000000 : ℝ)*(lower4) + (61741193/100000000000000 : ℝ)*(upper5) + (6057257652948357/100000000000000 : ℝ)*(major0) + (6057257652948357/100000000000000 : ℝ)*(major1) + (6057257652948357/100000000000000 : ℝ)*(major2) + (3020365711/20000000000000 : ℝ)*(sp1) + (8080727637/50000000000000 : ℝ)*(sp2) + (64993976061939/800000000000 : ℝ)*(sp4) + (1015528921654137/12500000000000 : ℝ)*(sp5) + (4062115134182803/50000000000000 : ℝ)*(sp6) + (1995134099933013/50000000000000 : ℝ)*(sp7) + (1995134099933013/50000000000000 : ℝ)*(f.failure) + (64993976061939/800000000000 : ℝ)*(f.sum) + (585911091/224000000000000000000000 : ℝ)*base66 + (4441344468264931/350000000000000000000000000000 : ℝ)*base67 + (1789509008214931/350000000000000000000000000000 : ℝ)*base69 + (5888380840785069/350000000000000000000000000000 : ℝ)*base72 + (38149885217/28000000000000000000000000 : ℝ)*base73 + (1368256448514931/350000000000000000000000000000 : ℝ)*base75 + (1054844493364931/350000000000000000000000000000 : ℝ)*base77 + (5405077528064931/350000000000000000000000000000 : ℝ)*base79 + (42633725411/28000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5569011/1000000000000000000000 : ℝ)*base90 + (5569011/1000000000000000000000 : ℝ)*base92 + (5569011/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1261_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1261_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1261_s7_0 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2111247501/10000000000 : ℝ)*x 0 + (2695417229/5000000000 : ℝ)*x 1 + (1316867559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111247501/10000000000 : ℝ)^4227 ≤ (1605107549861/12500000000000 : ℝ)^3203 := by
    have hnat : (2111247501 : ℕ)^4227*12500000000000^3203 ≤ 1605107549861^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111247501 10000000000 1605107549861 12500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695417229/5000000000 : ℝ)^4227 ≤ (22122609146271/50000000000000 : ℝ)^3203 := by
    have hnat : (2695417229 : ℕ)^4227*50000000000000^3203 ≤ 22122609146271^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695417229 5000000000 22122609146271 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316867559/2500000000 : ℝ)^4227 ≤ (42913921292107/100000000000000 : ℝ)^3203 := by
    have hnat : (1316867559 : ℕ)^4227*100000000000000^3203 ≤ 42913921292107^3203*2500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316867559 2500000000 42913921292107 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2111247501/10000000000 : ℝ), (2695417229/5000000000 : ℝ), (1316867559/2500000000 : ℝ)] ![(1605107549861/12500000000000 : ℝ), (22122609146271/50000000000000 : ℝ), (42913921292107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2111247501/10000000000 : ℝ)|^4227 ≤ (1605107549861/12500000000000 : ℝ)^3203
        have hw : |(-2111247501/10000000000 : ℝ)|=(2111247501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695417229/5000000000 : ℝ)|^4227 ≤ (22122609146271/50000000000000 : ℝ)^3203
        have hw : |(2695417229/5000000000 : ℝ)|=(2695417229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316867559/2500000000 : ℝ)|^4227 ≤ (42913921292107/100000000000000 : ℝ)^3203
        have hw : |(1316867559/2500000000 : ℝ)|=(1316867559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s7_1 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672101731/5000000000 : ℝ)*x 0 + (-1086895941/5000000000 : ℝ)*x 1 + (5267470399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672101731/5000000000 : ℝ)^4227 ≤ (43740837843753/100000000000000 : ℝ)^3203 := by
    have hnat : (2672101731 : ℕ)^4227*100000000000000^3203 ≤ 43740837843753^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672101731 5000000000 43740837843753 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086895941/5000000000 : ℝ)^4227 ≤ (13345239091337/100000000000000 : ℝ)^3203 := by
    have hnat : (1086895941 : ℕ)^4227*100000000000000^3203 ≤ 13345239091337^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086895941 5000000000 13345239091337 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267470399/10000000000 : ℝ)^4227 ≤ (42913923044611/100000000000000 : ℝ)^3203 := by
    have hnat : (5267470399 : ℕ)^4227*100000000000000^3203 ≤ 42913923044611^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267470399 10000000000 42913923044611 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672101731/5000000000 : ℝ), (-1086895941/5000000000 : ℝ), (5267470399/10000000000 : ℝ)] ![(43740837843753/100000000000000 : ℝ), (13345239091337/100000000000000 : ℝ), (42913923044611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672101731/5000000000 : ℝ)|^4227 ≤ (43740837843753/100000000000000 : ℝ)^3203
        have hw : |(2672101731/5000000000 : ℝ)|=(2672101731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1086895941/5000000000 : ℝ)|^4227 ≤ (13345239091337/100000000000000 : ℝ)^3203
        have hw : |(-1086895941/5000000000 : ℝ)|=(1086895941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267470399/10000000000 : ℝ)|^4227 ≤ (42913923044611/100000000000000 : ℝ)^3203
        have hw : |(5267470399/10000000000 : ℝ)|=(5267470399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s7_2 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344203491/10000000000 : ℝ)*x 0 + (210698811/400000000 : ℝ)*x 1 + (-271724001/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344203491/10000000000 : ℝ)^4227 ≤ (43740838156993/100000000000000 : ℝ)^3203 := by
    have hnat : (5344203491 : ℕ)^4227*100000000000000^3203 ≤ 43740838156993^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344203491 10000000000 43740838156993 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210698811/400000000 : ℝ)^4227 ≤ (21456960855709/50000000000000 : ℝ)^3203 := by
    have hnat : (210698811 : ℕ)^4227*50000000000000^3203 ≤ 21456960855709^3203*400000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210698811 400000000 21456960855709 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271724001/1250000000 : ℝ)^4227 ≤ (13345240112169/100000000000000 : ℝ)^3203 := by
    have hnat : (271724001 : ℕ)^4227*100000000000000^3203 ≤ 13345240112169^3203*1250000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271724001 1250000000 13345240112169 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344203491/10000000000 : ℝ), (210698811/400000000 : ℝ), (-271724001/1250000000 : ℝ)] ![(43740838156993/100000000000000 : ℝ), (21456960855709/50000000000000 : ℝ), (13345240112169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344203491/10000000000 : ℝ)|^4227 ≤ (43740838156993/100000000000000 : ℝ)^3203
        have hw : |(5344203491/10000000000 : ℝ)|=(5344203491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210698811/400000000 : ℝ)|^4227 ≤ (21456960855709/50000000000000 : ℝ)^3203
        have hw : |(210698811/400000000 : ℝ)|=(210698811/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271724001/1250000000 : ℝ)|^4227 ≤ (13345240112169/100000000000000 : ℝ)^3203
        have hw : |(-271724001/1250000000 : ℝ)|=(271724001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s7_3 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4348174663/10000000000 : ℝ)*x 0 + (2112171739/5000000000 : ℝ)*x 1 + (4475515901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348174663/10000000000 : ℝ)^4227 ≤ (4164699150143/12500000000000 : ℝ)^3203 := by
    have hnat : (4348174663 : ℕ)^4227*12500000000000^3203 ≤ 4164699150143^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348174663 10000000000 4164699150143 12500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112171739/5000000000 : ℝ)^4227 ≤ (32071135860411/100000000000000 : ℝ)^3203 := by
    have hnat : (2112171739 : ℕ)^4227*100000000000000^3203 ≤ 32071135860411^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112171739 5000000000 32071135860411 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475515901/10000000000 : ℝ)^4227 ≤ (4326408865487/12500000000000 : ℝ)^3203 := by
    have hnat : (4475515901 : ℕ)^4227*12500000000000^3203 ≤ 4326408865487^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475515901 10000000000 4326408865487 12500000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348174663/10000000000 : ℝ), (2112171739/5000000000 : ℝ), (4475515901/10000000000 : ℝ)] ![(4164699150143/12500000000000 : ℝ), (32071135860411/100000000000000 : ℝ), (4326408865487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348174663/10000000000 : ℝ)|^4227 ≤ (4164699150143/12500000000000 : ℝ)^3203
        have hw : |(4348174663/10000000000 : ℝ)|=(4348174663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112171739/5000000000 : ℝ)|^4227 ≤ (32071135860411/100000000000000 : ℝ)^3203
        have hw : |(2112171739/5000000000 : ℝ)|=(2112171739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475515901/10000000000 : ℝ)|^4227 ≤ (4326408865487/12500000000000 : ℝ)^3203
        have hw : |(4475515901/10000000000 : ℝ)|=(4475515901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s7_4 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055626027/5000000000 : ℝ)*x 0 + (2633890777/5000000000 : ℝ)*x 1 + (5390522057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055626027/5000000000 : ℝ)^4227 ≤ (6420448471949/50000000000000 : ℝ)^3203 := by
    have hnat : (1055626027 : ℕ)^4227*50000000000000^3203 ≤ 6420448471949^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055626027 5000000000 6420448471949 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633890777/5000000000 : ℝ)^4227 ≤ (21458634238697/50000000000000 : ℝ)^3203 := by
    have hnat : (2633890777 : ℕ)^4227*50000000000000^3203 ≤ 21458634238697^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633890777 5000000000 21458634238697 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390522057/10000000000 : ℝ)^4227 ≤ (11060458643857/25000000000000 : ℝ)^3203 := by
    have hnat : (5390522057 : ℕ)^4227*25000000000000^3203 ≤ 11060458643857^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390522057 10000000000 11060458643857 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055626027/5000000000 : ℝ), (2633890777/5000000000 : ℝ), (5390522057/10000000000 : ℝ)] ![(6420448471949/50000000000000 : ℝ), (21458634238697/50000000000000 : ℝ), (11060458643857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055626027/5000000000 : ℝ)|^4227 ≤ (6420448471949/50000000000000 : ℝ)^3203
        have hw : |(-1055626027/5000000000 : ℝ)|=(1055626027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633890777/5000000000 : ℝ)|^4227 ≤ (21458634238697/50000000000000 : ℝ)^3203
        have hw : |(2633890777/5000000000 : ℝ)|=(2633890777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390522057/10000000000 : ℝ)|^4227 ≤ (11060458643857/25000000000000 : ℝ)^3203
        have hw : |(5390522057/10000000000 : ℝ)|=(5390522057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s7_5 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531268659/1000000000 : ℝ)*x 0 + (-128171247/625000000 : ℝ)*x 1 + (53905221/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531268659/1000000000 : ℝ)^4227 ≤ (434007333431/1000000000000 : ℝ)^3203 := by
    have hnat : (531268659 : ℕ)^4227*1000000000000^3203 ≤ 434007333431^3203*1000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531268659 1000000000 434007333431 1000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128171247/625000000 : ℝ)^4227 ≤ (617871580107/5000000000000 : ℝ)^3203 := by
    have hnat : (128171247 : ℕ)^4227*5000000000000^3203 ≤ 617871580107^3203*625000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128171247 625000000 617871580107 5000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53905221/100000000 : ℝ)^4227 ≤ (44241835041171/100000000000000 : ℝ)^3203 := by
    have hnat : (53905221 : ℕ)^4227*100000000000000^3203 ≤ 44241835041171^3203*100000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53905221 100000000 44241835041171 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531268659/1000000000 : ℝ), (-128171247/625000000 : ℝ), (53905221/100000000 : ℝ)] ![(434007333431/1000000000000 : ℝ), (617871580107/5000000000000 : ℝ), (44241835041171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531268659/1000000000 : ℝ)|^4227 ≤ (434007333431/1000000000000 : ℝ)^3203
        have hw : |(531268659/1000000000 : ℝ)|=(531268659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128171247/625000000 : ℝ)|^4227 ≤ (617871580107/5000000000000 : ℝ)^3203
        have hw : |(-128171247/625000000 : ℝ)|=(128171247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53905221/100000000 : ℝ)|^4227 ≤ (44241835041171/100000000000000 : ℝ)^3203
        have hw : |(53905221/100000000 : ℝ)|=(53905221/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s7_6 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656343223/5000000000 : ℝ)*x 0 + (5390522189/10000000000 : ℝ)*x 1 + (-2050740027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656343223/5000000000 : ℝ)^4227 ≤ (43400731790639/100000000000000 : ℝ)^3203 := by
    have hnat : (2656343223 : ℕ)^4227*100000000000000^3203 ≤ 43400731790639^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656343223 5000000000 43400731790639 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390522189/10000000000 : ℝ)^4227 ≤ (884836720103/2000000000000 : ℝ)^3203 := by
    have hnat : (5390522189 : ℕ)^4227*2000000000000^3203 ≤ 884836720103^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390522189 10000000000 884836720103 2000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050740027/10000000000 : ℝ)^4227 ≤ (6178716099281/50000000000000 : ℝ)^3203 := by
    have hnat : (2050740027 : ℕ)^4227*50000000000000^3203 ≤ 6178716099281^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050740027 10000000000 6178716099281 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656343223/5000000000 : ℝ), (5390522189/10000000000 : ℝ), (-2050740027/10000000000 : ℝ)] ![(43400731790639/100000000000000 : ℝ), (884836720103/2000000000000 : ℝ), (6178716099281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656343223/5000000000 : ℝ)|^4227 ≤ (43400731790639/100000000000000 : ℝ)^3203
        have hw : |(2656343223/5000000000 : ℝ)|=(2656343223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390522189/10000000000 : ℝ)|^4227 ≤ (884836720103/2000000000000 : ℝ)^3203
        have hw : |(5390522189/10000000000 : ℝ)|=(5390522189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2050740027/10000000000 : ℝ)|^4227 ≤ (6178716099281/50000000000000 : ℝ)^3203
        have hw : |(-2050740027/10000000000 : ℝ)|=(2050740027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s7_7 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2174091829/5000000000 : ℝ)*x 0 + (894976371/2000000000 : ℝ)*x 1 + (528122529/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174091829/5000000000 : ℝ)^4227 ≤ (16658842079819/50000000000000 : ℝ)^3203 := by
    have hnat : (2174091829 : ℕ)^4227*50000000000000^3203 ≤ 16658842079819^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174091829 5000000000 16658842079819 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894976371/2000000000 : ℝ)^4227 ≤ (8651200020893/25000000000000 : ℝ)^3203 := by
    have hnat : (894976371 : ℕ)^4227*25000000000000^3203 ≤ 8651200020893^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894976371 2000000000 8651200020893 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528122529/1250000000 : ℝ)^4227 ≤ (32077515741339/100000000000000 : ℝ)^3203 := by
    have hnat : (528122529 : ℕ)^4227*100000000000000^3203 ≤ 32077515741339^3203*1250000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528122529 1250000000 32077515741339 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174091829/5000000000 : ℝ), (894976371/2000000000 : ℝ), (528122529/1250000000 : ℝ)] ![(16658842079819/50000000000000 : ℝ), (8651200020893/25000000000000 : ℝ), (32077515741339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174091829/5000000000 : ℝ)|^4227 ≤ (16658842079819/50000000000000 : ℝ)^3203
        have hw : |(2174091829/5000000000 : ℝ)|=(2174091829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(894976371/2000000000 : ℝ)|^4227 ≤ (8651200020893/25000000000000 : ℝ)^3203
        have hw : |(894976371/2000000000 : ℝ)|=(894976371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528122529/1250000000 : ℝ)|^4227 ≤ (32077515741339/100000000000000 : ℝ)^3203
        have hw : |(528122529/1250000000 : ℝ)|=(528122529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1261_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11501/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2823/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11497/100000 : ℝ) ^ (8453/2048 : ℝ) ≤ (13262264864031981/100000000000000000000 : ℝ) := by
    have hpowers : (11497/100000 : ℝ)^8453 ≤ (13262264864031981/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11497 : ℕ)^8453*100000000000000000000^2048 ≤ 13262264864031981^2048*100000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11497 100000 13262264864031981 100000000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11497/100000 : ℝ)) (X := (13262264864031981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7059/50000 : ℝ) ^ (8453/2048 : ℝ) ≤ (15477777981160947/50000000000000000000 : ℝ) := by
    have hpowers : (7059/50000 : ℝ)^8453 ≤ (15477777981160947/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7059 : ℕ)^8453*50000000000000000000^2048 ≤ 15477777981160947^2048*50000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7059 50000 15477777981160947 50000000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7059/50000 : ℝ)) (X := (15477777981160947/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013262264864031981/50000000000000000000 : ℝ) ≤ (10000642573983799/10000000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (50013262264864031981/50000000000000000000 : ℝ)^2048 ≤ (10000642573983799/10000000000000000 : ℝ)^8453 := by
      have hnat : (50013262264864031981 : ℕ)^2048*10000000000000000^8453 ≤ 10000642573983799^8453*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013262264864031981 50000000000000000000 10000642573983799 10000000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000642573983799/10000000000000000 : ℝ)) (X := (50013262264864031981/50000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (800353742566610831/800000000000000000 : ℝ) ≤ (1250133891710601/1250000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (800353742566610831/800000000000000000 : ℝ)^2048 ≤ (1250133891710601/1250000000000000 : ℝ)^8453 := by
      have hnat : (800353742566610831 : ℕ)^2048*1250000000000000^8453 ≤ 1250133891710601^8453*800000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800353742566610831 800000000000000000 1250133891710601 1250000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250133891710601/1250000000000000 : ℝ)) (X := (800353742566610831/800000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015477777981160947/25000000000000000000 : ℝ) ≤ (10001499693385817/10000000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (25015477777981160947/25000000000000000000 : ℝ)^2048 ≤ (10001499693385817/10000000000000000 : ℝ)^8453 := by
      have hnat : (25015477777981160947 : ℕ)^2048*10000000000000000^8453 ≤ 10001499693385817^8453*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015477777981160947 25000000000000000000 10001499693385817 10000000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001499693385817/10000000000000000 : ℝ)) (X := (25015477777981160947/25000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13262264864031981/100000000000000000000 : ℝ) ≤ ((26201829884646536233/26210000000000000000 : ℝ)+2*(428559701009/262100000000000 : ℝ)*(11497/100000 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (26201829884646536233/26210000000000000000 : ℝ)+2*(428559701009/262100000000000 : ℝ)*(11497/100000 : ℝ)=(10000642573983799/10000000000000000 : ℝ) by norm_num, show 1+2*(13262264864031981/100000000000000000000 : ℝ)=(50013262264864031981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15477777981160947/50000000000000000000 : ℝ)+(13262264864031981/100000000000000000000 : ℝ) ≤ ((26201829884646536233/26210000000000000000 : ℝ)+(428559701009/262100000000000 : ℝ)*((7059/50000 : ℝ)+(11497/100000 : ℝ)))^(8453/2048 : ℝ) := by
    rw [show (26201829884646536233/26210000000000000000 : ℝ)+(428559701009/262100000000000 : ℝ)*((7059/50000 : ℝ)+(11497/100000 : ℝ))=(1250133891710601/1250000000000000 : ℝ) by norm_num, show 1+(15477777981160947/50000000000000000000 : ℝ)+(13262264864031981/100000000000000000000 : ℝ)=(800353742566610831/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15477777981160947/50000000000000000000 : ℝ) ≤ ((26201829884646536233/26210000000000000000 : ℝ)+2*(428559701009/262100000000000 : ℝ)*(7059/50000 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (26201829884646536233/26210000000000000000 : ℝ)+2*(428559701009/262100000000000 : ℝ)*(7059/50000 : ℝ)=(10001499693385817/10000000000000000 : ℝ) by norm_num, show 1+2*(15477777981160947/50000000000000000000 : ℝ)=(25015477777981160947/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26201829884646536233/26210000000000000000 : ℝ)*(X 1 0+X 2 0)+(428559701009/262100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (11497/100000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (26201829884646536233/26210000000000000000 : ℝ)) (alpha := (428559701009/262100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26201829884646536233/26210000000000000000 : ℝ)*(X 0 1+X 2 1)+(428559701009/262100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (11497/100000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (26201829884646536233/26210000000000000000 : ℝ)) (alpha := (428559701009/262100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26201829884646536233/26210000000000000000 : ℝ)*(X 0 2+X 1 2)+(428559701009/262100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (11497/100000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (26201829884646536233/26210000000000000000 : ℝ)) (alpha := (428559701009/262100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2111247501/10000000000 : ℝ)*X 0 0+(2695417229/5000000000 : ℝ)*X 0 1+(1316867559/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672101731/5000000000 : ℝ)*X 1 0+(-1086895941/5000000000 : ℝ)*X 1 1+(5267470399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344203491/10000000000 : ℝ)*X 2 0+(210698811/400000000 : ℝ)*X 2 1+(-271724001/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348174663/10000000000 : ℝ)*X 0 0+(2112171739/5000000000 : ℝ)*X 0 1+(4475515901/10000000000 : ℝ)*X 0 2+(4348174663/10000000000 : ℝ)*X 1 0+(2112171739/5000000000 : ℝ)*X 1 1+(4475515901/10000000000 : ℝ)*X 1 2+(4348174663/10000000000 : ℝ)*X 2 0+(2112171739/5000000000 : ℝ)*X 2 1+(4475515901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1055626027/5000000000 : ℝ)*X 0 0+(2633890777/5000000000 : ℝ)*X 0 1+(5390522057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531268659/1000000000 : ℝ)*X 1 0+(-128171247/625000000 : ℝ)*X 1 1+(53905221/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656343223/5000000000 : ℝ)*X 2 0+(5390522189/10000000000 : ℝ)*X 2 1+(-2050740027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174091829/5000000000 : ℝ)*X 0 0+(894976371/2000000000 : ℝ)*X 0 1+(528122529/1250000000 : ℝ)*X 0 2+(2174091829/5000000000 : ℝ)*X 1 0+(894976371/2000000000 : ℝ)*X 1 1+(528122529/1250000000 : ℝ)*X 1 2+(2174091829/5000000000 : ℝ)*X 2 0+(894976371/2000000000 : ℝ)*X 2 1+(528122529/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44827872960220935336477/6552500000000000000000000000 : ℝ) := by norm_num
    linear_combination (310958967/25000000000000 : ℝ)*(base19) + (208775877/20000000000000 : ℝ)*(base23) + (201489143/100000000000000 : ℝ)*(lower2) + (18965649/5000000000000 : ℝ)*(upper3) + (8890063/12500000000000 : ℝ)*(lower4) + (755470463941229/12500000000000 : ℝ)*(major0) + (755470463941229/12500000000000 : ℝ)*(major1) + (755470463941229/12500000000000 : ℝ)*(major2) + (8106120490031471/100000000000000 : ℝ)*(sp0) + (8106146995987577/100000000000000 : ℝ)*(sp1) + (405307359797203/5000000000000 : ℝ)*(sp2) + (796269829385237/20000000000000 : ℝ)*(sp3) + (13874895987/50000000000000 : ℝ)*(sp4) + (149041327/500000000000 : ℝ)*(sp7) + (124418092349737/3125000000000 : ℝ)*(f.failure) + (1621229647964689/20000000000000 : ℝ)*(f.sum) + (358401600791/102382812500000000000000000 : ℝ)*base65 + (427521026409150357/327625000000000000000000000000000 : ℝ)*base67 + (1334526300055224643/327625000000000000000000000000000 : ℝ)*base70 + (1519296076888974643/327625000000000000000000000000000 : ℝ)*base72 + (215151437923/3276250000000000000000000000 : ℝ)*base74 + (1150553374453650357/327625000000000000000000000000000 : ℝ)*base75 + (3937274034789724643/327625000000000000000000000000000 : ℝ)*base78 + (667623895345900357/327625000000000000000000000000000 : ℝ)*base79 + (58866343205037/13105000000000000000000000000 : ℝ)*base82 + (170239/62500000000000000000 : ℝ)*base90 + (170239/62500000000000000000 : ℝ)*base92 + (170239/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7154772487351046005373826723/655250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (227707673/12500000000000 : ℝ)*(base19) + (1990116009/100000000000000 : ℝ)*(base23) + (168988709/100000000000000 : ℝ)*(upper3) + (48099319/25000000000000 : ℝ)*(lower4) + (156067751/100000000000000 : ℝ)*(upper5) + (3037208342813177/50000000000000 : ℝ)*(major0) + (3037208342813177/50000000000000 : ℝ)*(major1) + (3037208342813177/50000000000000 : ℝ)*(major2) + (143381867/250000000000 : ℝ)*(sp1) + (61927073343/100000000000000 : ℝ)*(sp2) + (203681528844713/2500000000000 : ℝ)*(sp4) + (509200123711271/6250000000000 : ℝ)*(sp5) + (63649978410931/781250000000 : ℝ)*(sp6) + (200078592674627/5000000000000 : ℝ)*(sp7) + (200078592674627/5000000000000 : ℝ)*(f.failure) + (203681528844713/2500000000000 : ℝ)*(f.sum) + (23899804545493/6552500000000000000000000000 : ℝ)*base65 + (24751393231050357759/1310500000000000000000000000000000 : ℝ)*base68 + (19584921461020357759/1310500000000000000000000000000000 : ℝ)*base70 + (4921700581540357759/1310500000000000000000000000000000 : ℝ)*base72 + (16874496098377/6552500000000000000000000000 : ℝ)*base74 + (7041800292799642241/1310500000000000000000000000000000 : ℝ)*base75 + (7271451551399142241/1310500000000000000000000000000000 : ℝ)*base77 + (34091795886118857759/1310500000000000000000000000000000 : ℝ)*base80 + (20148968876907/6552500000000000000000000000 : ℝ)*base82 + (937931/100000000000000000000 : ℝ)*base89 + (937931/100000000000000000000 : ℝ)*base91 + (937931/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1261_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11501/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1261_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1261_s8_0 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-42224941/200000000 : ℝ)*x 0 + (1347701001/2500000000 : ℝ)*x 1 + (5267501253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42224941/200000000 : ℝ)^4227 ≤ (12840856778903/100000000000000 : ℝ)^3203 := by
    have hnat : (42224941 : ℕ)^4227*100000000000000^3203 ≤ 12840856778903^3203*200000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42224941 200000000 12840856778903 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347701001/2500000000 : ℝ)^4227 ≤ (22122444216289/50000000000000 : ℝ)^3203 := by
    have hnat : (1347701001 : ℕ)^4227*50000000000000^3203 ≤ 22122444216289^3203*2500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347701001 2500000000 22122444216289 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267501253/10000000000 : ℝ)^4227 ≤ (42914254773509/100000000000000 : ℝ)^3203 := by
    have hnat : (5267501253 : ℕ)^4227*100000000000000^3203 ≤ 42914254773509^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267501253 10000000000 42914254773509 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42224941/200000000 : ℝ), (1347701001/2500000000 : ℝ), (5267501253/10000000000 : ℝ)] ![(12840856778903/100000000000000 : ℝ), (22122444216289/50000000000000 : ℝ), (42914254773509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42224941/200000000 : ℝ)|^4227 ≤ (12840856778903/100000000000000 : ℝ)^3203
        have hw : |(-42224941/200000000 : ℝ)|=(42224941/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347701001/2500000000 : ℝ)|^4227 ≤ (22122444216289/50000000000000 : ℝ)^3203
        have hw : |(1347701001/2500000000 : ℝ)|=(1347701001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267501253/10000000000 : ℝ)|^4227 ≤ (42914254773509/100000000000000 : ℝ)^3203
        have hw : |(5267501253/10000000000 : ℝ)|=(5267501253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s8_1 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344196807/10000000000 : ℝ)*x 0 + (-2173759507/10000000000 : ℝ)*x 1 + (5267501481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344196807/10000000000 : ℝ)^4227 ≤ (21870382980277/50000000000000 : ℝ)^3203 := by
    have hnat : (5344196807 : ℕ)^4227*50000000000000^3203 ≤ 21870382980277^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344196807 10000000000 21870382980277 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173759507/10000000000 : ℝ)^4227 ≤ (2668995358973/20000000000000 : ℝ)^3203 := by
    have hnat : (2173759507 : ℕ)^4227*20000000000000^3203 ≤ 2668995358973^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173759507 10000000000 2668995358973 20000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267501481/10000000000 : ℝ)^4227 ≤ (42914257224869/100000000000000 : ℝ)^3203 := by
    have hnat : (5267501481 : ℕ)^4227*100000000000000^3203 ≤ 42914257224869^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267501481 10000000000 42914257224869 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344196807/10000000000 : ℝ), (-2173759507/10000000000 : ℝ), (5267501481/10000000000 : ℝ)] ![(21870382980277/50000000000000 : ℝ), (2668995358973/20000000000000 : ℝ), (42914257224869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344196807/10000000000 : ℝ)|^4227 ≤ (21870382980277/50000000000000 : ℝ)^3203
        have hw : |(5344196807/10000000000 : ℝ)|=(5344196807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173759507/10000000000 : ℝ)|^4227 ≤ (2668995358973/20000000000000 : ℝ)^3203
        have hw : |(-2173759507/10000000000 : ℝ)|=(2173759507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267501481/10000000000 : ℝ)|^4227 ≤ (42914257224869/100000000000000 : ℝ)^3203
        have hw : |(5267501481/10000000000 : ℝ)|=(5267501481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s8_2 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344196971/10000000000 : ℝ)*x 0 + (5267501287/10000000000 : ℝ)*x 1 + (-1086879773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344196971/10000000000 : ℝ)^4227 ≤ (2187038386599/5000000000000 : ℝ)^3203 := by
    have hnat : (5344196971 : ℕ)^4227*5000000000000^3203 ≤ 2187038386599^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344196971 10000000000 2187038386599 5000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267501287/10000000000 : ℝ)^4227 ≤ (21457127569531/50000000000000 : ℝ)^3203 := by
    have hnat : (5267501287 : ℕ)^4227*50000000000000^3203 ≤ 21457127569531^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267501287 10000000000 21457127569531 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086879773/5000000000 : ℝ)^4227 ≤ (3336244277709/25000000000000 : ℝ)^3203 := by
    have hnat : (1086879773 : ℕ)^4227*25000000000000^3203 ≤ 3336244277709^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086879773 5000000000 3336244277709 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344196971/10000000000 : ℝ), (5267501287/10000000000 : ℝ), (-1086879773/5000000000 : ℝ)] ![(2187038386599/5000000000000 : ℝ), (21457127569531/50000000000000 : ℝ), (3336244277709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344196971/10000000000 : ℝ)|^4227 ≤ (2187038386599/5000000000000 : ℝ)^3203
        have hw : |(5344196971/10000000000 : ℝ)|=(5344196971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267501287/10000000000 : ℝ)|^4227 ≤ (21457127569531/50000000000000 : ℝ)^3203
        have hw : |(5267501287/10000000000 : ℝ)|=(5267501287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086879773/5000000000 : ℝ)|^4227 ≤ (3336244277709/25000000000000 : ℝ)^3203
        have hw : |(-1086879773/5000000000 : ℝ)|=(1086879773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s8_3 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4348176069/10000000000 : ℝ)*x 0 + (528050841/1250000000 : ℝ)*x 1 + (895090483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348176069/10000000000 : ℝ)^4227 ≤ (33317607418777/100000000000000 : ℝ)^3203 := by
    have hnat : (4348176069 : ℕ)^4227*100000000000000^3203 ≤ 33317607418777^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348176069 10000000000 33317607418777 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528050841/1250000000 : ℝ)^4227 ≤ (32071769572507/100000000000000 : ℝ)^3203 := by
    have hnat : (528050841 : ℕ)^4227*100000000000000^3203 ≤ 32071769572507^3203*1250000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528050841 1250000000 32071769572507 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895090483/2000000000 : ℝ)^4227 ≤ (34610622995921/100000000000000 : ℝ)^3203 := by
    have hnat : (895090483 : ℕ)^4227*100000000000000^3203 ≤ 34610622995921^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895090483 2000000000 34610622995921 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348176069/10000000000 : ℝ), (528050841/1250000000 : ℝ), (895090483/2000000000 : ℝ)] ![(33317607418777/100000000000000 : ℝ), (32071769572507/100000000000000 : ℝ), (34610622995921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348176069/10000000000 : ℝ)|^4227 ≤ (33317607418777/100000000000000 : ℝ)^3203
        have hw : |(4348176069/10000000000 : ℝ)|=(4348176069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528050841/1250000000 : ℝ)|^4227 ≤ (32071769572507/100000000000000 : ℝ)^3203
        have hw : |(528050841/1250000000 : ℝ)|=(528050841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895090483/2000000000 : ℝ)|^4227 ≤ (34610622995921/100000000000000 : ℝ)^3203
        have hw : |(895090483/2000000000 : ℝ)|=(895090483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s8_4 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-422250299/2000000000 : ℝ)*x 0 + (658476551/1250000000 : ℝ)*x 1 + (2695245921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422250299/2000000000 : ℝ)^4227 ≤ (12840892457039/100000000000000 : ℝ)^3203 := by
    have hnat : (422250299 : ℕ)^4227*100000000000000^3203 ≤ 12840892457039^3203*2000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422250299 2000000000 12840892457039 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658476551/1250000000 : ℝ)^4227 ≤ (10729400053139/25000000000000 : ℝ)^3203 := by
    have hnat : (658476551 : ℕ)^4227*25000000000000^3203 ≤ 10729400053139^3203*1250000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658476551 1250000000 10729400053139 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695245921/5000000000 : ℝ)^4227 ≤ (22120753655117/50000000000000 : ℝ)^3203 := by
    have hnat : (2695245921 : ℕ)^4227*50000000000000^3203 ≤ 22120753655117^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695245921 5000000000 22120753655117 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422250299/2000000000 : ℝ), (658476551/1250000000 : ℝ), (2695245921/5000000000 : ℝ)] ![(12840892457039/100000000000000 : ℝ), (10729400053139/25000000000000 : ℝ), (22120753655117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422250299/2000000000 : ℝ)|^4227 ≤ (12840892457039/100000000000000 : ℝ)^3203
        have hw : |(-422250299/2000000000 : ℝ)|=(422250299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658476551/1250000000 : ℝ)|^4227 ≤ (10729400053139/25000000000000 : ℝ)^3203
        have hw : |(658476551/1250000000 : ℝ)|=(658476551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695245921/5000000000 : ℝ)|^4227 ≤ (22120753655117/50000000000000 : ℝ)^3203
        have hw : |(2695245921/5000000000 : ℝ)|=(2695245921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s8_5 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656347723/5000000000 : ℝ)*x 0 + (-1025384579/5000000000 : ℝ)*x 1 + (2695245921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656347723/5000000000 : ℝ)^4227 ≤ (43400828819471/100000000000000 : ℝ)^3203 := by
    have hnat : (2656347723 : ℕ)^4227*100000000000000^3203 ≤ 43400828819471^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656347723 5000000000 43400828819471 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025384579/5000000000 : ℝ)^4227 ≤ (12357663857637/100000000000000 : ℝ)^3203 := by
    have hnat : (1025384579 : ℕ)^4227*100000000000000^3203 ≤ 12357663857637^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025384579 5000000000 12357663857637 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695245921/5000000000 : ℝ)^4227 ≤ (22120753655117/50000000000000 : ℝ)^3203 := by
    have hnat : (2695245921 : ℕ)^4227*50000000000000^3203 ≤ 22120753655117^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695245921 5000000000 22120753655117 50000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656347723/5000000000 : ℝ), (-1025384579/5000000000 : ℝ), (2695245921/5000000000 : ℝ)] ![(43400828819471/100000000000000 : ℝ), (12357663857637/100000000000000 : ℝ), (22120753655117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656347723/5000000000 : ℝ)|^4227 ≤ (43400828819471/100000000000000 : ℝ)^3203
        have hw : |(2656347723/5000000000 : ℝ)|=(2656347723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025384579/5000000000 : ℝ)|^4227 ≤ (12357663857637/100000000000000 : ℝ)^3203
        have hw : |(-1025384579/5000000000 : ℝ)|=(1025384579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695245921/5000000000 : ℝ)|^4227 ≤ (22120753655117/50000000000000 : ℝ)^3203
        have hw : |(2695245921/5000000000 : ℝ)|=(2695245921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s8_6 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664086931/1250000000 : ℝ)*x 0 + (16845287/31250000 : ℝ)*x 1 + (-1025384579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664086931/1250000000 : ℝ)^4227 ≤ (43400828841033/100000000000000 : ℝ)^3203 := by
    have hnat : (664086931 : ℕ)^4227*100000000000000^3203 ≤ 43400828841033^3203*1250000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664086931 1250000000 43400828841033 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16845287/31250000 : ℝ)^4227 ≤ (11060376822143/25000000000000 : ℝ)^3203 := by
    have hnat : (16845287 : ℕ)^4227*25000000000000^3203 ≤ 11060376822143^3203*31250000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16845287 31250000 11060376822143 25000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025384579/5000000000 : ℝ)^4227 ≤ (12357663857637/100000000000000 : ℝ)^3203 := by
    have hnat : (1025384579 : ℕ)^4227*100000000000000^3203 ≤ 12357663857637^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025384579 5000000000 12357663857637 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664086931/1250000000 : ℝ), (16845287/31250000 : ℝ), (-1025384579/5000000000 : ℝ)] ![(43400828841033/100000000000000 : ℝ), (11060376822143/25000000000000 : ℝ), (12357663857637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664086931/1250000000 : ℝ)|^4227 ≤ (43400828841033/100000000000000 : ℝ)^3203
        have hw : |(664086931/1250000000 : ℝ)|=(664086931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16845287/31250000 : ℝ)|^4227 ≤ (11060376822143/25000000000000 : ℝ)^3203
        have hw : |(16845287/31250000 : ℝ)|=(16845287/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025384579/5000000000 : ℝ)|^4227 ≤ (12357663857637/100000000000000 : ℝ)^3203
        have hw : |(-1025384579/5000000000 : ℝ)|=(1025384579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1261_s8_7 (p : ℝ) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2174092601/5000000000 : ℝ)*x 0 + (1118704861/2500000000 : ℝ)*x 1 + (4225042241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174092601/5000000000 : ℝ)^4227 ≤ (33317699772753/100000000000000 : ℝ)^3203 := by
    have hnat : (2174092601 : ℕ)^4227*100000000000000^3203 ≤ 33317699772753^3203*5000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174092601 5000000000 33317699772753 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118704861/2500000000 : ℝ)^4227 ≤ (34604163155701/100000000000000 : ℝ)^3203 := by
    have hnat : (1118704861 : ℕ)^4227*100000000000000^3203 ≤ 34604163155701^3203*2500000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118704861 2500000000 34604163155701 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225042241/10000000000 : ℝ)^4227 ≤ (32078137049561/100000000000000 : ℝ)^3203 := by
    have hnat : (4225042241 : ℕ)^4227*100000000000000^3203 ≤ 32078137049561^3203*10000000000^4227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225042241 10000000000 32078137049561 100000000000000 4227 3203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4227/1024 : ℝ)) 4227 3203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174092601/5000000000 : ℝ), (1118704861/2500000000 : ℝ), (4225042241/10000000000 : ℝ)] ![(33317699772753/100000000000000 : ℝ), (34604163155701/100000000000000 : ℝ), (32078137049561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174092601/5000000000 : ℝ)|^4227 ≤ (33317699772753/100000000000000 : ℝ)^3203
        have hw : |(2174092601/5000000000 : ℝ)|=(2174092601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118704861/2500000000 : ℝ)|^4227 ≤ (34604163155701/100000000000000 : ℝ)^3203
        have hw : |(1118704861/2500000000 : ℝ)|=(1118704861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225042241/10000000000 : ℝ)|^4227 ≤ (32078137049561/100000000000000 : ℝ)^3203
        have hw : |(4225042241/10000000000 : ℝ)|=(4225042241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1261_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5751/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7057/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11501/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11501/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11501/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11501/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11501/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11501/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11501/100000 : ℝ) ^ (8453/2048 : ℝ) ≤ (2656263985006183/20000000000000000000 : ℝ) := by
    have hpowers : (11501/100000 : ℝ)^8453 ≤ (2656263985006183/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11501 : ℕ)^8453*20000000000000000000^2048 ≤ 2656263985006183^2048*100000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11501 100000 2656263985006183 20000000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11501/100000 : ℝ)) (X := (2656263985006183/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2823/20000 : ℝ) ^ (8453/2048 : ℝ) ≤ (6185683024379781/20000000000000000000 : ℝ) := by
    have hpowers : (2823/20000 : ℝ)^8453 ≤ (6185683024379781/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2823 : ℕ)^8453*20000000000000000000^2048 ≤ 6185683024379781^2048*20000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 20000 6185683024379781 20000000000000000000 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/20000 : ℝ)) (X := (6185683024379781/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002656263985006183/10000000000000000000 : ℝ) ≤ (50003217485667/50000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (10002656263985006183/10000000000000000000 : ℝ)^2048 ≤ (50003217485667/50000000000000 : ℝ)^8453 := by
      have hnat : (10002656263985006183 : ℕ)^2048*50000000000000^8453 ≤ 50003217485667^8453*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002656263985006183 10000000000000000000 50003217485667 50000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50003217485667/50000000000000 : ℝ)) (X := (10002656263985006183/10000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002210486752346491/5000000000000000000 : ℝ) ≤ (1250133867230933/1250000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (5002210486752346491/5000000000000000000 : ℝ)^2048 ≤ (1250133867230933/1250000000000000 : ℝ)^8453 := by
      have hnat : (5002210486752346491 : ℕ)^2048*1250000000000000^8453 ≤ 1250133867230933^8453*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002210486752346491 5000000000000000000 1250133867230933 1250000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250133867230933/1250000000000000 : ℝ)) (X := (5002210486752346491/5000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006185683024379781/10000000000000000000 : ℝ) ≤ (1250187297320191/1250000000000000 : ℝ) ^ (8453/2048 : ℝ) := by
    have hpowers : (10006185683024379781/10000000000000000000 : ℝ)^2048 ≤ (1250187297320191/1250000000000000 : ℝ)^8453 := by
      have hnat : (10006185683024379781 : ℕ)^2048*1250000000000000^8453 ≤ 1250187297320191^8453*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006185683024379781 10000000000000000000 1250187297320191 1250000000000000 2048 8453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250187297320191/1250000000000000 : ℝ)) (X := (10006185683024379781/10000000000000000000 : ℝ)) (by norm_num) 8453 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2656263985006183/20000000000000000000 : ℝ) ≤ ((1633240631887612967/1633750000000000000 : ℝ)+2*(26715044629/16337500000000 : ℝ)*(11501/100000 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (1633240631887612967/1633750000000000000 : ℝ)+2*(26715044629/16337500000000 : ℝ)*(11501/100000 : ℝ)=(50003217485667/50000000000000 : ℝ) by norm_num, show 1+2*(2656263985006183/20000000000000000000 : ℝ)=(10002656263985006183/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6185683024379781/20000000000000000000 : ℝ)+(2656263985006183/20000000000000000000 : ℝ) ≤ ((1633240631887612967/1633750000000000000 : ℝ)+(26715044629/16337500000000 : ℝ)*((2823/20000 : ℝ)+(11501/100000 : ℝ)))^(8453/2048 : ℝ) := by
    rw [show (1633240631887612967/1633750000000000000 : ℝ)+(26715044629/16337500000000 : ℝ)*((2823/20000 : ℝ)+(11501/100000 : ℝ))=(1250133867230933/1250000000000000 : ℝ) by norm_num, show 1+(6185683024379781/20000000000000000000 : ℝ)+(2656263985006183/20000000000000000000 : ℝ)=(5002210486752346491/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6185683024379781/20000000000000000000 : ℝ) ≤ ((1633240631887612967/1633750000000000000 : ℝ)+2*(26715044629/16337500000000 : ℝ)*(2823/20000 : ℝ))^(8453/2048 : ℝ) := by
    rw [show (1633240631887612967/1633750000000000000 : ℝ)+2*(26715044629/16337500000000 : ℝ)*(2823/20000 : ℝ)=(1250187297320191/1250000000000000 : ℝ) by norm_num, show 1+2*(6185683024379781/20000000000000000000 : ℝ)=(10006185683024379781/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1633240631887612967/1633750000000000000 : ℝ)*(X 1 0+X 2 0)+(26715044629/16337500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (11501/100000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (1633240631887612967/1633750000000000000 : ℝ)) (alpha := (26715044629/16337500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1633240631887612967/1633750000000000000 : ℝ)*(X 0 1+X 2 1)+(26715044629/16337500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (11501/100000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (1633240631887612967/1633750000000000000 : ℝ)) (alpha := (26715044629/16337500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1633240631887612967/1633750000000000000 : ℝ)*(X 0 2+X 1 2)+(26715044629/16337500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8453/2048 : ℝ)) (lo := (11501/100000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (1633240631887612967/1633750000000000000 : ℝ)) (alpha := (26715044629/16337500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-42224941/200000000 : ℝ)*X 0 0+(1347701001/2500000000 : ℝ)*X 0 1+(5267501253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344196807/10000000000 : ℝ)*X 1 0+(-2173759507/10000000000 : ℝ)*X 1 1+(5267501481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344196971/10000000000 : ℝ)*X 2 0+(5267501287/10000000000 : ℝ)*X 2 1+(-1086879773/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348176069/10000000000 : ℝ)*X 0 0+(528050841/1250000000 : ℝ)*X 0 1+(895090483/2000000000 : ℝ)*X 0 2+(4348176069/10000000000 : ℝ)*X 1 0+(528050841/1250000000 : ℝ)*X 1 1+(895090483/2000000000 : ℝ)*X 1 2+(4348176069/10000000000 : ℝ)*X 2 0+(528050841/1250000000 : ℝ)*X 2 1+(895090483/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-422250299/2000000000 : ℝ)*X 0 0+(658476551/1250000000 : ℝ)*X 0 1+(2695245921/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656347723/5000000000 : ℝ)*X 1 0+(-1025384579/5000000000 : ℝ)*X 1 1+(2695245921/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664086931/1250000000 : ℝ)*X 2 0+(16845287/31250000 : ℝ)*X 2 1+(-1025384579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174092601/5000000000 : ℝ)*X 0 0+(1118704861/2500000000 : ℝ)*X 0 1+(4225042241/10000000000 : ℝ)*X 0 2+(2174092601/5000000000 : ℝ)*X 1 0+(1118704861/2500000000 : ℝ)*X 1 1+(4225042241/10000000000 : ℝ)*X 1 2+(2174092601/5000000000 : ℝ)*X 2 0+(1118704861/2500000000 : ℝ)*X 2 1+(4225042241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1261_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10142358534170907385341/6535000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1005196279/100000000000000 : ℝ)*(base19) + (1212394447/100000000000000 : ℝ)*(base23) + (43421987/25000000000000 : ℝ)*(upper3) + (11138219/50000000000000 : ℝ)*(upper4) + (123939039/100000000000000 : ℝ)*(upper5) + (755847812530571/12500000000000 : ℝ)*(major0) + (755847812530571/12500000000000 : ℝ)*(major1) + (755847812530571/12500000000000 : ℝ)*(major2) + (4055078875298223/50000000000000 : ℝ)*(sp0) + (8110196336522181/100000000000000 : ℝ)*(sp1) + (2027549032331003/25000000000000 : ℝ)*(sp2) + (3983351854816601/100000000000000 : ℝ)*(sp3) + (19795561007/50000000000000 : ℝ)*(sp4) + (1969027567/12500000000000 : ℝ)*(sp7) + (1991683803518569/50000000000000 : ℝ)*(f.failure) + (405509867085923/5000000000000 : ℝ)*(f.sum) + (38403731572791/6535000000000000000000000000 : ℝ)*base65 + (323636379740835843/20421875000000000000000000000000 : ℝ)*base68 + (36558410948621141/10210937500000000000000000000000 : ℝ)*base69 + (125527707703335843/20421875000000000000000000000000 : ℝ)*base72 + (39126932353601/6535000000000000000000000000 : ℝ)*base73 + (74936545029351657/20421875000000000000000000000000 : ℝ)*base75 + (18687859417121141/10210937500000000000000000000000 : ℝ)*base77 + (20859290991398343/20421875000000000000000000000000 : ℝ)*base80 + (26129370907311/6535000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (13181057/1000000000000000000000 : ℝ)*base89 + (13181057/1000000000000000000000 : ℝ)*base91 + (13181057/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (293612074752062586554294601/40843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161066207/12500000000000 : ℝ)*(base19) + (140235139/10000000000000 : ℝ)*(base23) + (28082693/6250000000000 : ℝ)*(lower1) + (9039107/6250000000000 : ℝ)*(upper3) + (393913/781250000000 : ℝ)*(lower4) + (9231213/6250000000000 : ℝ)*(upper5) + (3038709337205549/50000000000000 : ℝ)*(major0) + (3038709337205549/50000000000000 : ℝ)*(major1) + (3038709337205549/50000000000000 : ℝ)*(major2) + (1336270619/50000000000000 : ℝ)*(sp2) + (8151287670953663/100000000000000 : ℝ)*(sp4) + (8151286382424007/100000000000000 : ℝ)*(sp5) + (1630256719212207/20000000000000 : ℝ)*(sp6) + (1000887359561577/25000000000000 : ℝ)*(sp7) + (1000887359561577/25000000000000 : ℝ)*(f.failure) + (8151287670953663/100000000000000 : ℝ)*(f.sum) + (44470496908551/6535000000000000000000000000 : ℝ)*base65 + (4372446232755646117/81687500000000000000000000000000 : ℝ)*base68 + (254158121311478883/81687500000000000000000000000000 : ℝ)*base69 + (10473485510483478883/81687500000000000000000000000000 : ℝ)*base71 + (8064209170237/3267500000000000000000000000 : ℝ)*base74 + (3427151103940478883/81687500000000000000000000000000 : ℝ)*base75 + (349391081771478883/81687500000000000000000000000000 : ℝ)*base77 + (1831195257944021117/81687500000000000000000000000000 : ℝ)*base80 + (12350009737443/3267500000000000000000000000 : ℝ)*base81 + (641281/500000000000000000000 : ℝ)*base89 + (641281/500000000000000000000 : ℝ)*base91 + (641281/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1261_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5751/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1261_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1261_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5751/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1261_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1261_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1261_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8453/2048 : ℝ) ≤ p) (hpb : p ≤ (4227/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30360153/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5751/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1261_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
