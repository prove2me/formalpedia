-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1391_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:44.492665+00:00
-- url     : https://prove2.me/submissions/40c35b16-0847-4fca-b944-8b40ab8b9522

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
theorem support_rectangle_w1391_s6_0 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1001190753/5000000000 : ℝ)*x 0 + (541018593/1000000000 : ℝ)*x 1 + (262299353/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001190753/5000000000 : ℝ)^4351 ≤ (6103002746407/50000000000000 : ℝ)^3327 := by
    have hnat : (1001190753 : ℕ)^4351*50000000000000^3327 ≤ 6103002746407^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001190753 5000000000 6103002746407 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541018593/1000000000 : ℝ)^4351 ≤ (22390766695439/50000000000000 : ℝ)^3327 := by
    have hnat : (541018593 : ℕ)^4351*50000000000000^3327 ≤ 22390766695439^3327*1000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541018593 1000000000 22390766695439 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262299353/500000000 : ℝ)^4351 ≤ (43012461104327/100000000000000 : ℝ)^3327 := by
    have hnat : (262299353 : ℕ)^4351*100000000000000^3327 ≤ 43012461104327^3327*500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262299353 500000000 43012461104327 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1001190753/5000000000 : ℝ), (541018593/1000000000 : ℝ), (262299353/500000000 : ℝ)] ![(6103002746407/50000000000000 : ℝ), (22390766695439/50000000000000 : ℝ), (43012461104327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1001190753/5000000000 : ℝ)|^4351 ≤ (6103002746407/50000000000000 : ℝ)^3327
        have hw : |(-1001190753/5000000000 : ℝ)|=(1001190753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541018593/1000000000 : ℝ)|^4351 ≤ (22390766695439/50000000000000 : ℝ)^3327
        have hw : |(541018593/1000000000 : ℝ)|=(541018593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262299353/500000000 : ℝ)|^4351 ≤ (43012461104327/100000000000000 : ℝ)^3327
        have hw : |(262299353/500000000 : ℝ)|=(262299353/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s6_1 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348099871/10000000000 : ℝ)*x 0 + (-2086005037/10000000000 : ℝ)*x 1 + (327874191/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348099871/10000000000 : ℝ)^4351 ≤ (22055324687903/50000000000000 : ℝ)^3327 := by
    have hnat : (5348099871 : ℕ)^4351*50000000000000^3327 ≤ 22055324687903^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348099871 10000000000 22055324687903 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086005037/10000000000 : ℝ)^4351 ≤ (2575377911247/20000000000000 : ℝ)^3327 := by
    have hnat : (2086005037 : ℕ)^4351*20000000000000^3327 ≤ 2575377911247^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086005037 10000000000 2575377911247 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327874191/625000000 : ℝ)^4351 ≤ (10753115265359/25000000000000 : ℝ)^3327 := by
    have hnat : (327874191 : ℕ)^4351*25000000000000^3327 ≤ 10753115265359^3327*625000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327874191 625000000 10753115265359 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348099871/10000000000 : ℝ), (-2086005037/10000000000 : ℝ), (327874191/625000000 : ℝ)] ![(22055324687903/50000000000000 : ℝ), (2575377911247/20000000000000 : ℝ), (10753115265359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348099871/10000000000 : ℝ)|^4351 ≤ (22055324687903/50000000000000 : ℝ)^3327
        have hw : |(5348099871/10000000000 : ℝ)|=(5348099871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086005037/10000000000 : ℝ)|^4351 ≤ (2575377911247/20000000000000 : ℝ)^3327
        have hw : |(-2086005037/10000000000 : ℝ)|=(2086005037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327874191/625000000 : ℝ)|^4351 ≤ (10753115265359/25000000000000 : ℝ)^3327
        have hw : |(327874191/625000000 : ℝ)|=(327874191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s6_2 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337024969/2500000000 : ℝ)*x 0 + (5245987073/10000000000 : ℝ)*x 1 + (-2086005007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337024969/2500000000 : ℝ)^4351 ≤ (22055324714869/50000000000000 : ℝ)^3327 := by
    have hnat : (1337024969 : ℕ)^4351*50000000000000^3327 ≤ 22055324714869^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337024969 2500000000 22055324714869 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245987073/10000000000 : ℝ)^4351 ≤ (21506230621861/50000000000000 : ℝ)^3327 := by
    have hnat : (5245987073 : ℕ)^4351*50000000000000^3327 ≤ 21506230621861^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245987073 10000000000 21506230621861 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086005007/10000000000 : ℝ)^4351 ≤ (12876889314047/100000000000000 : ℝ)^3327 := by
    have hnat : (2086005007 : ℕ)^4351*100000000000000^3327 ≤ 12876889314047^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086005007 10000000000 12876889314047 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337024969/2500000000 : ℝ), (5245987073/10000000000 : ℝ), (-2086005007/10000000000 : ℝ)] ![(22055324714869/50000000000000 : ℝ), (21506230621861/50000000000000 : ℝ), (12876889314047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337024969/2500000000 : ℝ)|^4351 ≤ (22055324714869/50000000000000 : ℝ)^3327
        have hw : |(1337024969/2500000000 : ℝ)|=(1337024969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245987073/10000000000 : ℝ)|^4351 ≤ (21506230621861/50000000000000 : ℝ)^3327
        have hw : |(5245987073/10000000000 : ℝ)|=(5245987073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086005007/10000000000 : ℝ)|^4351 ≤ (12876889314047/100000000000000 : ℝ)^3327
        have hw : |(-2086005007/10000000000 : ℝ)|=(2086005007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s6_3 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4313967373/10000000000 : ℝ)*x 0 + (2071039977/5000000000 : ℝ)*x 1 + (4492357317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313967373/10000000000 : ℝ)^4351 ≤ (4163010618353/12500000000000 : ℝ)^3327 := by
    have hnat : (4313967373 : ℕ)^4351*12500000000000^3327 ≤ 4163010618353^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313967373 10000000000 4163010618353 12500000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071039977/5000000000 : ℝ)^4351 ≤ (31579419824243/100000000000000 : ℝ)^3327 := by
    have hnat : (2071039977 : ℕ)^4351*100000000000000^3327 ≤ 31579419824243^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071039977 5000000000 31579419824243 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492357317/10000000000 : ℝ)^4351 ≤ (35116495218837/100000000000000 : ℝ)^3327 := by
    have hnat : (4492357317 : ℕ)^4351*100000000000000^3327 ≤ 35116495218837^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492357317 10000000000 35116495218837 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313967373/10000000000 : ℝ), (2071039977/5000000000 : ℝ), (4492357317/10000000000 : ℝ)] ![(4163010618353/12500000000000 : ℝ), (31579419824243/100000000000000 : ℝ), (35116495218837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313967373/10000000000 : ℝ)|^4351 ≤ (4163010618353/12500000000000 : ℝ)^3327
        have hw : |(4313967373/10000000000 : ℝ)|=(4313967373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071039977/5000000000 : ℝ)|^4351 ≤ (31579419824243/100000000000000 : ℝ)^3327
        have hw : |(2071039977/5000000000 : ℝ)|=(2071039977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492357317/10000000000 : ℝ)|^4351 ≤ (35116495218837/100000000000000 : ℝ)^3327
        have hw : |(4492357317/10000000000 : ℝ)|=(4492357317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s6_4 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2002393221/10000000000 : ℝ)*x 0 + (2623288697/5000000000 : ℝ)*x 1 + (2704796261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2002393221/10000000000 : ℝ)^4351 ≤ (305152472099/2500000000000 : ℝ)^3327 := by
    have hnat : (2002393221 : ℕ)^4351*2500000000000^3327 ≤ 305152472099^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002393221 10000000000 305152472099 2500000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623288697/5000000000 : ℝ)^4351 ≤ (43018791176737/100000000000000 : ℝ)^3327 := by
    have hnat : (2623288697 : ℕ)^4351*100000000000000^3327 ≤ 43018791176737^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623288697 5000000000 43018791176737 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704796261/5000000000 : ℝ)^4351 ≤ (11193777482371/25000000000000 : ℝ)^3327 := by
    have hnat : (2704796261 : ℕ)^4351*25000000000000^3327 ≤ 11193777482371^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704796261 5000000000 11193777482371 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2002393221/10000000000 : ℝ), (2623288697/5000000000 : ℝ), (2704796261/5000000000 : ℝ)] ![(305152472099/2500000000000 : ℝ), (43018791176737/100000000000000 : ℝ), (11193777482371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2002393221/10000000000 : ℝ)|^4351 ≤ (305152472099/2500000000000 : ℝ)^3327
        have hw : |(-2002393221/10000000000 : ℝ)|=(2002393221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623288697/5000000000 : ℝ)|^4351 ≤ (43018791176737/100000000000000 : ℝ)^3327
        have hw : |(2623288697/5000000000 : ℝ)|=(2623288697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704796261/5000000000 : ℝ)|^4351 ≤ (11193777482371/25000000000000 : ℝ)^3327
        have hw : |(2704796261/5000000000 : ℝ)|=(2704796261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s6_5 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331598559/625000000 : ℝ)*x 0 + (-961199783/5000000000 : ℝ)*x 1 + (2163837/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331598559/625000000 : ℝ)^4351 ≤ (43652538432043/100000000000000 : ℝ)^3327 := by
    have hnat : (331598559 : ℕ)^4351*100000000000000^3327 ≤ 43652538432043^3327*625000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331598559 625000000 43652538432043 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961199783/5000000000 : ℝ)^4351 ≤ (5786175932253/50000000000000 : ℝ)^3327 := by
    have hnat : (961199783 : ℕ)^4351*50000000000000^3327 ≤ 5786175932253^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961199783 5000000000 5786175932253 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2163837/4000000 : ℝ)^4351 ≤ (2798444355709/6250000000000 : ℝ)^3327 := by
    have hnat : (2163837 : ℕ)^4351*6250000000000^3327 ≤ 2798444355709^3327*4000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163837 4000000 2798444355709 6250000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331598559/625000000 : ℝ), (-961199783/5000000000 : ℝ), (2163837/4000000 : ℝ)] ![(43652538432043/100000000000000 : ℝ), (5786175932253/50000000000000 : ℝ), (2798444355709/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331598559/625000000 : ℝ)|^4351 ≤ (43652538432043/100000000000000 : ℝ)^3327
        have hw : |(331598559/625000000 : ℝ)|=(331598559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-961199783/5000000000 : ℝ)|^4351 ≤ (5786175932253/50000000000000 : ℝ)^3327
        have hw : |(-961199783/5000000000 : ℝ)|=(961199783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2163837/4000000 : ℝ)|^4351 ≤ (2798444355709/6250000000000 : ℝ)^3327
        have hw : |(2163837/4000000 : ℝ)|=(2163837/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s6_6 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305576879/10000000000 : ℝ)*x 0 + (2704796273/5000000000 : ℝ)*x 1 + (-240299949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305576879/10000000000 : ℝ)^4351 ≤ (43652537732641/100000000000000 : ℝ)^3327 := by
    have hnat : (5305576879 : ℕ)^4351*100000000000000^3327 ≤ 43652537732641^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305576879 10000000000 43652537732641 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704796273/5000000000 : ℝ)^4351 ≤ (5596888773659/12500000000000 : ℝ)^3327 := by
    have hnat : (2704796273 : ℕ)^4351*12500000000000^3327 ≤ 5596888773659^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704796273 5000000000 5596888773659 12500000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240299949/1250000000 : ℝ)^4351 ≤ (1446544008649/12500000000000 : ℝ)^3327 := by
    have hnat : (240299949 : ℕ)^4351*12500000000000^3327 ≤ 1446544008649^3327*1250000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240299949 1250000000 1446544008649 12500000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305576879/10000000000 : ℝ), (2704796273/5000000000 : ℝ), (-240299949/1250000000 : ℝ)] ![(43652537732641/100000000000000 : ℝ), (5596888773659/12500000000000 : ℝ), (1446544008649/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305576879/10000000000 : ℝ)|^4351 ≤ (43652537732641/100000000000000 : ℝ)^3327
        have hw : |(5305576879/10000000000 : ℝ)|=(5305576879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704796273/5000000000 : ℝ)|^4351 ≤ (5596888773659/12500000000000 : ℝ)^3327
        have hw : |(2704796273/5000000000 : ℝ)|=(2704796273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240299949/1250000000 : ℝ)|^4351 ≤ (1446544008649/12500000000000 : ℝ)^3327
        have hw : |(-240299949/1250000000 : ℝ)|=(240299949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s6_7 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4313992291/10000000000 : ℝ)*x 0 + (4491098043/10000000000 : ℝ)*x 1 + (207167287/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313992291/10000000000 : ℝ)^4351 ≤ (8326084130893/25000000000000 : ℝ)^3327 := by
    have hnat : (4313992291 : ℕ)^4351*25000000000000^3327 ≤ 8326084130893^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313992291 10000000000 8326084130893 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491098043/10000000000 : ℝ)^4351 ≤ (35103622370417/100000000000000 : ℝ)^3327 := by
    have hnat : (4491098043 : ℕ)^4351*100000000000000^3327 ≤ 35103622370417^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491098043 10000000000 35103622370417 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207167287/500000000 : ℝ)^4351 ≤ (31592041082741/100000000000000 : ℝ)^3327 := by
    have hnat : (207167287 : ℕ)^4351*100000000000000^3327 ≤ 31592041082741^3327*500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207167287 500000000 31592041082741 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313992291/10000000000 : ℝ), (4491098043/10000000000 : ℝ), (207167287/500000000 : ℝ)] ![(8326084130893/25000000000000 : ℝ), (35103622370417/100000000000000 : ℝ), (31592041082741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313992291/10000000000 : ℝ)|^4351 ≤ (8326084130893/25000000000000 : ℝ)^3327
        have hw : |(4313992291/10000000000 : ℝ)|=(4313992291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491098043/10000000000 : ℝ)|^4351 ≤ (35103622370417/100000000000000 : ℝ)^3327
        have hw : |(4491098043/10000000000 : ℝ)|=(4491098043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207167287/500000000 : ℝ)|^4351 ≤ (31592041082741/100000000000000 : ℝ)^3327
        have hw : |(207167287/500000000 : ℝ)|=(207167287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1391_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (563/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14737/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2251/20000 : ℝ) ^ (2175/512 : ℝ) ≤ (2333518356954113/25000000000000000000 : ℝ) := by
    have hpowers : (2251/20000 : ℝ)^2175 ≤ (2333518356954113/25000000000000000000 : ℝ)^512 := by
      have hnat : (2251 : ℕ)^2175*25000000000000000000^512 ≤ 2333518356954113^512*20000^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2251 20000 2333518356954113 25000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2251/20000 : ℝ)) (X := (2333518356954113/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7371/50000 : ℝ) ^ (2175/512 : ℝ) ≤ (29375728282826651/100000000000000000000 : ℝ) := by
    have hpowers : (7371/50000 : ℝ)^2175 ≤ (29375728282826651/100000000000000000000 : ℝ)^512 := by
      have hnat : (7371 : ℕ)^2175*100000000000000000000^512 ≤ 29375728282826651^512*50000^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7371 50000 29375728282826651 100000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7371/50000 : ℝ)) (X := (29375728282826651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502333518356954113/12500000000000000000 : ℝ) ≤ (10000439421109061/10000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (12502333518356954113/12500000000000000000 : ℝ)^512 ≤ (10000439421109061/10000000000000000 : ℝ)^2175 := by
      have hnat : (12502333518356954113 : ℕ)^512*10000000000000000^2175 ≤ 10000439421109061^2175*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502333518356954113 12500000000000000000 10000439421109061 10000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000439421109061/10000000000000000 : ℝ)) (X := (12502333518356954113/12500000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038709801710643103/100000000000000000000 : ℝ) ≤ (10000911102810331/10000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (100038709801710643103/100000000000000000000 : ℝ)^512 ≤ (10000911102810331/10000000000000000 : ℝ)^2175 := by
      have hnat : (100038709801710643103 : ℕ)^512*10000000000000000^2175 ≤ 10000911102810331^2175*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038709801710643103 100000000000000000000 10000911102810331 10000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000911102810331/10000000000000000 : ℝ)) (X := (100038709801710643103/100000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029375728282826651/50000000000000000000 : ℝ) ≤ (10001382784511601/10000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (50029375728282826651/50000000000000000000 : ℝ)^512 ≤ (10001382784511601/10000000000000000 : ℝ)^2175 := by
      have hnat : (50029375728282826651 : ℕ)^512*10000000000000000^2175 ≤ 10001382784511601^2175*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029375728282826651 50000000000000000000 10001382784511601 10000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001382784511601/10000000000000000 : ℝ)) (X := (50029375728282826651/50000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2333518356954113/25000000000000000000 : ℝ) ≤ ((34860914706311708007/34870000000000000000 : ℝ)+2*(47168170127/34870000000000 : ℝ)*(2251/20000 : ℝ))^(2175/512 : ℝ) := by
    rw [show (34860914706311708007/34870000000000000000 : ℝ)+2*(47168170127/34870000000000 : ℝ)*(2251/20000 : ℝ)=(10000439421109061/10000000000000000 : ℝ) by norm_num, show 1+2*(2333518356954113/25000000000000000000 : ℝ)=(12502333518356954113/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29375728282826651/100000000000000000000 : ℝ)+(2333518356954113/25000000000000000000 : ℝ) ≤ ((34860914706311708007/34870000000000000000 : ℝ)+(47168170127/34870000000000 : ℝ)*((7371/50000 : ℝ)+(2251/20000 : ℝ)))^(2175/512 : ℝ) := by
    rw [show (34860914706311708007/34870000000000000000 : ℝ)+(47168170127/34870000000000 : ℝ)*((7371/50000 : ℝ)+(2251/20000 : ℝ))=(10000911102810331/10000000000000000 : ℝ) by norm_num, show 1+(29375728282826651/100000000000000000000 : ℝ)+(2333518356954113/25000000000000000000 : ℝ)=(100038709801710643103/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29375728282826651/100000000000000000000 : ℝ) ≤ ((34860914706311708007/34870000000000000000 : ℝ)+2*(47168170127/34870000000000 : ℝ)*(7371/50000 : ℝ))^(2175/512 : ℝ) := by
    rw [show (34860914706311708007/34870000000000000000 : ℝ)+2*(47168170127/34870000000000 : ℝ)*(7371/50000 : ℝ)=(10001382784511601/10000000000000000 : ℝ) by norm_num, show 1+2*(29375728282826651/100000000000000000000 : ℝ)=(50029375728282826651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34860914706311708007/34870000000000000000 : ℝ)*(X 1 0+X 2 0)+(47168170127/34870000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (34860914706311708007/34870000000000000000 : ℝ)) (alpha := (47168170127/34870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34860914706311708007/34870000000000000000 : ℝ)*(X 0 1+X 2 1)+(47168170127/34870000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (34860914706311708007/34870000000000000000 : ℝ)) (alpha := (47168170127/34870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34860914706311708007/34870000000000000000 : ℝ)*(X 0 2+X 1 2)+(47168170127/34870000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (34860914706311708007/34870000000000000000 : ℝ)) (alpha := (47168170127/34870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1001190753/5000000000 : ℝ)*X 0 0+(541018593/1000000000 : ℝ)*X 0 1+(262299353/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348099871/10000000000 : ℝ)*X 1 0+(-2086005037/10000000000 : ℝ)*X 1 1+(327874191/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337024969/2500000000 : ℝ)*X 2 0+(5245987073/10000000000 : ℝ)*X 2 1+(-2086005007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313967373/10000000000 : ℝ)*X 0 0+(2071039977/5000000000 : ℝ)*X 0 1+(4492357317/10000000000 : ℝ)*X 0 2+(4313967373/10000000000 : ℝ)*X 1 0+(2071039977/5000000000 : ℝ)*X 1 1+(4492357317/10000000000 : ℝ)*X 1 2+(4313967373/10000000000 : ℝ)*X 2 0+(2071039977/5000000000 : ℝ)*X 2 1+(4492357317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2002393221/10000000000 : ℝ)*X 0 0+(2623288697/5000000000 : ℝ)*X 0 1+(2704796261/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331598559/625000000 : ℝ)*X 1 0+(-961199783/5000000000 : ℝ)*X 1 1+(2163837/4000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305576879/10000000000 : ℝ)*X 2 0+(2704796273/5000000000 : ℝ)*X 2 1+(-240299949/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313992291/10000000000 : ℝ)*X 0 0+(4491098043/10000000000 : ℝ)*X 0 1+(207167287/500000000 : ℝ)*X 0 2+(4313992291/10000000000 : ℝ)*X 1 0+(4491098043/10000000000 : ℝ)*X 1 1+(207167287/500000000 : ℝ)*X 1 2+(4313992291/10000000000 : ℝ)*X 2 0+(4491098043/10000000000 : ℝ)*X 2 1+(207167287/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111509938618627346403157479/39625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (586739103/100000000000000 : ℝ)*(base19) + (475829703/100000000000000 : ℝ)*(base23) + (31180277/50000000000000 : ℝ)*(lower2) + (4011/6400000000 : ℝ)*(upper3) + (3099577/20000000000000 : ℝ)*(upper5) + (2236273410766489/50000000000000 : ℝ)*(major0) + (2236273410766489/50000000000000 : ℝ)*(major1) + (2236273410766489/50000000000000 : ℝ)*(major2) + (1522547290640319/25000000000000 : ℝ)*(sp0) + (1218040329118399/20000000000000 : ℝ)*(sp1) + (1218040351300279/20000000000000 : ℝ)*(sp2) + (1427442631921677/50000000000000 : ℝ)*(sp3) + (6534884911/50000000000000 : ℝ)*(sp4) + (1210617427/20000000000000 : ℝ)*(sp7) + (2854891316930489/100000000000000 : ℝ)*(f.failure) + (3045101116165549/50000000000000 : ℝ)*(f.sum) + (4093307883971/3487000000000000000000000000 : ℝ)*base66 + (3743692553069922577/1743500000000000000000000000000000 : ℝ)*base68 + (8971024078315422577/1743500000000000000000000000000000 : ℝ)*base70 + (15638544308549577423/1743500000000000000000000000000000 : ℝ)*base71 + (55557203359/348700000000000000000000000 : ℝ)*base73 + (11624033190321422577/1743500000000000000000000000000000 : ℝ)*base76 + (13330047084262922577/1743500000000000000000000000000000 : ℝ)*base78 + (5155607249454422577/1743500000000000000000000000000000 : ℝ)*base80 + (11553620051499/3487000000000000000000000000 : ℝ)*base82 + (8271791/2000000000000000000000 : ℝ)*base89 + (8271791/2000000000000000000000 : ℝ)*base91 + (8271791/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16450779147472073391719519079/1743500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (333328699/20000000000000 : ℝ)*(base19) + (176778689/10000000000000 : ℝ)*(base23) + (17749241/10000000000000 : ℝ)*(upper3) + (85867179/100000000000000 : ℝ)*(lower4) + (188597963/100000000000000 : ℝ)*(upper5) + (4505003575892967/100000000000000 : ℝ)*(major0) + (4505003575892967/100000000000000 : ℝ)*(major1) + (4505003575892967/100000000000000 : ℝ)*(major2) + (35088636559/100000000000000 : ℝ)*(sp1) + (9223006793/25000000000000 : ℝ)*(sp2) + (6134397904650393/100000000000000 : ℝ)*(sp4) + (6134361149370339/100000000000000 : ℝ)*(sp5) + (613435924483633/10000000000000 : ℝ)*(sp6) + (2875608932619153/100000000000000 : ℝ)*(sp7) + (2875608932619153/100000000000000 : ℝ)*(f.failure) + (6134397904650393/100000000000000 : ℝ)*(f.sum) + (884780084541/435875000000000000000000000 : ℝ)*base65 + (34806203229770886769/3487000000000000000000000000000000 : ℝ)*base67 + (10172689439555886769/3487000000000000000000000000000000 : ℝ)*base69 + (19174107737361886769/3487000000000000000000000000000000 : ℝ)*base71 + (586962511119/217937500000000000000000000 : ℝ)*base73 + (73698588133109886769/3487000000000000000000000000000000 : ℝ)*base75 + (15410250966742886769/3487000000000000000000000000000000 : ℝ)*base77 + (64627976063392886769/3487000000000000000000000000000000 : ℝ)*base79 + (2373728001927/1743500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8863593/2000000000000000000000 : ℝ)*base90 + (8863593/2000000000000000000000 : ℝ)*base92 + (8863593/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1391_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1391_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1391_s7_0 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674045111/5000000000 : ℝ)*x 0 + (2623011453/5000000000 : ℝ)*x 1 + (-2085970311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674045111/5000000000 : ℝ)^4351 ≤ (44110545296973/100000000000000 : ℝ)^3327 := by
    have hnat : (2674045111 : ℕ)^4351*100000000000000^3327 ≤ 44110545296973^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674045111 5000000000 44110545296973 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623011453/5000000000 : ℝ)^4351 ≤ (10753211367483/25000000000000 : ℝ)^3327 := by
    have hnat : (2623011453 : ℕ)^4351*25000000000000^3327 ≤ 10753211367483^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623011453 5000000000 10753211367483 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085970311/10000000000 : ℝ)^4351 ≤ (515064368637/4000000000000 : ℝ)^3327 := by
    have hnat : (2085970311 : ℕ)^4351*4000000000000^3327 ≤ 515064368637^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085970311 10000000000 515064368637 4000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674045111/5000000000 : ℝ), (2623011453/5000000000 : ℝ), (-2085970311/10000000000 : ℝ)] ![(44110545296973/100000000000000 : ℝ), (10753211367483/25000000000000 : ℝ), (515064368637/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674045111/5000000000 : ℝ)|^4351 ≤ (44110545296973/100000000000000 : ℝ)^3327
        have hw : |(2674045111/5000000000 : ℝ)|=(2674045111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623011453/5000000000 : ℝ)|^4351 ≤ (10753211367483/25000000000000 : ℝ)^3327
        have hw : |(2623011453/5000000000 : ℝ)|=(2623011453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2085970311/10000000000 : ℝ)|^4351 ≤ (515064368637/4000000000000 : ℝ)^3327
        have hw : |(-2085970311/10000000000 : ℝ)|=(2085970311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s7_1 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-200239691/1000000000 : ℝ)*x 0 + (5246612681/10000000000 : ℝ)*x 1 + (169048589/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200239691/1000000000 : ℝ)^4351 ≤ (305153207311/2500000000000 : ℝ)^3327 := by
    have hnat : (200239691 : ℕ)^4351*2500000000000^3327 ≤ 305153207311^3327*1000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200239691 1000000000 305153207311 2500000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246612681/10000000000 : ℝ)^4351 ≤ (8603833912291/20000000000000 : ℝ)^3327 := by
    have hnat : (5246612681 : ℕ)^4351*20000000000000^3327 ≤ 8603833912291^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246612681 10000000000 8603833912291 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169048589/312500000 : ℝ)^4351 ≤ (11193675531799/25000000000000 : ℝ)^3327 := by
    have hnat : (169048589 : ℕ)^4351*25000000000000^3327 ≤ 11193675531799^3327*312500000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169048589 312500000 11193675531799 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200239691/1000000000 : ℝ), (5246612681/10000000000 : ℝ), (169048589/312500000 : ℝ)] ![(305153207311/2500000000000 : ℝ), (8603833912291/20000000000000 : ℝ), (11193675531799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200239691/1000000000 : ℝ)|^4351 ≤ (305153207311/2500000000000 : ℝ)^3327
        have hw : |(-200239691/1000000000 : ℝ)|=(200239691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246612681/10000000000 : ℝ)|^4351 ≤ (8603833912291/20000000000000 : ℝ)^3327
        have hw : |(5246612681/10000000000 : ℝ)|=(5246612681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169048589/312500000 : ℝ)|^4351 ≤ (11193675531799/25000000000000 : ℝ)^3327
        have hw : |(169048589/312500000 : ℝ)|=(169048589/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s7_2 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212223457/400000000 : ℝ)*x 0 + (-384487681/2000000000 : ℝ)*x 1 + (1352388707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212223457/400000000 : ℝ)^4351 ≤ (21826320223921/50000000000000 : ℝ)^3327 := by
    have hnat : (212223457 : ℕ)^4351*50000000000000^3327 ≤ 21826320223921^3327*400000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212223457 400000000 21826320223921 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384487681/2000000000 : ℝ)^4351 ≤ (11572657626599/100000000000000 : ℝ)^3327 := by
    have hnat : (384487681 : ℕ)^4351*100000000000000^3327 ≤ 11572657626599^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384487681 2000000000 11572657626599 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352388707/2500000000 : ℝ)^4351 ≤ (22387350955353/50000000000000 : ℝ)^3327 := by
    have hnat : (1352388707 : ℕ)^4351*50000000000000^3327 ≤ 22387350955353^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352388707 2500000000 22387350955353 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212223457/400000000 : ℝ), (-384487681/2000000000 : ℝ), (1352388707/2500000000 : ℝ)] ![(21826320223921/50000000000000 : ℝ), (11572657626599/100000000000000 : ℝ), (22387350955353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212223457/400000000 : ℝ)|^4351 ≤ (21826320223921/50000000000000 : ℝ)^3327
        have hw : |(212223457/400000000 : ℝ)|=(212223457/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-384487681/2000000000 : ℝ)|^4351 ≤ (11572657626599/100000000000000 : ℝ)^3327
        have hw : |(-384487681/2000000000 : ℝ)|=(384487681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352388707/2500000000 : ℝ)|^4351 ≤ (22387350955353/50000000000000 : ℝ)^3327
        have hw : |(1352388707/2500000000 : ℝ)|=(1352388707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s7_3 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652793193/5000000000 : ℝ)*x 0 + (338097179/625000000 : ℝ)*x 1 + (-240304801/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652793193/5000000000 : ℝ)^4351 ≤ (218263200141/500000000000 : ℝ)^3327 := by
    have hnat : (2652793193 : ℕ)^4351*500000000000^3327 ≤ 218263200141^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652793193 5000000000 218263200141 500000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338097179/625000000 : ℝ)^4351 ≤ (44774702300387/100000000000000 : ℝ)^3327 := by
    have hnat : (338097179 : ℕ)^4351*100000000000000^3327 ≤ 44774702300387^3327*625000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338097179 625000000 44774702300387 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240304801/1250000000 : ℝ)^4351 ≤ (11572657650217/100000000000000 : ℝ)^3327 := by
    have hnat : (240304801 : ℕ)^4351*100000000000000^3327 ≤ 11572657650217^3327*1250000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240304801 1250000000 11572657650217 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652793193/5000000000 : ℝ), (338097179/625000000 : ℝ), (-240304801/1250000000 : ℝ)] ![(218263200141/500000000000 : ℝ), (44774702300387/100000000000000 : ℝ), (11572657650217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652793193/5000000000 : ℝ)|^4351 ≤ (218263200141/500000000000 : ℝ)^3327
        have hw : |(2652793193/5000000000 : ℝ)|=(2652793193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338097179/625000000 : ℝ)|^4351 ≤ (44774702300387/100000000000000 : ℝ)^3327
        have hw : |(338097179/625000000 : ℝ)|=(338097179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240304801/1250000000 : ℝ)|^4351 ≤ (11572657650217/100000000000000 : ℝ)^3327
        have hw : |(-240304801/1250000000 : ℝ)|=(240304801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s7_4 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078498719/2500000000 : ℝ)*x 0 + (2245509943/5000000000 : ℝ)*x 1 + (4143423243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078498719/2500000000 : ℝ)^4351 ≤ (33304362622237/100000000000000 : ℝ)^3327 := by
    have hnat : (1078498719 : ℕ)^4351*100000000000000^3327 ≤ 33304362622237^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078498719 2500000000 33304362622237 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245509943/5000000000 : ℝ)^4351 ≤ (1096963232877/3125000000000 : ℝ)^3327 := by
    have hnat : (2245509943 : ℕ)^4351*3125000000000^3327 ≤ 1096963232877^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245509943 5000000000 1096963232877 3125000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4143423243/10000000000 : ℝ)^4351 ≤ (31592813910223/100000000000000 : ℝ)^3327 := by
    have hnat : (4143423243 : ℕ)^4351*100000000000000^3327 ≤ 31592813910223^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143423243 10000000000 31592813910223 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078498719/2500000000 : ℝ), (2245509943/5000000000 : ℝ), (4143423243/10000000000 : ℝ)] ![(33304362622237/100000000000000 : ℝ), (1096963232877/3125000000000 : ℝ), (31592813910223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078498719/2500000000 : ℝ)|^4351 ≤ (33304362622237/100000000000000 : ℝ)^3327
        have hw : |(1078498719/2500000000 : ℝ)|=(1078498719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245509943/5000000000 : ℝ)|^4351 ≤ (1096963232877/3125000000000 : ℝ)^3327
        have hw : |(2245509943/5000000000 : ℝ)|=(2245509943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4143423243/10000000000 : ℝ)|^4351 ≤ (31592813910223/100000000000000 : ℝ)^3327
        have hw : |(4143423243/10000000000 : ℝ)|=(4143423243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1391_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (563/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (921/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (563/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (563/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (563/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (563/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (563/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (563/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (563/5000 : ℝ) ^ (2175/512 : ℝ) ≤ (9351701236927807/100000000000000000000 : ℝ) := by
    have hpowers : (563/5000 : ℝ)^2175 ≤ (9351701236927807/100000000000000000000 : ℝ)^512 := by
      have hnat : (563 : ℕ)^2175*100000000000000000000^512 ≤ 9351701236927807^512*5000^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 5000 9351701236927807 100000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/5000 : ℝ)) (X := (9351701236927807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14737/100000 : ℝ) ^ (2175/512 : ℝ) ≤ (14666713559357417/50000000000000000000 : ℝ) := by
    have hpowers : (14737/100000 : ℝ)^2175 ≤ (14666713559357417/50000000000000000000 : ℝ)^512 := by
      have hnat : (14737 : ℕ)^2175*50000000000000000000^512 ≤ 14666713559357417^512*100000^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14737 100000 14666713559357417 50000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14737/100000 : ℝ)) (X := (14666713559357417/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009351701236927807/50000000000000000000 : ℝ) ≤ (5000220125457933/5000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (50009351701236927807/50000000000000000000 : ℝ)^512 ≤ (5000220125457933/5000000000000000 : ℝ)^2175 := by
      have hnat : (50009351701236927807 : ℕ)^512*5000000000000000^2175 ≤ 5000220125457933^2175*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009351701236927807 50000000000000000000 5000220125457933 5000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000220125457933/5000000000000000 : ℝ)) (X := (50009351701236927807/50000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038685128355642641/100000000000000000000 : ℝ) ≤ (2500227630541419/2500000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (100038685128355642641/100000000000000000000 : ℝ)^512 ≤ (2500227630541419/2500000000000000 : ℝ)^2175 := by
      have hnat : (100038685128355642641 : ℕ)^512*2500000000000000^2175 ≤ 2500227630541419^2175*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038685128355642641 100000000000000000000 2500227630541419 2500000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500227630541419/2500000000000000 : ℝ)) (X := (100038685128355642641/100000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014666713559357417/25000000000000000000 : ℝ) ≤ (5000690396707743/5000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (25014666713559357417/25000000000000000000 : ℝ)^512 ≤ (5000690396707743/5000000000000000 : ℝ)^2175 := by
      have hnat : (25014666713559357417 : ℕ)^512*5000000000000000^2175 ≤ 5000690396707743^2175*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014666713559357417 25000000000000000000 5000690396707743 5000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000690396707743/5000000000000000 : ℝ)) (X := (25014666713559357417/25000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9351701236927807/100000000000000000000 : ℝ) ≤ ((5793490040648124147/5795000000000000000 : ℝ)+2*(15675708327/11590000000000 : ℝ)*(563/5000 : ℝ))^(2175/512 : ℝ) := by
    rw [show (5793490040648124147/5795000000000000000 : ℝ)+2*(15675708327/11590000000000 : ℝ)*(563/5000 : ℝ)=(5000220125457933/5000000000000000 : ℝ) by norm_num, show 1+2*(9351701236927807/100000000000000000000 : ℝ)=(50009351701236927807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14666713559357417/50000000000000000000 : ℝ)+(9351701236927807/100000000000000000000 : ℝ) ≤ ((5793490040648124147/5795000000000000000 : ℝ)+(15675708327/11590000000000 : ℝ)*((14737/100000 : ℝ)+(563/5000 : ℝ)))^(2175/512 : ℝ) := by
    rw [show (5793490040648124147/5795000000000000000 : ℝ)+(15675708327/11590000000000 : ℝ)*((14737/100000 : ℝ)+(563/5000 : ℝ))=(2500227630541419/2500000000000000 : ℝ) by norm_num, show 1+(14666713559357417/50000000000000000000 : ℝ)+(9351701236927807/100000000000000000000 : ℝ)=(100038685128355642641/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14666713559357417/50000000000000000000 : ℝ) ≤ ((5793490040648124147/5795000000000000000 : ℝ)+2*(15675708327/11590000000000 : ℝ)*(14737/100000 : ℝ))^(2175/512 : ℝ) := by
    rw [show (5793490040648124147/5795000000000000000 : ℝ)+2*(15675708327/11590000000000 : ℝ)*(14737/100000 : ℝ)=(5000690396707743/5000000000000000 : ℝ) by norm_num, show 1+2*(14666713559357417/50000000000000000000 : ℝ)=(25014666713559357417/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5793490040648124147/5795000000000000000 : ℝ)*(X 1 0+X 2 0)+(15675708327/11590000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (5793490040648124147/5795000000000000000 : ℝ)) (alpha := (15675708327/11590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5793490040648124147/5795000000000000000 : ℝ)*(X 0 1+X 2 1)+(15675708327/11590000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (5793490040648124147/5795000000000000000 : ℝ)) (alpha := (15675708327/11590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5793490040648124147/5795000000000000000 : ℝ)*(X 0 2+X 1 2)+(15675708327/11590000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (5793490040648124147/5795000000000000000 : ℝ)) (alpha := (15675708327/11590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2674045111/5000000000 : ℝ)*X 2 0+(2623011453/5000000000 : ℝ)*X 2 1+(-2085970311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-200239691/1000000000 : ℝ)*X 0 0+(5246612681/10000000000 : ℝ)*X 0 1+(169048589/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((212223457/400000000 : ℝ)*X 1 0+(-384487681/2000000000 : ℝ)*X 1 1+(1352388707/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2652793193/5000000000 : ℝ)*X 2 0+(338097179/625000000 : ℝ)*X 2 1+(-240304801/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1078498719/2500000000 : ℝ)*X 0 0+(2245509943/5000000000 : ℝ)*X 0 1+(4143423243/10000000000 : ℝ)*X 0 2+(1078498719/2500000000 : ℝ)*X 1 0+(2245509943/5000000000 : ℝ)*X 1 1+(4143423243/10000000000 : ℝ)*X 1 2+(1078498719/2500000000 : ℝ)*X 2 0+(2245509943/5000000000 : ℝ)*X 2 1+(4143423243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (541826604869128338519658347/72437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1313553811/100000000000000 : ℝ)*(base19) + (343323647/25000000000000 : ℝ)*(base23) + (10992711/2500000000000 : ℝ)*(lower1) + (150996979/100000000000000 : ℝ)*(upper3) + (25029457/50000000000000 : ℝ)*(lower4) + (20435901/12500000000000 : ℝ)*(upper5) + (1126750439427133/25000000000000 : ℝ)*(major0) + (1126750439427133/25000000000000 : ℝ)*(major1) + (1126750439427133/25000000000000 : ℝ)*(major2) + (1310899979/100000000000000 : ℝ)*(sp0) + (6137118865117233/100000000000000 : ℝ)*(sp1) + (3068558775781711/50000000000000 : ℝ)*(sp2) + (3068558090461333/50000000000000 : ℝ)*(sp3) + (1438442200484593/50000000000000 : ℝ)*(sp4) + (1438442200484593/50000000000000 : ℝ)*(f.failure) + (6137118865117233/100000000000000 : ℝ)*(f.sum) + (532611090937/579500000000000000000000000 : ℝ)*base65 + (4071364021543405551/144875000000000000000000000000000 : ℝ)*base67 + (545002021322530551/144875000000000000000000000000000 : ℝ)*base69 + (2203356627819469449/144875000000000000000000000000000 : ℝ)*base72 + (1655525637527/579500000000000000000000000 : ℝ)*base73 + (25904074223588469449/144875000000000000000000000000000 : ℝ)*base76 + (684207255908530551/144875000000000000000000000000000 : ℝ)*base77 + (309302940759030551/144875000000000000000000000000000 : ℝ)*base79 + (5205668441769/1159000000000000000000000000 : ℝ)*base81 + (620233/1000000000000000000000 : ℝ)*base90 + (620233/1000000000000000000000 : ℝ)*base92 + (620233/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1391_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1391_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1391_box_0 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-919459859/5000000000 : ℝ)*x 0 + (2693939123/5000000000 : ℝ)*x 1 + (1077575489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (919459859/5000000000 : ℝ)^4351 ≤ (2729897771083/25000000000000 : ℝ)^3327 := by
    have hnat : (919459859 : ℕ)^4351*25000000000000^3327 ≤ 2729897771083^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919459859 5000000000 2729897771083 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693939123/5000000000 : ℝ)^4351 ≤ (22270104391743/50000000000000 : ℝ)^3327 := by
    have hnat : (2693939123 : ℕ)^4351*50000000000000^3327 ≤ 22270104391743^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693939123 5000000000 22270104391743 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077575489/2000000000 : ℝ)^4351 ≤ (22270100061889/50000000000000 : ℝ)^3327 := by
    have hnat : (1077575489 : ℕ)^4351*50000000000000^3327 ≤ 22270100061889^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077575489 2000000000 22270100061889 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-919459859/5000000000 : ℝ), (2693939123/5000000000 : ℝ), (1077575489/2000000000 : ℝ)] ![(2729897771083/25000000000000 : ℝ), (22270104391743/50000000000000 : ℝ), (22270100061889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-919459859/5000000000 : ℝ)|^4351 ≤ (2729897771083/25000000000000 : ℝ)^3327
        have hw : |(-919459859/5000000000 : ℝ)|=(919459859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693939123/5000000000 : ℝ)|^4351 ≤ (22270104391743/50000000000000 : ℝ)^3327
        have hw : |(2693939123/5000000000 : ℝ)|=(2693939123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077575489/2000000000 : ℝ)|^4351 ≤ (22270100061889/50000000000000 : ℝ)^3327
        have hw : |(1077575489/2000000000 : ℝ)|=(1077575489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_1 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642870541/5000000000 : ℝ)*x 0 + (-79163103/400000000 : ℝ)*x 1 + (2693939223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642870541/5000000000 : ℝ)^4351 ≤ (43439227022521/100000000000000 : ℝ)^3327 := by
    have hnat : (2642870541 : ℕ)^4351*100000000000000^3327 ≤ 43439227022521^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642870541 5000000000 43439227022521 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79163103/400000000 : ℝ)^4351 ≤ (3005140502517/25000000000000 : ℝ)^3327 := by
    have hnat : (79163103 : ℕ)^4351*25000000000000^3327 ≤ 3005140502517^3327*400000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79163103 400000000 3005140502517 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693939223/5000000000 : ℝ)^4351 ≤ (44540210945711/100000000000000 : ℝ)^3327 := by
    have hnat : (2693939223 : ℕ)^4351*100000000000000^3327 ≤ 44540210945711^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693939223 5000000000 44540210945711 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642870541/5000000000 : ℝ), (-79163103/400000000 : ℝ), (2693939223/5000000000 : ℝ)] ![(43439227022521/100000000000000 : ℝ), (3005140502517/25000000000000 : ℝ), (44540210945711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642870541/5000000000 : ℝ)|^4351 ≤ (43439227022521/100000000000000 : ℝ)^3327
        have hw : |(2642870541/5000000000 : ℝ)|=(2642870541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79163103/400000000 : ℝ)|^4351 ≤ (3005140502517/25000000000000 : ℝ)^3327
        have hw : |(-79163103/400000000 : ℝ)|=(79163103/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693939223/5000000000 : ℝ)|^4351 ≤ (44540210945711/100000000000000 : ℝ)^3327
        have hw : |(2693939223/5000000000 : ℝ)|=(2693939223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_2 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285739463/10000000000 : ℝ)*x 0 + (5387879313/10000000000 : ℝ)*x 1 + (-1979078587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285739463/10000000000 : ℝ)^4351 ≤ (21719604811059/50000000000000 : ℝ)^3327 := by
    have hnat : (5285739463 : ℕ)^4351*50000000000000^3327 ≤ 21719604811059^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285739463 10000000000 21719604811059 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387879313/10000000000 : ℝ)^4351 ≤ (44540220318953/100000000000000 : ℝ)^3327 := by
    have hnat : (5387879313 : ℕ)^4351*100000000000000^3327 ≤ 44540220318953^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387879313 10000000000 44540220318953 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1979078587/10000000000 : ℝ)^4351 ≤ (6010285024319/50000000000000 : ℝ)^3327 := by
    have hnat : (1979078587 : ℕ)^4351*50000000000000^3327 ≤ 6010285024319^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979078587 10000000000 6010285024319 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285739463/10000000000 : ℝ), (5387879313/10000000000 : ℝ), (-1979078587/10000000000 : ℝ)] ![(21719604811059/50000000000000 : ℝ), (44540220318953/100000000000000 : ℝ), (6010285024319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285739463/10000000000 : ℝ)|^4351 ≤ (21719604811059/50000000000000 : ℝ)^3327
        have hw : |(5285739463/10000000000 : ℝ)|=(5285739463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387879313/10000000000 : ℝ)|^4351 ≤ (44540220318953/100000000000000 : ℝ)^3327
        have hw : |(5387879313/10000000000 : ℝ)|=(5387879313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1979078587/10000000000 : ℝ)|^4351 ≤ (6010285024319/50000000000000 : ℝ)^3327
        have hw : |(-1979078587/10000000000 : ℝ)|=(1979078587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_3 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4461060149/10000000000 : ℝ)*x 0 + (4244208657/10000000000 : ℝ)*x 1 + (4244209907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4461060149/10000000000 : ℝ)^4351 ≤ (34796891683793/100000000000000 : ℝ)^3327 := by
    have hnat : (4461060149 : ℕ)^4351*100000000000000^3327 ≤ 34796891683793^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4461060149 10000000000 34796891683793 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244208657/10000000000 : ℝ)^4351 ≤ (32601547871963/100000000000000 : ℝ)^3327 := by
    have hnat : (4244208657 : ℕ)^4351*100000000000000^3327 ≤ 32601547871963^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244208657 10000000000 32601547871963 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244209907/10000000000 : ℝ)^4351 ≤ (32601560429019/100000000000000 : ℝ)^3327 := by
    have hnat : (4244209907 : ℕ)^4351*100000000000000^3327 ≤ 32601560429019^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244209907 10000000000 32601560429019 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4461060149/10000000000 : ℝ), (4244208657/10000000000 : ℝ), (4244209907/10000000000 : ℝ)] ![(34796891683793/100000000000000 : ℝ), (32601547871963/100000000000000 : ℝ), (32601560429019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4461060149/10000000000 : ℝ)|^4351 ≤ (34796891683793/100000000000000 : ℝ)^3327
        have hw : |(4461060149/10000000000 : ℝ)|=(4461060149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244208657/10000000000 : ℝ)|^4351 ≤ (32601547871963/100000000000000 : ℝ)^3327
        have hw : |(4244208657/10000000000 : ℝ)|=(4244208657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244209907/10000000000 : ℝ)|^4351 ≤ (32601560429019/100000000000000 : ℝ)^3327
        have hw : |(4244209907/10000000000 : ℝ)|=(4244209907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_4 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-17348783/80000000 : ℝ)*x 0 + (2632952373/5000000000 : ℝ)*x 1 + (263295253/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17348783/80000000 : ℝ)^4351 ≤ (846730192437/6250000000000 : ℝ)^3327 := by
    have hnat : (17348783 : ℕ)^4351*6250000000000^3327 ≤ 846730192437^3327*80000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17348783 80000000 846730192437 6250000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632952373/5000000000 : ℝ)^4351 ≤ (4322615676333/10000000000000 : ℝ)^3327 := by
    have hnat : (2632952373 : ℕ)^4351*10000000000000^3327 ≤ 4322615676333^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632952373 5000000000 4322615676333 10000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263295253/500000000 : ℝ)^4351 ≤ (43226160134181/100000000000000 : ℝ)^3327 := by
    have hnat : (263295253 : ℕ)^4351*100000000000000^3327 ≤ 43226160134181^3327*500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263295253 500000000 43226160134181 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17348783/80000000 : ℝ), (2632952373/5000000000 : ℝ), (263295253/500000000 : ℝ)] ![(846730192437/6250000000000 : ℝ), (4322615676333/10000000000000 : ℝ), (43226160134181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17348783/80000000 : ℝ)|^4351 ≤ (846730192437/6250000000000 : ℝ)^3327
        have hw : |(-17348783/80000000 : ℝ)|=(17348783/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632952373/5000000000 : ℝ)|^4351 ≤ (4322615676333/10000000000000 : ℝ)^3327
        have hw : |(2632952373/5000000000 : ℝ)|=(2632952373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263295253/500000000 : ℝ)|^4351 ≤ (43226160134181/100000000000000 : ℝ)^3327
        have hw : |(263295253/500000000 : ℝ)|=(263295253/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_5 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685618419/5000000000 : ℝ)*x 0 + (-253544111/1250000000 : ℝ)*x 1 + (2632952457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685618419/5000000000 : ℝ)^4351 ≤ (8872076414653/20000000000000 : ℝ)^3327 := by
    have hnat : (2685618419 : ℕ)^4351*20000000000000^3327 ≤ 8872076414653^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685618419 5000000000 8872076414653 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253544111/1250000000 : ℝ)^4351 ≤ (310336483589/2500000000000 : ℝ)^3327 := by
    have hnat : (253544111 : ℕ)^4351*2500000000000^3327 ≤ 310336483589^3327*1250000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253544111 1250000000 310336483589 2500000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632952457/5000000000 : ℝ)^4351 ≤ (21613079283421/50000000000000 : ℝ)^3327 := by
    have hnat : (2632952457 : ℕ)^4351*50000000000000^3327 ≤ 21613079283421^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632952457 5000000000 21613079283421 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685618419/5000000000 : ℝ), (-253544111/1250000000 : ℝ), (2632952457/5000000000 : ℝ)] ![(8872076414653/20000000000000 : ℝ), (310336483589/2500000000000 : ℝ), (21613079283421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685618419/5000000000 : ℝ)|^4351 ≤ (8872076414653/20000000000000 : ℝ)^3327
        have hw : |(2685618419/5000000000 : ℝ)|=(2685618419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253544111/1250000000 : ℝ)|^4351 ≤ (310336483589/2500000000000 : ℝ)^3327
        have hw : |(-253544111/1250000000 : ℝ)|=(253544111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632952457/5000000000 : ℝ)|^4351 ≤ (21613079283421/50000000000000 : ℝ)^3327
        have hw : |(2632952457/5000000000 : ℝ)|=(2632952457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_6 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371236891/10000000000 : ℝ)*x 0 + (1053180967/2000000000 : ℝ)*x 1 + (-2028352923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371236891/10000000000 : ℝ)^4351 ≤ (44360382645709/100000000000000 : ℝ)^3327 := by
    have hnat : (5371236891 : ℕ)^4351*100000000000000^3327 ≤ 44360382645709^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371236891 10000000000 44360382645709 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053180967/2000000000 : ℝ)^4351 ≤ (21613078859381/50000000000000 : ℝ)^3327 := by
    have hnat : (1053180967 : ℕ)^4351*50000000000000^3327 ≤ 21613078859381^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053180967 2000000000 21613078859381 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2028352923/10000000000 : ℝ)^4351 ≤ (6206729811843/50000000000000 : ℝ)^3327 := by
    have hnat : (2028352923 : ℕ)^4351*50000000000000^3327 ≤ 6206729811843^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028352923 10000000000 6206729811843 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371236891/10000000000 : ℝ), (1053180967/2000000000 : ℝ), (-2028352923/10000000000 : ℝ)] ![(44360382645709/100000000000000 : ℝ), (21613078859381/50000000000000 : ℝ), (6206729811843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371236891/10000000000 : ℝ)|^4351 ≤ (44360382645709/100000000000000 : ℝ)^3327
        have hw : |(5371236891/10000000000 : ℝ)|=(5371236891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053180967/2000000000 : ℝ)|^4351 ≤ (21613078859381/50000000000000 : ℝ)^3327
        have hw : |(1053180967/2000000000 : ℝ)|=(1053180967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2028352923/10000000000 : ℝ)|^4351 ≤ (6206729811843/50000000000000 : ℝ)^3327
        have hw : |(-2028352923/10000000000 : ℝ)|=(2028352923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_7 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2082941693/5000000000 : ℝ)*x 0 + (4391745699/10000000000 : ℝ)*x 1 + (2195872791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082941693/5000000000 : ℝ)^4351 ≤ (31816964299151/100000000000000 : ℝ)^3327 := by
    have hnat : (2082941693 : ℕ)^4351*100000000000000^3327 ≤ 31816964299151^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082941693 5000000000 31816964299151 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4391745699/10000000000 : ℝ)^4351 ≤ (8522879609867/25000000000000 : ℝ)^3327 := by
    have hnat : (4391745699 : ℕ)^4351*25000000000000^3327 ≤ 8522879609867^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391745699 10000000000 8522879609867 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195872791/5000000000 : ℝ)^4351 ≤ (34091517251701/100000000000000 : ℝ)^3327 := by
    have hnat : (2195872791 : ℕ)^4351*100000000000000^3327 ≤ 34091517251701^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195872791 5000000000 34091517251701 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2082941693/5000000000 : ℝ), (4391745699/10000000000 : ℝ), (2195872791/5000000000 : ℝ)] ![(31816964299151/100000000000000 : ℝ), (8522879609867/25000000000000 : ℝ), (34091517251701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2082941693/5000000000 : ℝ)|^4351 ≤ (31816964299151/100000000000000 : ℝ)^3327
        have hw : |(2082941693/5000000000 : ℝ)|=(2082941693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4391745699/10000000000 : ℝ)|^4351 ≤ (8522879609867/25000000000000 : ℝ)^3327
        have hw : |(4391745699/10000000000 : ℝ)|=(4391745699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2195872791/5000000000 : ℝ)|^4351 ≤ (34091517251701/100000000000000 : ℝ)^3327
        have hw : |(2195872791/5000000000 : ℝ)|=(2195872791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_8 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049622357/5000000000 : ℝ)*x 0 + (2590854829/5000000000 : ℝ)*x 1 + (5401874521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049622357/5000000000 : ℝ)^4351 ≤ (3245969240541/25000000000000 : ℝ)^3327 := by
    have hnat : (1049622357 : ℕ)^4351*25000000000000^3327 ≤ 3245969240541^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049622357 5000000000 3245969240541 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590854829/5000000000 : ℝ)^4351 ≤ (21162269180917/50000000000000 : ℝ)^3327 := by
    have hnat : (2590854829 : ℕ)^4351*50000000000000^3327 ≤ 21162269180917^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590854829 5000000000 21162269180917 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401874521/10000000000 : ℝ)^4351 ≤ (8938316934361/20000000000000 : ℝ)^3327 := by
    have hnat : (5401874521 : ℕ)^4351*20000000000000^3327 ≤ 8938316934361^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401874521 10000000000 8938316934361 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049622357/5000000000 : ℝ), (2590854829/5000000000 : ℝ), (5401874521/10000000000 : ℝ)] ![(3245969240541/25000000000000 : ℝ), (21162269180917/50000000000000 : ℝ), (8938316934361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049622357/5000000000 : ℝ)|^4351 ≤ (3245969240541/25000000000000 : ℝ)^3327
        have hw : |(-1049622357/5000000000 : ℝ)|=(1049622357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590854829/5000000000 : ℝ)|^4351 ≤ (21162269180917/50000000000000 : ℝ)^3327
        have hw : |(2590854829/5000000000 : ℝ)|=(2590854829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401874521/10000000000 : ℝ)|^4351 ≤ (8938316934361/20000000000000 : ℝ)^3327
        have hw : |(5401874521/10000000000 : ℝ)|=(5401874521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_9 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055185123/2000000000 : ℝ)*x 0 + (-493323861/2500000000 : ℝ)*x 1 + (5401874273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055185123/2000000000 : ℝ)^4351 ≤ (8666752845759/20000000000000 : ℝ)^3327 := by
    have hnat : (1055185123 : ℕ)^4351*20000000000000^3327 ≤ 8666752845759^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055185123 2000000000 8666752845759 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493323861/2500000000 : ℝ)^4351 ≤ (2993663440417/25000000000000 : ℝ)^3327 := by
    have hnat : (493323861 : ℕ)^4351*25000000000000^3327 ≤ 2993663440417^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493323861 2500000000 2993663440417 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401874273/10000000000 : ℝ)^4351 ≤ (8938316397701/20000000000000 : ℝ)^3327 := by
    have hnat : (5401874273 : ℕ)^4351*20000000000000^3327 ≤ 8938316397701^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401874273 10000000000 8938316397701 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055185123/2000000000 : ℝ), (-493323861/2500000000 : ℝ), (5401874273/10000000000 : ℝ)] ![(8666752845759/20000000000000 : ℝ), (2993663440417/25000000000000 : ℝ), (8938316397701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055185123/2000000000 : ℝ)|^4351 ≤ (8666752845759/20000000000000 : ℝ)^3327
        have hw : |(1055185123/2000000000 : ℝ)|=(1055185123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-493323861/2500000000 : ℝ)|^4351 ≤ (2993663440417/25000000000000 : ℝ)^3327
        have hw : |(-493323861/2500000000 : ℝ)|=(493323861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401874273/10000000000 : ℝ)|^4351 ≤ (8938316397701/20000000000000 : ℝ)^3327
        have hw : |(5401874273/10000000000 : ℝ)|=(5401874273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_10 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65949067/125000000 : ℝ)*x 0 + (2700937199/5000000000 : ℝ)*x 1 + (-1973295619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65949067/125000000 : ℝ)^4351 ≤ (21666880744859/50000000000000 : ℝ)^3327 := by
    have hnat : (65949067 : ℕ)^4351*50000000000000^3327 ≤ 21666880744859^3327*125000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65949067 125000000 21666880744859 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700937199/5000000000 : ℝ)^4351 ≤ (22345791670487/50000000000000 : ℝ)^3327 := by
    have hnat : (2700937199 : ℕ)^4351*50000000000000^3327 ≤ 22345791670487^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700937199 5000000000 22345791670487 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1973295619/10000000000 : ℝ)^4351 ≤ (5987327575243/50000000000000 : ℝ)^3327 := by
    have hnat : (1973295619 : ℕ)^4351*50000000000000^3327 ≤ 5987327575243^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973295619 10000000000 5987327575243 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65949067/125000000 : ℝ), (2700937199/5000000000 : ℝ), (-1973295619/10000000000 : ℝ)] ![(21666880744859/50000000000000 : ℝ), (22345791670487/50000000000000 : ℝ), (5987327575243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65949067/125000000 : ℝ)|^4351 ≤ (21666880744859/50000000000000 : ℝ)^3327
        have hw : |(65949067/125000000 : ℝ)|=(65949067/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700937199/5000000000 : ℝ)|^4351 ≤ (22345791670487/50000000000000 : ℝ)^3327
        have hw : |(2700937199/5000000000 : ℝ)|=(2700937199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1973295619/10000000000 : ℝ)|^4351 ≤ (5987327575243/50000000000000 : ℝ)^3327
        have hw : |(-1973295619/10000000000 : ℝ)|=(1973295619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_11 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (112359341/250000000 : ℝ)*x 0 + (4227265229/10000000000 : ℝ)*x 1 + (4227265321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112359341/250000000 : ℝ)^4351 ≤ (35137109265399/100000000000000 : ℝ)^3327 := by
    have hnat : (112359341 : ℕ)^4351*100000000000000^3327 ≤ 35137109265399^3327*250000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112359341 250000000 35137109265399 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227265229/10000000000 : ℝ)^4351 ≤ (6486288978823/20000000000000 : ℝ)^3327 := by
    have hnat : (4227265229 : ℕ)^4351*20000000000000^3327 ≤ 6486288978823^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227265229 10000000000 6486288978823 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227265321/10000000000 : ℝ)^4351 ≤ (16215722908589/50000000000000 : ℝ)^3327 := by
    have hnat : (4227265321 : ℕ)^4351*50000000000000^3327 ≤ 16215722908589^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227265321 10000000000 16215722908589 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112359341/250000000 : ℝ), (4227265229/10000000000 : ℝ), (4227265321/10000000000 : ℝ)] ![(35137109265399/100000000000000 : ℝ), (6486288978823/20000000000000 : ℝ), (16215722908589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112359341/250000000 : ℝ)|^4351 ≤ (35137109265399/100000000000000 : ℝ)^3327
        have hw : |(112359341/250000000 : ℝ)|=(112359341/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227265229/10000000000 : ℝ)|^4351 ≤ (6486288978823/20000000000000 : ℝ)^3327
        have hw : |(4227265229/10000000000 : ℝ)|=(4227265229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227265321/10000000000 : ℝ)|^4351 ≤ (16215722908589/50000000000000 : ℝ)^3327
        have hw : |(4227265321/10000000000 : ℝ)|=(4227265321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_12 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-954259221/5000000000 : ℝ)*x 0 + (5469973549/10000000000 : ℝ)*x 1 + (656849967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954259221/5000000000 : ℝ)^4351 ≤ (5731596976691/50000000000000 : ℝ)^3327 := by
    have hnat : (954259221 : ℕ)^4351*50000000000000^3327 ≤ 5731596976691^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954259221 5000000000 5731596976691 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469973549/10000000000 : ℝ)^4351 ≤ (9085964998923/20000000000000 : ℝ)^3327 := by
    have hnat : (5469973549 : ℕ)^4351*20000000000000^3327 ≤ 9085964998923^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469973549 10000000000 9085964998923 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656849967/1250000000 : ℝ)^4351 ≤ (43106981031983/100000000000000 : ℝ)^3327 := by
    have hnat : (656849967 : ℕ)^4351*100000000000000^3327 ≤ 43106981031983^3327*1250000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656849967 1250000000 43106981031983 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-954259221/5000000000 : ℝ), (5469973549/10000000000 : ℝ), (656849967/1250000000 : ℝ)] ![(5731596976691/50000000000000 : ℝ), (9085964998923/20000000000000 : ℝ), (43106981031983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-954259221/5000000000 : ℝ)|^4351 ≤ (5731596976691/50000000000000 : ℝ)^3327
        have hw : |(-954259221/5000000000 : ℝ)|=(954259221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469973549/10000000000 : ℝ)|^4351 ≤ (9085964998923/20000000000000 : ℝ)^3327
        have hw : |(5469973549/10000000000 : ℝ)|=(5469973549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656849967/1250000000 : ℝ)|^4351 ≤ (43106981031983/100000000000000 : ℝ)^3327
        have hw : |(656849967/1250000000 : ℝ)|=(656849967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_13 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689509431/5000000000 : ℝ)*x 0 + (-406547521/2000000000 : ℝ)*x 1 + (5254799853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689509431/5000000000 : ℝ)^4351 ≤ (44444453150627/100000000000000 : ℝ)^3327 := by
    have hnat : (2689509431 : ℕ)^4351*100000000000000^3327 ≤ 44444453150627^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689509431 5000000000 44444453150627 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (406547521/2000000000 : ℝ)^4351 ≤ (12448564550973/100000000000000 : ℝ)^3327 := by
    have hnat : (406547521 : ℕ)^4351*100000000000000^3327 ≤ 12448564550973^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406547521 2000000000 12448564550973 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254799853/10000000000 : ℝ)^4351 ≤ (8621396457437/20000000000000 : ℝ)^3327 := by
    have hnat : (5254799853 : ℕ)^4351*20000000000000^3327 ≤ 8621396457437^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254799853 10000000000 8621396457437 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689509431/5000000000 : ℝ), (-406547521/2000000000 : ℝ), (5254799853/10000000000 : ℝ)] ![(44444453150627/100000000000000 : ℝ), (12448564550973/100000000000000 : ℝ), (8621396457437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689509431/5000000000 : ℝ)|^4351 ≤ (44444453150627/100000000000000 : ℝ)^3327
        have hw : |(2689509431/5000000000 : ℝ)|=(2689509431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-406547521/2000000000 : ℝ)|^4351 ≤ (12448564550973/100000000000000 : ℝ)^3327
        have hw : |(-406547521/2000000000 : ℝ)|=(406547521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254799853/10000000000 : ℝ)|^4351 ≤ (8621396457437/20000000000000 : ℝ)^3327
        have hw : |(5254799853/10000000000 : ℝ)|=(5254799853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_14 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672377341/1250000000 : ℝ)*x 0 + (5254800059/10000000000 : ℝ)*x 1 + (-203273751/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672377341/1250000000 : ℝ)^4351 ≤ (4444445170267/10000000000000 : ℝ)^3327 := by
    have hnat : (672377341 : ℕ)^4351*10000000000000^3327 ≤ 4444445170267^3327*1250000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672377341 1250000000 4444445170267 10000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254800059/10000000000 : ℝ)^4351 ≤ (21553492248599/50000000000000 : ℝ)^3327 := by
    have hnat : (5254800059 : ℕ)^4351*50000000000000^3327 ≤ 21553492248599^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254800059 10000000000 21553492248599 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203273751/1000000000 : ℝ)^4351 ≤ (99588510321/800000000000 : ℝ)^3327 := by
    have hnat : (203273751 : ℕ)^4351*800000000000^3327 ≤ 99588510321^3327*1000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203273751 1000000000 99588510321 800000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672377341/1250000000 : ℝ), (5254800059/10000000000 : ℝ), (-203273751/1000000000 : ℝ)] ![(4444445170267/10000000000000 : ℝ), (21553492248599/50000000000000 : ℝ), (99588510321/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672377341/1250000000 : ℝ)|^4351 ≤ (4444445170267/10000000000000 : ℝ)^3327
        have hw : |(672377341/1250000000 : ℝ)|=(672377341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254800059/10000000000 : ℝ)|^4351 ≤ (21553492248599/50000000000000 : ℝ)^3327
        have hw : |(5254800059/10000000000 : ℝ)|=(5254800059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203273751/1000000000 : ℝ)|^4351 ≤ (99588510321/800000000000 : ℝ)^3327
        have hw : |(-203273751/1000000000 : ℝ)|=(203273751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_box_15 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (206928009/500000000 : ℝ)*x 0 + (176206691/400000000 : ℝ)*x 1 + (275322937/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206928009/500000000 : ℝ)^4351 ≤ (3154433010267/10000000000000 : ℝ)^3327 := by
    have hnat : (206928009 : ℕ)^4351*10000000000000^3327 ≤ 3154433010267^3327*500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206928009 500000000 3154433010267 10000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176206691/400000000 : ℝ)^4351 ≤ (6845567276161/20000000000000 : ℝ)^3327 := by
    have hnat : (176206691 : ℕ)^4351*20000000000000^3327 ≤ 6845567276161^3327*400000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176206691 400000000 6845567276161 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275322937/625000000 : ℝ)^4351 ≤ (34227833505131/100000000000000 : ℝ)^3327 := by
    have hnat : (275322937 : ℕ)^4351*100000000000000^3327 ≤ 34227833505131^3327*625000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275322937 625000000 34227833505131 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206928009/500000000 : ℝ), (176206691/400000000 : ℝ), (275322937/625000000 : ℝ)] ![(3154433010267/10000000000000 : ℝ), (6845567276161/20000000000000 : ℝ), (34227833505131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206928009/500000000 : ℝ)|^4351 ≤ (3154433010267/10000000000000 : ℝ)^3327
        have hw : |(206928009/500000000 : ℝ)|=(206928009/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(176206691/400000000 : ℝ)|^4351 ≤ (6845567276161/20000000000000 : ℝ)^3327
        have hw : |(176206691/400000000 : ℝ)|=(176206691/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275322937/625000000 : ℝ)|^4351 ≤ (34227833505131/100000000000000 : ℝ)^3327
        have hw : |(275322937/625000000 : ℝ)|=(275322937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1391_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31439/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59037/100000 : ℝ) ∧ (20059/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84541/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (563/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (563/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (563/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (563/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (563/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (563/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (563/5000 : ℝ) ^ (2175/512 : ℝ) ≤ (9351701236927807/100000000000000000000 : ℝ) := by
    have hpowers : (563/5000 : ℝ)^2175 ≤ (9351701236927807/100000000000000000000 : ℝ)^512 := by
      have hnat : (563 : ℕ)^2175*100000000000000000000^512 ≤ 9351701236927807^512*5000^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 5000 9351701236927807 100000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/5000 : ℝ)) (X := (9351701236927807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hpowhi : (921/6250 : ℝ) ^ (2175/512 : ℝ) ≤ (29324972477875121/100000000000000000000 : ℝ) := by
    have hpowers : (921/6250 : ℝ)^2175 ≤ (29324972477875121/100000000000000000000 : ℝ)^512 := by
      have hnat : (921 : ℕ)^2175*100000000000000000000^512 ≤ 29324972477875121^512*6250^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        921 6250 29324972477875121 100000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (921/6250 : ℝ)) (X := (29324972477875121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009351701236927807/50000000000000000000 : ℝ) ≤ (5000220125457933/5000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (50009351701236927807/50000000000000000000 : ℝ)^512 ≤ (5000220125457933/5000000000000000 : ℝ)^2175 := by
      have hnat : (50009351701236927807 : ℕ)^512*5000000000000000^2175 ≤ 5000220125457933^2175*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009351701236927807 50000000000000000000 5000220125457933 5000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000220125457933/5000000000000000 : ℝ)) (X := (50009351701236927807/50000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252417292107175183/6250000000000000000 : ℝ) ≤ (10000910323200329/10000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (6252417292107175183/6250000000000000000 : ℝ)^512 ≤ (10000910323200329/10000000000000000 : ℝ)^2175 := by
      have hnat : (6252417292107175183 : ℕ)^512*10000000000000000^2175 ≤ 10000910323200329^2175*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252417292107175183 6250000000000000000 10000910323200329 10000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000910323200329/10000000000000000 : ℝ)) (X := (6252417292107175183/6250000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029324972477875121/50000000000000000000 : ℝ) ≤ (1250172549435599/1250000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (50029324972477875121/50000000000000000000 : ℝ)^512 ≤ (1250172549435599/1250000000000000 : ℝ)^2175 := by
      have hnat : (50029324972477875121 : ℕ)^512*1250000000000000^2175 ≤ 1250172549435599^2175*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029324972477875121 50000000000000000000 1250172549435599 1250000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250172549435599/1250000000000000 : ℝ)) (X := (50029324972477875121/50000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9351701236927807/100000000000000000000 : ℝ) ≤ ((271491752221386277/271562500000000000 : ℝ)+2*(470072284463/347600000000000 : ℝ)*(563/5000 : ℝ))^(2175/512 : ℝ) := by
    rw [show (271491752221386277/271562500000000000 : ℝ)+2*(470072284463/347600000000000 : ℝ)*(563/5000 : ℝ)=(5000220125457933/5000000000000000 : ℝ) by norm_num, show 1+2*(9351701236927807/100000000000000000000 : ℝ)=(50009351701236927807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29324972477875121/100000000000000000000 : ℝ)+(9351701236927807/100000000000000000000 : ℝ) ≤ ((271491752221386277/271562500000000000 : ℝ)+(470072284463/347600000000000 : ℝ)*((921/6250 : ℝ)+(563/5000 : ℝ)))^(2175/512 : ℝ) := by
    rw [show (271491752221386277/271562500000000000 : ℝ)+(470072284463/347600000000000 : ℝ)*((921/6250 : ℝ)+(563/5000 : ℝ))=(10000910323200329/10000000000000000 : ℝ) by norm_num, show 1+(29324972477875121/100000000000000000000 : ℝ)+(9351701236927807/100000000000000000000 : ℝ)=(6252417292107175183/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29324972477875121/100000000000000000000 : ℝ) ≤ ((271491752221386277/271562500000000000 : ℝ)+2*(470072284463/347600000000000 : ℝ)*(921/6250 : ℝ))^(2175/512 : ℝ) := by
    rw [show (271491752221386277/271562500000000000 : ℝ)+2*(470072284463/347600000000000 : ℝ)*(921/6250 : ℝ)=(1250172549435599/1250000000000000 : ℝ) by norm_num, show 1+2*(29324972477875121/100000000000000000000 : ℝ)=(50029324972477875121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (271491752221386277/271562500000000000 : ℝ)*(X 1 0+X 2 0)+(470072284463/347600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (271491752221386277/271562500000000000 : ℝ)) (alpha := (470072284463/347600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (271491752221386277/271562500000000000 : ℝ)*(X 0 1+X 2 1)+(470072284463/347600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (271491752221386277/271562500000000000 : ℝ)) (alpha := (470072284463/347600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (271491752221386277/271562500000000000 : ℝ)*(X 0 2+X 1 2)+(470072284463/347600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (271491752221386277/271562500000000000 : ℝ)) (alpha := (470072284463/347600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-919459859/5000000000 : ℝ)*X 0 0+(2693939123/5000000000 : ℝ)*X 0 1+(1077575489/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642870541/5000000000 : ℝ)*X 1 0+(-79163103/400000000 : ℝ)*X 1 1+(2693939223/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285739463/10000000000 : ℝ)*X 2 0+(5387879313/10000000000 : ℝ)*X 2 1+(-1979078587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4461060149/10000000000 : ℝ)*X 0 0+(4244208657/10000000000 : ℝ)*X 0 1+(4244209907/10000000000 : ℝ)*X 0 2+(4461060149/10000000000 : ℝ)*X 1 0+(4244208657/10000000000 : ℝ)*X 1 1+(4244209907/10000000000 : ℝ)*X 1 2+(4461060149/10000000000 : ℝ)*X 2 0+(4244208657/10000000000 : ℝ)*X 2 1+(4244209907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-17348783/80000000 : ℝ)*X 0 0+(2632952373/5000000000 : ℝ)*X 0 1+(263295253/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685618419/5000000000 : ℝ)*X 1 0+(-253544111/1250000000 : ℝ)*X 1 1+(2632952457/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5371236891/10000000000 : ℝ)*X 2 0+(1053180967/2000000000 : ℝ)*X 2 1+(-2028352923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2082941693/5000000000 : ℝ)*X 0 0+(4391745699/10000000000 : ℝ)*X 0 1+(2195872791/5000000000 : ℝ)*X 0 2+(2082941693/5000000000 : ℝ)*X 1 0+(4391745699/10000000000 : ℝ)*X 1 1+(2195872791/5000000000 : ℝ)*X 1 2+(2082941693/5000000000 : ℝ)*X 2 0+(4391745699/10000000000 : ℝ)*X 2 1+(2195872791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1049622357/5000000000 : ℝ)*X 0 0+(2590854829/5000000000 : ℝ)*X 0 1+(5401874521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1055185123/2000000000 : ℝ)*X 1 0+(-493323861/2500000000 : ℝ)*X 1 1+(5401874273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((65949067/125000000 : ℝ)*X 2 0+(2700937199/5000000000 : ℝ)*X 2 1+(-1973295619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((112359341/250000000 : ℝ)*X 0 0+(4227265229/10000000000 : ℝ)*X 0 1+(4227265321/10000000000 : ℝ)*X 0 2+(112359341/250000000 : ℝ)*X 1 0+(4227265229/10000000000 : ℝ)*X 1 1+(4227265321/10000000000 : ℝ)*X 1 2+(112359341/250000000 : ℝ)*X 2 0+(4227265229/10000000000 : ℝ)*X 2 1+(4227265321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-954259221/5000000000 : ℝ)*X 0 0+(5469973549/10000000000 : ℝ)*X 0 1+(656849967/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2689509431/5000000000 : ℝ)*X 1 0+(-406547521/2000000000 : ℝ)*X 1 1+(5254799853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672377341/1250000000 : ℝ)*X 2 0+(5254800059/10000000000 : ℝ)*X 2 1+(-203273751/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((206928009/500000000 : ℝ)*X 0 0+(176206691/400000000 : ℝ)*X 0 1+(275322937/625000000 : ℝ)*X 0 2+(206928009/500000000 : ℝ)*X 1 0+(176206691/400000000 : ℝ)*X 1 1+(275322937/625000000 : ℝ)*X 1 2+(206928009/500000000 : ℝ)*X 2 0+(176206691/400000000 : ℝ)*X 2 1+(275322937/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31439/50000 : ℝ) ≤ (-4268645242473646194237511964721/6789062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (4701697/20000000000000 : ℝ)*(upper1) + (1963887/100000000000000 : ℝ)*(lower4) + (121527/20000000000000 : ℝ)*(upper5) + (1487528676373147/50000000000000 : ℝ)*(major0) + (1487528676373147/50000000000000 : ℝ)*(major1) + (1487528676373147/50000000000000 : ℝ)*(major2) + (2501824693/100000000000000 : ℝ)*(sp1) + (2627874187/50000000000000 : ℝ)*(sp2) + (2599515883/100000000000000 : ℝ)*(sp3) + (2036023063748817/50000000000000 : ℝ)*(sp4) + (2036024256628337/50000000000000 : ℝ)*(sp5) + (4072045759332993/100000000000000 : ℝ)*(sp6) + (1899019533205903/100000000000000 : ℝ)*(sp7) + (1221895933/25000000000000 : ℝ)*(sp12) + (949511066360893/50000000000000 : ℝ)*(f.failure) + (2036025507540683/50000000000000 : ℝ)*(f.sum) + (62429385106329/8690000000000000000000000000 : ℝ)*base66 + (445496119177980501/54312500000000000000000000000000 : ℝ)*base67 + (668241997848543001/54312500000000000000000000000000 : ℝ)*base69 + (304466510927543001/54312500000000000000000000000000 : ℝ)*base71 + (43841175388229/8690000000000000000000000000 : ℝ)*base74 + (546851370359918001/54312500000000000000000000000000 : ℝ)*base75 + (352552990527355501/54312500000000000000000000000000 : ℝ)*base77 + (539205147767668001/54312500000000000000000000000000 : ℝ)*base79 + (175150756439/8690000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (779467/1000000000000000000000 : ℝ)*base89 + (779467/1000000000000000000000 : ℝ)*base91 + (779467/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59037/100000 : ℝ) ≤ (2004122732026009577778969157047/3394531250000000000000000000000 : ℝ) := by norm_num
    linear_combination (130787451/100000000000000 : ℝ)*(lower0) + (204443/80000000000 : ℝ)*(upper2) + (97757971/20000000000000 : ℝ)*(lower4) + (190337226475149/6250000000000 : ℝ)*(major0) + (190337226475149/6250000000000 : ℝ)*(major1) + (190337226475149/6250000000000 : ℝ)*(major2) + (2063595512854017/50000000000000 : ℝ)*(sp0) + (4127157133525291/100000000000000 : ℝ)*(sp1) + (257947877565633/6250000000000 : ℝ)*(sp2) + (971959028192577/50000000000000 : ℝ)*(sp3) + (34129101537/100000000000000 : ℝ)*(sp5) + (25221576701/100000000000000 : ℝ)*(sp6) + (31434951/1562500000000 : ℝ)*(sp7) + (118459397/50000000000000 : ℝ)*(sp12) + (971960034111009/50000000000000 : ℝ)*(f.failure) + (1031797815656707/25000000000000 : ℝ)*(f.sum) + (15344663985551/2172500000000000000000000000 : ℝ)*base66 + (24821065032855467/6789062500000000000000000000000 : ℝ)*base67 + (120152723172980467/6789062500000000000000000000000 : ℝ)*base69 + (9008812052304199/848632812500000000000000000000 : ℝ)*base71 + (6605841171063/4345000000000000000000000000 : ℝ)*base73 + (40525561941138671/3394531250000000000000000000000 : ℝ)*base75 + (122055453060257809/13578125000000000000000000000000 : ℝ)*base77 + (49785472579757809/13578125000000000000000000000000 : ℝ)*base79 + (1527789990333/4345000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2398329/1000000000000000000000 : ℝ)*base90 + (2398329/1000000000000000000000 : ℝ)*base92 + (2398329/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (20059/25000 : ℝ) ≤ (10894919016159360350225001264249/13578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3643279/25000000000000 : ℝ)*(upper1) + (57786017/50000000000000 : ℝ)*(upper2) + (11338099/25000000000000 : ℝ)*(lower5) + (838814183510087/25000000000000 : ℝ)*(major0) + (838814183510087/25000000000000 : ℝ)*(major1) + (838814183510087/25000000000000 : ℝ)*(major2) + (127598461/50000000000000 : ℝ)*(sp2) + (9426051429/25000000000000 : ℝ)*(sp3) + (1051431199/50000000000000 : ℝ)*(sp4) + (141939109127327/3125000000000 : ℝ)*(sp8) + (908411663777779/20000000000000 : ℝ)*(sp9) + (4542058063691973/100000000000000 : ℝ)*(sp10) + (1070835595967643/50000000000000 : ℝ)*(sp11) + (4723952033/100000000000000 : ℝ)*(sp12) + (1070854448070501/50000000000000 : ℝ)*(f.failure) + (908411663777779/20000000000000 : ℝ)*(f.sum) + (5627966933959/4345000000000000000000000000 : ℝ)*base66 + (84150110011586229/27156250000000000000000000000000 : ℝ)*base68 + (24609832463320021/27156250000000000000000000000000 : ℝ)*base69 + (191478362072351271/27156250000000000000000000000000 : ℝ)*base71 + (19431888262189/4345000000000000000000000000 : ℝ)*base74 + (205672244069976271/27156250000000000000000000000000 : ℝ)*base75 + (257709122637070021/27156250000000000000000000000000 : ℝ)*base77 + (202076968578820021/27156250000000000000000000000000 : ℝ)*base79 + (3202538135521/1086250000000000000000000000 : ℝ)*base82 + (5922019/1000000000000000000000 : ℝ)*base89 + (5922019/1000000000000000000000 : ℝ)*base91 + (5922019/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84541/100000 : ℝ) ≤ (-11478758143141726598682289738641/13578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35450609/50000000000000 : ℝ)*(lower0) + (35742801/100000000000000 : ℝ)*(upper3) + (54426907/100000000000000 : ℝ)*(upper5) + (848073310995803/25000000000000 : ℝ)*(major0) + (848073310995803/25000000000000 : ℝ)*(major1) + (848073310995803/25000000000000 : ℝ)*(major2) + (129960349/25000000000000 : ℝ)*(sp0) + (80024652867/100000000000000 : ℝ)*(sp5) + (4588043449/20000000000000 : ℝ)*(sp7) + (6838827131/100000000000000 : ℝ)*(sp8) + (4647408829925189/100000000000000 : ℝ)*(sp12) + (4647336163940849/100000000000000 : ℝ)*(sp13) + (1161854047148429/25000000000000 : ℝ)*(sp14) + (108266344791607/5000000000000 : ℝ)*(sp15) + (433069967209877/20000000000000 : ℝ)*(f.failure) + (1161854047148429/25000000000000 : ℝ)*(f.sum) + (3705313353861/4345000000000000000000000000 : ℝ)*base66 + (135470476327334849/27156250000000000000000000000000 : ℝ)*base67 + (232283840541866099/27156250000000000000000000000000 : ℝ)*base69 + (57973082831834849/27156250000000000000000000000000 : ℝ)*base71 + (30482094533959/4345000000000000000000000000 : ℝ)*base73 + (132069373943741099/27156250000000000000000000000000 : ℝ)*base75 + (59844016368834849/27156250000000000000000000000000 : ℝ)*base77 + (203056927728553599/27156250000000000000000000000000 : ℝ)*base79 + (2042087796839/4345000000000000000000000000 : ℝ)*base81 + (90163/400000000000000000000 : ℝ)*base89 + (90163/400000000000000000000 : ℝ)*base91 + (90163/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1391_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31439/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59037/100000 : ℝ) else (20059/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84541/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1391_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1391_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31439/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59037/100000 : ℝ) else (20059/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84541/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1391_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1391_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1391_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31439/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59037/100000 : ℝ) else (20059/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84541/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1391_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
