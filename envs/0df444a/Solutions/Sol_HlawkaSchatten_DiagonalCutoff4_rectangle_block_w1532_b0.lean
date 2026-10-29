-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1532_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:29.890197+00:00
-- url     : https://prove2.me/submissions/fef84d20-b273-4d26-b659-608a781545fd

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
theorem support_rectangle_w1532_s0_0 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16648263/100000000 : ℝ)*x 0 + (184299837/312500000 : ℝ)*x 1 + (2431889689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16648263/100000000 : ℝ)^4561 ≤ (1238388100603/12500000000000 : ℝ)^3537 := by
    have hnat : (16648263 : ℕ)^4561*12500000000000^3537 ≤ 1238388100603^3537*100000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16648263 100000000 1238388100603 12500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184299837/312500000 : ℝ)^4561 ≤ (12653854429043/25000000000000 : ℝ)^3537 := by
    have hnat : (184299837 : ℕ)^4561*25000000000000^3537 ≤ 12653854429043^3537*312500000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184299837 312500000 12653854429043 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2431889689/5000000000 : ℝ)^4561 ≤ (39477477461661/100000000000000 : ℝ)^3537 := by
    have hnat : (2431889689 : ℕ)^4561*100000000000000^3537 ≤ 39477477461661^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431889689 5000000000 39477477461661 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16648263/100000000 : ℝ), (184299837/312500000 : ℝ), (2431889689/5000000000 : ℝ)] ![(1238388100603/12500000000000 : ℝ), (12653854429043/25000000000000 : ℝ), (39477477461661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16648263/100000000 : ℝ)|^4561 ≤ (1238388100603/12500000000000 : ℝ)^3537
        have hw : |(-16648263/100000000 : ℝ)|=(16648263/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(184299837/312500000 : ℝ)|^4561 ≤ (12653854429043/25000000000000 : ℝ)^3537
        have hw : |(184299837/312500000 : ℝ)|=(184299837/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2431889689/5000000000 : ℝ)|^4561 ≤ (39477477461661/100000000000000 : ℝ)^3537
        have hw : |(2431889689/5000000000 : ℝ)|=(2431889689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s0_1 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1368410337/2500000000 : ℝ)*x 0 + (-560706239/2500000000 : ℝ)*x 1 + (4863779289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1368410337/2500000000 : ℝ)^4561 ≤ (1436661686843/3125000000000 : ℝ)^3537 := by
    have hnat : (1368410337 : ℕ)^4561*3125000000000^3537 ≤ 1436661686843^3537*2500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368410337 2500000000 1436661686843 3125000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560706239/2500000000 : ℝ)^4561 ≤ (14549349476429/100000000000000 : ℝ)^3537 := by
    have hnat : (560706239 : ℕ)^4561*100000000000000^3537 ≤ 14549349476429^3537*2500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560706239 2500000000 14549349476429 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4863779289/10000000000 : ℝ)^4561 ≤ (1233671141567/3125000000000 : ℝ)^3537 := by
    have hnat : (4863779289 : ℕ)^4561*3125000000000^3537 ≤ 1233671141567^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4863779289 10000000000 1233671141567 3125000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1368410337/2500000000 : ℝ), (-560706239/2500000000 : ℝ), (4863779289/10000000000 : ℝ)] ![(1436661686843/3125000000000 : ℝ), (14549349476429/100000000000000 : ℝ), (1233671141567/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1368410337/2500000000 : ℝ)|^4561 ≤ (1436661686843/3125000000000 : ℝ)^3537
        have hw : |(1368410337/2500000000 : ℝ)|=(1368410337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560706239/2500000000 : ℝ)|^4561 ≤ (14549349476429/100000000000000 : ℝ)^3537
        have hw : |(-560706239/2500000000 : ℝ)|=(560706239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4863779289/10000000000 : ℝ)|^4561 ≤ (1233671141567/3125000000000 : ℝ)^3537
        have hw : |(4863779289/10000000000 : ℝ)|=(4863779289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s0_2 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (68420519/125000000 : ℝ)*x 0 + (486377939/1000000000 : ℝ)*x 1 + (-2242824607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68420519/125000000 : ℝ)^4561 ≤ (22986587920921/50000000000000 : ℝ)^3537 := by
    have hnat : (68420519 : ℕ)^4561*50000000000000^3537 ≤ 22986587920921^3537*125000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68420519 125000000 22986587920921 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486377939/1000000000 : ℝ)^4561 ≤ (39477477587259/100000000000000 : ℝ)^3537 := by
    have hnat : (486377939 : ℕ)^4561*100000000000000^3537 ≤ 39477477587259^3537*1000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486377939 1000000000 39477477587259 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242824607/10000000000 : ℝ)^4561 ≤ (3637336639249/25000000000000 : ℝ)^3537 := by
    have hnat : (2242824607 : ℕ)^4561*25000000000000^3537 ≤ 3637336639249^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242824607 10000000000 3637336639249 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68420519/125000000 : ℝ), (486377939/1000000000 : ℝ), (-2242824607/10000000000 : ℝ)] ![(22986587920921/50000000000000 : ℝ), (39477477587259/100000000000000 : ℝ), (3637336639249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68420519/125000000 : ℝ)|^4561 ≤ (22986587920921/50000000000000 : ℝ)^3537
        have hw : |(68420519/125000000 : ℝ)|=(68420519/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(486377939/1000000000 : ℝ)|^4561 ≤ (39477477587259/100000000000000 : ℝ)^3537
        have hw : |(486377939/1000000000 : ℝ)|=(486377939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2242824607/10000000000 : ℝ)|^4561 ≤ (3637336639249/25000000000000 : ℝ)^3537
        have hw : |(-2242824607/10000000000 : ℝ)|=(2242824607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s0_3 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4139793647/10000000000 : ℝ)*x 0 + (30916071/100000000 : ℝ)*x 1 + (2734473687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4139793647/10000000000 : ℝ)^4561 ≤ (32069327767193/100000000000000 : ℝ)^3537 := by
    have hnat : (4139793647 : ℕ)^4561*100000000000000^3537 ≤ 32069327767193^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139793647 10000000000 32069327767193 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30916071/100000000 : ℝ)^4561 ≤ (22008330557621/100000000000000 : ℝ)^3537 := by
    have hnat : (30916071 : ℕ)^4561*100000000000000^3537 ≤ 22008330557621^3537*100000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30916071 100000000 22008330557621 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734473687/5000000000 : ℝ)^4561 ≤ (45922341660677/100000000000000 : ℝ)^3537 := by
    have hnat : (2734473687 : ℕ)^4561*100000000000000^3537 ≤ 45922341660677^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734473687 5000000000 45922341660677 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4139793647/10000000000 : ℝ), (30916071/100000000 : ℝ), (2734473687/5000000000 : ℝ)] ![(32069327767193/100000000000000 : ℝ), (22008330557621/100000000000000 : ℝ), (45922341660677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4139793647/10000000000 : ℝ)|^4561 ≤ (32069327767193/100000000000000 : ℝ)^3537
        have hw : |(4139793647/10000000000 : ℝ)|=(4139793647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30916071/100000000 : ℝ)|^4561 ≤ (22008330557621/100000000000000 : ℝ)^3537
        have hw : |(30916071/100000000 : ℝ)|=(30916071/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734473687/5000000000 : ℝ)|^4561 ≤ (45922341660677/100000000000000 : ℝ)^3537
        have hw : |(2734473687/5000000000 : ℝ)|=(2734473687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s0_4 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-834089617/5000000000 : ℝ)*x 0 + (4890045899/10000000000 : ℝ)*x 1 + (2935195307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834089617/5000000000 : ℝ)^4561 ≤ (4966420797439/50000000000000 : ℝ)^3537 := by
    have hnat : (834089617 : ℕ)^4561*50000000000000^3537 ≤ 4966420797439^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834089617 5000000000 4966420797439 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4890045899/10000000000 : ℝ)^4561 ≤ (7950522010119/20000000000000 : ℝ)^3537 := by
    have hnat : (4890045899 : ℕ)^4561*20000000000000^3537 ≤ 7950522010119^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4890045899 10000000000 7950522010119 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2935195307/5000000000 : ℝ)^4561 ≤ (50314548339623/100000000000000 : ℝ)^3537 := by
    have hnat : (2935195307 : ℕ)^4561*100000000000000^3537 ≤ 50314548339623^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935195307 5000000000 50314548339623 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-834089617/5000000000 : ℝ), (4890045899/10000000000 : ℝ), (2935195307/5000000000 : ℝ)] ![(4966420797439/50000000000000 : ℝ), (7950522010119/20000000000000 : ℝ), (50314548339623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-834089617/5000000000 : ℝ)|^4561 ≤ (4966420797439/50000000000000 : ℝ)^3537
        have hw : |(-834089617/5000000000 : ℝ)|=(834089617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4890045899/10000000000 : ℝ)|^4561 ≤ (7950522010119/20000000000000 : ℝ)^3537
        have hw : |(4890045899/10000000000 : ℝ)|=(4890045899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2935195307/5000000000 : ℝ)|^4561 ≤ (50314548339623/100000000000000 : ℝ)^3537
        have hw : |(2935195307/5000000000 : ℝ)|=(2935195307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s0_5 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191113031/10000000000 : ℝ)*x 0 + (-154526729/1250000000 : ℝ)*x 1 + (1467597671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191113031/10000000000 : ℝ)^4561 ≤ (4293636719419/10000000000000 : ℝ)^3537 := by
    have hnat : (5191113031 : ℕ)^4561*10000000000000^3537 ≤ 4293636719419^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191113031 10000000000 4293636719419 10000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154526729/1250000000 : ℝ)^4561 ≤ (3374541840253/50000000000000 : ℝ)^3537 := by
    have hnat : (154526729 : ℕ)^4561*50000000000000^3537 ≤ 3374541840253^3537*1250000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154526729 1250000000 3374541840253 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1467597671/2500000000 : ℝ)^4561 ≤ (25157274556641/50000000000000 : ℝ)^3537 := by
    have hnat : (1467597671 : ℕ)^4561*50000000000000^3537 ≤ 25157274556641^3537*2500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1467597671 2500000000 25157274556641 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191113031/10000000000 : ℝ), (-154526729/1250000000 : ℝ), (1467597671/2500000000 : ℝ)] ![(4293636719419/10000000000000 : ℝ), (3374541840253/50000000000000 : ℝ), (25157274556641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191113031/10000000000 : ℝ)|^4561 ≤ (4293636719419/10000000000000 : ℝ)^3537
        have hw : |(5191113031/10000000000 : ℝ)|=(5191113031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-154526729/1250000000 : ℝ)|^4561 ≤ (3374541840253/50000000000000 : ℝ)^3537
        have hw : |(-154526729/1250000000 : ℝ)|=(154526729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1467597671/2500000000 : ℝ)|^4561 ≤ (25157274556641/50000000000000 : ℝ)^3537
        have hw : |(1467597671/2500000000 : ℝ)|=(1467597671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s0_6 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191112991/10000000000 : ℝ)*x 0 + (733798869/1250000000 : ℝ)*x 1 + (-1236213473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191112991/10000000000 : ℝ)^4561 ≤ (21468183383781/50000000000000 : ℝ)^3537 := by
    have hnat : (5191112991 : ℕ)^4561*50000000000000^3537 ≤ 21468183383781^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191112991 10000000000 21468183383781 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733798869/1250000000 : ℝ)^4561 ≤ (50314552075291/100000000000000 : ℝ)^3537 := by
    have hnat : (733798869 : ℕ)^4561*100000000000000^3537 ≤ 50314552075291^3537*1250000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733798869 1250000000 50314552075291 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1236213473/10000000000 : ℝ)^4561 ≤ (2159705969/32000000000 : ℝ)^3537 := by
    have hnat : (1236213473 : ℕ)^4561*32000000000^3537 ≤ 2159705969^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236213473 10000000000 2159705969 32000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191112991/10000000000 : ℝ), (733798869/1250000000 : ℝ), (-1236213473/10000000000 : ℝ)] ![(21468183383781/50000000000000 : ℝ), (50314552075291/100000000000000 : ℝ), (2159705969/32000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191112991/10000000000 : ℝ)|^4561 ≤ (21468183383781/50000000000000 : ℝ)^3537
        have hw : |(5191112991/10000000000 : ℝ)|=(5191112991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(733798869/1250000000 : ℝ)|^4561 ≤ (50314552075291/100000000000000 : ℝ)^3537
        have hw : |(733798869/1250000000 : ℝ)|=(733798869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1236213473/10000000000 : ℝ)|^4561 ≤ (2159705969/32000000000 : ℝ)^3537
        have hw : |(-1236213473/10000000000 : ℝ)|=(1236213473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s0_7 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4147503711/10000000000 : ℝ)*x 0 + (216341821/400000000 : ℝ)*x 1 + (788541341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4147503711/10000000000 : ℝ)^4561 ≤ (32146366862671/100000000000000 : ℝ)^3537 := by
    have hnat : (4147503711 : ℕ)^4561*100000000000000^3537 ≤ 32146366862671^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147503711 10000000000 32146366862671 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216341821/400000000 : ℝ)^4561 ≤ (1414667601969/3125000000000 : ℝ)^3537 := by
    have hnat : (216341821 : ℕ)^4561*3125000000000^3537 ≤ 1414667601969^3537*400000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216341821 400000000 1414667601969 3125000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788541341/2500000000 : ℝ)^4561 ≤ (11292134929121/50000000000000 : ℝ)^3537 := by
    have hnat : (788541341 : ℕ)^4561*50000000000000^3537 ≤ 11292134929121^3537*2500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788541341 2500000000 11292134929121 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4147503711/10000000000 : ℝ), (216341821/400000000 : ℝ), (788541341/2500000000 : ℝ)] ![(32146366862671/100000000000000 : ℝ), (1414667601969/3125000000000 : ℝ), (11292134929121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4147503711/10000000000 : ℝ)|^4561 ≤ (32146366862671/100000000000000 : ℝ)^3537
        have hw : |(4147503711/10000000000 : ℝ)|=(4147503711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216341821/400000000 : ℝ)|^4561 ≤ (1414667601969/3125000000000 : ℝ)^3537
        have hw : |(216341821/400000000 : ℝ)|=(216341821/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(788541341/2500000000 : ℝ)|^4561 ≤ (11292134929121/50000000000000 : ℝ)^3537
        have hw : |(788541341/2500000000 : ℝ)|=(788541341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1532_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3081/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6307/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4559/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4559 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4559*1^1024 ≤ 0^1024*1^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4559/1024 : ℝ) ≤ (1691655839221126461/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4559 ≤ (1691655839221126461/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4559*100000000000000000000^1024 ≤ 1691655839221126461^1024*5^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1691655839221126461 100000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1691655839221126461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4559 := by
      have hnat : (1 : ℕ)^1024*1^4559 ≤ 1^4559*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101691655839221126461/100000000000000000000 : ℝ) ≤ (1254718707691301/1250000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (101691655839221126461/100000000000000000000 : ℝ)^1024 ≤ (1254718707691301/1250000000000000 : ℝ)^4559 := by
      have hnat : (101691655839221126461 : ℕ)^1024*1250000000000000^4559 ≤ 1254718707691301^4559*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101691655839221126461 100000000000000000000 1254718707691301 1250000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254718707691301/1250000000000000 : ℝ)) (X := (101691655839221126461/100000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51691655839221126461/50000000000000000000 : ℝ) ≤ (629718707691301/625000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (51691655839221126461/50000000000000000000 : ℝ)^1024 ≤ (629718707691301/625000000000000 : ℝ)^4559 := by
      have hnat : (51691655839221126461 : ℕ)^1024*625000000000000^4559 ≤ 629718707691301^4559*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51691655839221126461 50000000000000000000 629718707691301 625000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (629718707691301/625000000000000 : ℝ)) (X := (51691655839221126461/50000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4718707691301/500000000000000 : ℝ)*(0 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4718707691301/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1691655839221126461/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4718707691301/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4559/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4718707691301/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1254718707691301/1250000000000000 : ℝ) by norm_num, show 1+(1691655839221126461/100000000000000000000 : ℝ)+(0 : ℝ)=(101691655839221126461/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1691655839221126461/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4718707691301/500000000000000 : ℝ)*(2/5 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4718707691301/500000000000000 : ℝ)*(2/5 : ℝ)=(629718707691301/625000000000000 : ℝ) by norm_num, show 1+2*(1691655839221126461/100000000000000000000 : ℝ)=(51691655839221126461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4718707691301/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4718707691301/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4718707691301/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4718707691301/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4718707691301/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4718707691301/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16648263/100000000 : ℝ)*X 0 0+(184299837/312500000 : ℝ)*X 0 1+(2431889689/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1368410337/2500000000 : ℝ)*X 1 0+(-560706239/2500000000 : ℝ)*X 1 1+(4863779289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((68420519/125000000 : ℝ)*X 2 0+(486377939/1000000000 : ℝ)*X 2 1+(-2242824607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4139793647/10000000000 : ℝ)*X 0 0+(30916071/100000000 : ℝ)*X 0 1+(2734473687/5000000000 : ℝ)*X 0 2+(4139793647/10000000000 : ℝ)*X 1 0+(30916071/100000000 : ℝ)*X 1 1+(2734473687/5000000000 : ℝ)*X 1 2+(4139793647/10000000000 : ℝ)*X 2 0+(30916071/100000000 : ℝ)*X 2 1+(2734473687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-834089617/5000000000 : ℝ)*X 0 0+(4890045899/10000000000 : ℝ)*X 0 1+(2935195307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5191113031/10000000000 : ℝ)*X 1 0+(-154526729/1250000000 : ℝ)*X 1 1+(1467597671/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5191112991/10000000000 : ℝ)*X 2 0+(733798869/1250000000 : ℝ)*X 2 1+(-1236213473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4147503711/10000000000 : ℝ)*X 0 0+(216341821/400000000 : ℝ)*X 0 1+(788541341/2500000000 : ℝ)*X 0 2+(4147503711/10000000000 : ℝ)*X 1 0+(216341821/400000000 : ℝ)*X 1 1+(788541341/2500000000 : ℝ)*X 1 2+(4147503711/10000000000 : ℝ)*X 2 0+(216341821/400000000 : ℝ)*X 2 1+(788541341/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188425978001321581016493/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24898003/100000000000000 : ℝ)*(base1) + (361048087/20000000000000 : ℝ)*(base19) + (458909069/25000000000000 : ℝ)*(base23) + (185967311/100000000000000 : ℝ)*(upper3) + (147948503/50000000000000 : ℝ)*(upper5) + (693974010558531/100000000000000 : ℝ)*(major0) + (693974010558531/100000000000000 : ℝ)*(major1) + (693974010558531/100000000000000 : ℝ)*(major2) + (967296643050959/100000000000000 : ℝ)*(sp0) + (483650985420767/50000000000000 : ℝ)*(sp1) + (967301940445693/100000000000000 : ℝ)*(sp2) + (52580141094861/12500000000000 : ℝ)*(sp3) + (7157929013/100000000000000 : ℝ)*(sp4) + (71003589/2500000000000 : ℝ)*(sp7) + (105160998450113/25000000000000 : ℝ)*(f.failure) + (967303776081969/100000000000000 : ℝ)*(f.sum) + (732408811169/25000000000000000000000000000 : ℝ)*base66 + (485470572888831/50000000000000000000000000000 : ℝ)*base67 + (114748631761169/50000000000000000000000000000 : ℝ)*base70 + (78208363638831/50000000000000000000000000000 : ℝ)*base71 + (107913757638831/25000000000000000000000000000 : ℝ)*base73 + (114217723861169/50000000000000000000000000000 : ℝ)*base76 + (4382912761169/50000000000000000000000000000 : ℝ)*base78 + (84005486538831/50000000000000000000000000000 : ℝ)*base79 + (41858667486169/25000000000000000000000000000 : ℝ)*base82 + (3760223/1250000000000000000000 : ℝ)*base89 + (3760223/1250000000000000000000 : ℝ)*base91 + (3760223/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (196591627018347535414893/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (874520501/50000000000000 : ℝ)*(base19) + (882754741/50000000000000 : ℝ)*(base23) + (3632297/50000000000000 : ℝ)*(base32) + (26172393/10000000000000 : ℝ)*(upper3) + (233061009/100000000000000 : ℝ)*(upper5) + (731815211998669/100000000000000 : ℝ)*(major0) + (731815211998669/100000000000000 : ℝ)*(major1) + (731815211998669/100000000000000 : ℝ)*(major2) + (232315081/5000000000000 : ℝ)*(sp1) + (1273325757/25000000000000 : ℝ)*(sp2) + (1020049179280023/100000000000000 : ℝ)*(sp4) + (1020042783937401/100000000000000 : ℝ)*(sp5) + (1020042320467513/100000000000000 : ℝ)*(sp6) + (110895243832637/25000000000000 : ℝ)*(sp7) + (221790491297571/50000000000000 : ℝ)*(f.failure) + (1020049179280023/100000000000000 : ℝ)*(f.sum) + (54779656271631/25000000000000000000000000000 : ℝ)*base66 + (40022206028369/50000000000000000000000000000 : ℝ)*base67 + (328788695178369/50000000000000000000000000000 : ℝ)*base69 + (210649883928369/50000000000000000000000000000 : ℝ)*base71 + (103820083821631/25000000000000000000000000000 : ℝ)*base74 + (169997878078369/50000000000000000000000000000 : ℝ)*base75 + (330673496328369/50000000000000000000000000000 : ℝ)*base77 + (214595774921631/50000000000000000000000000000 : ℝ)*base80 + (837704203369/25000000000000000000000000000 : ℝ)*base81 + (10374941/2500000000000000000000 : ℝ)*base89 + (10374941/2500000000000000000000 : ℝ)*base91 + (10374941/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1532_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3081/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6307/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1532_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1532_s1_0 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-906613343/5000000000 : ℝ)*x 0 + (2778786671/5000000000 : ℝ)*x 1 + (102166661/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (906613343/5000000000 : ℝ)^4561 ≤ (11060274712093/100000000000000 : ℝ)^3537 := by
    have hnat : (906613343 : ℕ)^4561*100000000000000^3537 ≤ 11060274712093^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906613343 5000000000 11060274712093 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2778786671/5000000000 : ℝ)^4561 ≤ (5860527456807/12500000000000 : ℝ)^3537 := by
    have hnat : (2778786671 : ℕ)^4561*12500000000000^3537 ≤ 5860527456807^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2778786671 5000000000 5860527456807 12500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102166661/200000000 : ℝ)^4561 ≤ (10513876404107/25000000000000 : ℝ)^3537 := by
    have hnat : (102166661 : ℕ)^4561*25000000000000^3537 ≤ 10513876404107^3537*200000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102166661 200000000 10513876404107 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-906613343/5000000000 : ℝ), (2778786671/5000000000 : ℝ), (102166661/200000000 : ℝ)] ![(11060274712093/100000000000000 : ℝ), (5860527456807/12500000000000 : ℝ), (10513876404107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-906613343/5000000000 : ℝ)|^4561 ≤ (11060274712093/100000000000000 : ℝ)^3537
        have hw : |(-906613343/5000000000 : ℝ)|=(906613343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2778786671/5000000000 : ℝ)|^4561 ≤ (5860527456807/12500000000000 : ℝ)^3537
        have hw : |(2778786671/5000000000 : ℝ)|=(2778786671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(102166661/200000000 : ℝ)|^4561 ≤ (10513876404107/25000000000000 : ℝ)^3537
        have hw : |(102166661/200000000 : ℝ)|=(102166661/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s1_1 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076604781/2000000000 : ℝ)*x 0 + (-819683/4000000 : ℝ)*x 1 + (255416747/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076604781/2000000000 : ℝ)^4561 ≤ (44994092516119/100000000000000 : ℝ)^3537 := by
    have hnat : (1076604781 : ℕ)^4561*100000000000000^3537 ≤ 44994092516119^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076604781 2000000000 44994092516119 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (819683/4000000 : ℝ)^4561 ≤ (1618797723771/12500000000000 : ℝ)^3537 := by
    have hnat : (819683 : ℕ)^4561*12500000000000^3537 ≤ 1618797723771^3537*4000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819683 4000000 1618797723771 12500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255416747/500000000 : ℝ)^4561 ≤ (10513881420257/25000000000000 : ℝ)^3537 := by
    have hnat : (255416747 : ℕ)^4561*25000000000000^3537 ≤ 10513881420257^3537*500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255416747 500000000 10513881420257 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076604781/2000000000 : ℝ), (-819683/4000000 : ℝ), (255416747/500000000 : ℝ)] ![(44994092516119/100000000000000 : ℝ), (1618797723771/12500000000000 : ℝ), (10513881420257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076604781/2000000000 : ℝ)|^4561 ≤ (44994092516119/100000000000000 : ℝ)^3537
        have hw : |(1076604781/2000000000 : ℝ)|=(1076604781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-819683/4000000 : ℝ)|^4561 ≤ (1618797723771/12500000000000 : ℝ)^3537
        have hw : |(-819683/4000000 : ℝ)|=(819683/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(255416747/500000000 : ℝ)|^4561 ≤ (10513881420257/25000000000000 : ℝ)^3537
        have hw : |(255416747/500000000 : ℝ)|=(255416747/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s1_2 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383025709/10000000000 : ℝ)*x 0 + (5108332653/10000000000 : ℝ)*x 1 + (-2049208093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383025709/10000000000 : ℝ)^4561 ≤ (44994111960349/100000000000000 : ℝ)^3537 := by
    have hnat : (5383025709 : ℕ)^4561*100000000000000^3537 ≤ 44994111960349^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383025709 10000000000 44994111960349 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5108332653/10000000000 : ℝ)^4561 ≤ (42055501401801/100000000000000 : ℝ)^3537 := by
    have hnat : (5108332653 : ℕ)^4561*100000000000000^3537 ≤ 42055501401801^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5108332653 10000000000 42055501401801 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2049208093/10000000000 : ℝ)^4561 ≤ (6475193311359/50000000000000 : ℝ)^3537 := by
    have hnat : (2049208093 : ℕ)^4561*50000000000000^3537 ≤ 6475193311359^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049208093 10000000000 6475193311359 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383025709/10000000000 : ℝ), (5108332653/10000000000 : ℝ), (-2049208093/10000000000 : ℝ)] ![(44994111960349/100000000000000 : ℝ), (42055501401801/100000000000000 : ℝ), (6475193311359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383025709/10000000000 : ℝ)|^4561 ≤ (44994111960349/100000000000000 : ℝ)^3537
        have hw : |(5383025709/10000000000 : ℝ)|=(5383025709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5108332653/10000000000 : ℝ)|^4561 ≤ (42055501401801/100000000000000 : ℝ)^3537
        have hw : |(5108332653/10000000000 : ℝ)|=(5108332653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2049208093/10000000000 : ℝ)|^4561 ≤ (6475193311359/50000000000000 : ℝ)^3537
        have hw : |(-2049208093/10000000000 : ℝ)|=(2049208093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s1_3 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530288841/1250000000 : ℝ)*x 0 + (93797721/250000000 : ℝ)*x 1 + (2392484731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530288841/1250000000 : ℝ)^4561 ≤ (33097053982167/100000000000000 : ℝ)^3537 := by
    have hnat : (530288841 : ℕ)^4561*100000000000000^3537 ≤ 33097053982167^3537*1250000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530288841 1250000000 33097053982167 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93797721/250000000 : ℝ)^4561 ≤ (7062097133751/25000000000000 : ℝ)^3537 := by
    have hnat : (93797721 : ℕ)^4561*25000000000000^3537 ≤ 7062097133751^3537*250000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93797721 250000000 7062097133751 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2392484731/5000000000 : ℝ)^4561 ≤ (2415909842319/6250000000000 : ℝ)^3537 := by
    have hnat : (2392484731 : ℕ)^4561*6250000000000^3537 ≤ 2415909842319^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392484731 5000000000 2415909842319 6250000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530288841/1250000000 : ℝ), (93797721/250000000 : ℝ), (2392484731/5000000000 : ℝ)] ![(33097053982167/100000000000000 : ℝ), (7062097133751/25000000000000 : ℝ), (2415909842319/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530288841/1250000000 : ℝ)|^4561 ≤ (33097053982167/100000000000000 : ℝ)^3537
        have hw : |(530288841/1250000000 : ℝ)|=(530288841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(93797721/250000000 : ℝ)|^4561 ≤ (7062097133751/25000000000000 : ℝ)^3537
        have hw : |(93797721/250000000 : ℝ)|=(93797721/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2392484731/5000000000 : ℝ)|^4561 ≤ (2415909842319/6250000000000 : ℝ)^3537
        have hw : |(2392484731/5000000000 : ℝ)|=(2392484731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s1_4 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1813493159/10000000000 : ℝ)*x 0 + (2556609279/5000000000 : ℝ)*x 1 + (5552611629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1813493159/10000000000 : ℝ)^4561 ≤ (2212474152067/20000000000000 : ℝ)^3537 := by
    have hnat : (1813493159 : ℕ)^4561*20000000000000^3537 ≤ 2212474152067^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813493159 10000000000 2212474152067 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2556609279/5000000000 : ℝ)^4561 ≤ (8421475654881/20000000000000 : ℝ)^3537 := by
    have hnat : (2556609279 : ℕ)^4561*20000000000000^3537 ≤ 8421475654881^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556609279 5000000000 8421475654881 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5552611629/10000000000 : ℝ)^4561 ≤ (374642007593/800000000000 : ℝ)^3537 := by
    have hnat : (5552611629 : ℕ)^4561*800000000000^3537 ≤ 374642007593^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5552611629 10000000000 374642007593 800000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1813493159/10000000000 : ℝ), (2556609279/5000000000 : ℝ), (5552611629/10000000000 : ℝ)] ![(2212474152067/20000000000000 : ℝ), (8421475654881/20000000000000 : ℝ), (374642007593/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1813493159/10000000000 : ℝ)|^4561 ≤ (2212474152067/20000000000000 : ℝ)^3537
        have hw : |(-1813493159/10000000000 : ℝ)|=(1813493159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2556609279/5000000000 : ℝ)|^4561 ≤ (8421475654881/20000000000000 : ℝ)^3537
        have hw : |(2556609279/5000000000 : ℝ)|=(2556609279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5552611629/10000000000 : ℝ)|^4561 ≤ (374642007593/800000000000 : ℝ)^3537
        have hw : |(5552611629/10000000000 : ℝ)|=(5552611629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s1_5 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052884517/2000000000 : ℝ)*x 0 + (-1604929209/10000000000 : ℝ)*x 1 + (1110522347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052884517/2000000000 : ℝ)^4561 ≤ (2732491176107/6250000000000 : ℝ)^3537 := by
    have hnat : (1052884517 : ℕ)^4561*6250000000000^3537 ≤ 2732491176107^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052884517 2000000000 2732491176107 6250000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1604929209/10000000000 : ℝ)^4561 ≤ (1889977812473/20000000000000 : ℝ)^3537 := by
    have hnat : (1604929209 : ℕ)^4561*20000000000000^3537 ≤ 1889977812473^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604929209 10000000000 1889977812473 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110522347/2000000000 : ℝ)^4561 ≤ (46830252101941/100000000000000 : ℝ)^3537 := by
    have hnat : (1110522347 : ℕ)^4561*100000000000000^3537 ≤ 46830252101941^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110522347 2000000000 46830252101941 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052884517/2000000000 : ℝ), (-1604929209/10000000000 : ℝ), (1110522347/2000000000 : ℝ)] ![(2732491176107/6250000000000 : ℝ), (1889977812473/20000000000000 : ℝ), (46830252101941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052884517/2000000000 : ℝ)|^4561 ≤ (2732491176107/6250000000000 : ℝ)^3537
        have hw : |(1052884517/2000000000 : ℝ)|=(1052884517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1604929209/10000000000 : ℝ)|^4561 ≤ (1889977812473/20000000000000 : ℝ)^3537
        have hw : |(-1604929209/10000000000 : ℝ)|=(1604929209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1110522347/2000000000 : ℝ)|^4561 ≤ (46830252101941/100000000000000 : ℝ)^3537
        have hw : |(1110522347/2000000000 : ℝ)|=(1110522347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s1_6 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316105633/2500000000 : ℝ)*x 0 + (2776305907/5000000000 : ℝ)*x 1 + (-160492917/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316105633/2500000000 : ℝ)^4561 ≤ (4371985825013/10000000000000 : ℝ)^3537 := by
    have hnat : (1316105633 : ℕ)^4561*10000000000000^3537 ≤ 4371985825013^3537*2500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316105633 2500000000 4371985825013 10000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2776305907/5000000000 : ℝ)^4561 ≤ (9366050592223/20000000000000 : ℝ)^3537 := by
    have hnat : (2776305907 : ℕ)^4561*20000000000000^3537 ≤ 9366050592223^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2776305907 5000000000 9366050592223 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160492917/1000000000 : ℝ)^4561 ≤ (7559911013/80000000000 : ℝ)^3537 := by
    have hnat : (160492917 : ℕ)^4561*80000000000^3537 ≤ 7559911013^3537*1000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160492917 1000000000 7559911013 80000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316105633/2500000000 : ℝ), (2776305907/5000000000 : ℝ), (-160492917/1000000000 : ℝ)] ![(4371985825013/10000000000000 : ℝ), (9366050592223/20000000000000 : ℝ), (7559911013/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316105633/2500000000 : ℝ)|^4561 ≤ (4371985825013/10000000000000 : ℝ)^3537
        have hw : |(1316105633/2500000000 : ℝ)|=(1316105633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2776305907/5000000000 : ℝ)|^4561 ≤ (9366050592223/20000000000000 : ℝ)^3537
        have hw : |(2776305907/5000000000 : ℝ)|=(2776305907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-160492917/1000000000 : ℝ)|^4561 ≤ (7559911013/80000000000 : ℝ)^3537
        have hw : |(-160492917/1000000000 : ℝ)|=(160492917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s1_7 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121462719/5000000000 : ℝ)*x 0 + (954747133/2000000000 : ℝ)*x 1 + (752663213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121462719/5000000000 : ℝ)^4561 ≤ (33103238292329/100000000000000 : ℝ)^3537 := by
    have hnat : (2121462719 : ℕ)^4561*100000000000000^3537 ≤ 33103238292329^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121462719 5000000000 33103238292329 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (954747133/2000000000 : ℝ)^4561 ≤ (7707514751883/20000000000000 : ℝ)^3537 := by
    have hnat : (954747133 : ℕ)^4561*20000000000000^3537 ≤ 7707514751883^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954747133 2000000000 7707514751883 20000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752663213/2000000000 : ℝ)^4561 ≤ (14179593963717/50000000000000 : ℝ)^3537 := by
    have hnat : (752663213 : ℕ)^4561*50000000000000^3537 ≤ 14179593963717^3537*2000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752663213 2000000000 14179593963717 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121462719/5000000000 : ℝ), (954747133/2000000000 : ℝ), (752663213/2000000000 : ℝ)] ![(33103238292329/100000000000000 : ℝ), (7707514751883/20000000000000 : ℝ), (14179593963717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121462719/5000000000 : ℝ)|^4561 ≤ (33103238292329/100000000000000 : ℝ)^3537
        have hw : |(2121462719/5000000000 : ℝ)|=(2121462719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(954747133/2000000000 : ℝ)|^4561 ≤ (7707514751883/20000000000000 : ℝ)^3537
        have hw : |(954747133/2000000000 : ℝ)|=(954747133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(752663213/2000000000 : ℝ)|^4561 ≤ (14179593963717/50000000000000 : ℝ)^3537
        have hw : |(752663213/2000000000 : ℝ)|=(752663213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1532_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6307/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1077/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9061/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6307/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6307/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6307/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6307/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6307/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6307/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3081/100000 : ℝ) ^ (4559/1024 : ℝ) ≤ (4670583220553/25000000000000000000 : ℝ) := by
    have hpowers : (3081/100000 : ℝ)^4559 ≤ (4670583220553/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3081 : ℕ)^4559*25000000000000000000^1024 ≤ 4670583220553^1024*100000^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3081 100000 4670583220553 25000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3081/100000 : ℝ)) (X := (4670583220553/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6307/25000 : ℝ) ^ (4559/1024 : ℝ) ≤ (54329230092674147/25000000000000000000 : ℝ) := by
    have hpowers : (6307/25000 : ℝ)^4559 ≤ (54329230092674147/25000000000000000000 : ℝ)^1024 := by
      have hnat : (6307 : ℕ)^4559*25000000000000000000^1024 ≤ 54329230092674147^1024*25000^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6307 25000 54329230092674147 25000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6307/25000 : ℝ)) (X := (54329230092674147/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500004670583220553/12500000000000000000 : ℝ) ≤ (1250000104906263/1250000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (12500004670583220553/12500000000000000000 : ℝ)^1024 ≤ (1250000104906263/1250000000000000 : ℝ)^4559 := by
      have hnat : (12500004670583220553 : ℕ)^1024*1250000000000000^4559 ≤ 1250000104906263^4559*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500004670583220553 12500000000000000000 1250000104906263 1250000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000104906263/1250000000000000 : ℝ)) (X := (12500004670583220553/12500000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (250543339006758947/250000000000000000 : ℝ) ≤ (2501219370345963/2500000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (250543339006758947/250000000000000000 : ℝ)^1024 ≤ (2501219370345963/2500000000000000 : ℝ)^4559 := by
      have hnat : (250543339006758947 : ℕ)^1024*2500000000000000^4559 ≤ 2501219370345963^4559*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250543339006758947 250000000000000000 2501219370345963 2500000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501219370345963/2500000000000000 : ℝ)) (X := (250543339006758947/250000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12554329230092674147/12500000000000000000 : ℝ) ≤ (12512192654397/12500000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (12554329230092674147/12500000000000000000 : ℝ)^1024 ≤ (12512192654397/12500000000000 : ℝ)^4559 := by
      have hnat : (12554329230092674147 : ℕ)^1024*12500000000000^4559 ≤ 12512192654397^4559*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12554329230092674147 12500000000000000000 12512192654397 12500000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12512192654397/12500000000000 : ℝ)) (X := (12554329230092674147/12500000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4670583220553/25000000000000000000 : ℝ) ≤ ((864999877804858977/865117187500000000 : ℝ)+2*(1219160533437/553675000000000 : ℝ)*(3081/100000 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (864999877804858977/865117187500000000 : ℝ)+2*(1219160533437/553675000000000 : ℝ)*(3081/100000 : ℝ)=(1250000104906263/1250000000000000 : ℝ) by norm_num, show 1+2*(4670583220553/25000000000000000000 : ℝ)=(12500004670583220553/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54329230092674147/25000000000000000000 : ℝ)+(4670583220553/25000000000000000000 : ℝ) ≤ ((864999877804858977/865117187500000000 : ℝ)+(1219160533437/553675000000000 : ℝ)*((6307/25000 : ℝ)+(3081/100000 : ℝ)))^(4559/1024 : ℝ) := by
    rw [show (864999877804858977/865117187500000000 : ℝ)+(1219160533437/553675000000000 : ℝ)*((6307/25000 : ℝ)+(3081/100000 : ℝ))=(2501219370345963/2500000000000000 : ℝ) by norm_num, show 1+(54329230092674147/25000000000000000000 : ℝ)+(4670583220553/25000000000000000000 : ℝ)=(250543339006758947/250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54329230092674147/25000000000000000000 : ℝ) ≤ ((864999877804858977/865117187500000000 : ℝ)+2*(1219160533437/553675000000000 : ℝ)*(6307/25000 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (864999877804858977/865117187500000000 : ℝ)+2*(1219160533437/553675000000000 : ℝ)*(6307/25000 : ℝ)=(12512192654397/12500000000000 : ℝ) by norm_num, show 1+2*(54329230092674147/25000000000000000000 : ℝ)=(12554329230092674147/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (864999877804858977/865117187500000000 : ℝ)*(X 1 0+X 2 0)+(1219160533437/553675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (3081/100000 : ℝ)) (hi := (6307/25000 : ℝ)) (c := (864999877804858977/865117187500000000 : ℝ)) (alpha := (1219160533437/553675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (864999877804858977/865117187500000000 : ℝ)*(X 0 1+X 2 1)+(1219160533437/553675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (3081/100000 : ℝ)) (hi := (6307/25000 : ℝ)) (c := (864999877804858977/865117187500000000 : ℝ)) (alpha := (1219160533437/553675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (864999877804858977/865117187500000000 : ℝ)*(X 0 2+X 1 2)+(1219160533437/553675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (3081/100000 : ℝ)) (hi := (6307/25000 : ℝ)) (c := (864999877804858977/865117187500000000 : ℝ)) (alpha := (1219160533437/553675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-906613343/5000000000 : ℝ)*X 0 0+(2778786671/5000000000 : ℝ)*X 0 1+(102166661/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1076604781/2000000000 : ℝ)*X 1 0+(-819683/4000000 : ℝ)*X 1 1+(255416747/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5383025709/10000000000 : ℝ)*X 2 0+(5108332653/10000000000 : ℝ)*X 2 1+(-2049208093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((530288841/1250000000 : ℝ)*X 0 0+(93797721/250000000 : ℝ)*X 0 1+(2392484731/5000000000 : ℝ)*X 0 2+(530288841/1250000000 : ℝ)*X 1 0+(93797721/250000000 : ℝ)*X 1 1+(2392484731/5000000000 : ℝ)*X 1 2+(530288841/1250000000 : ℝ)*X 2 0+(93797721/250000000 : ℝ)*X 2 1+(2392484731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1813493159/10000000000 : ℝ)*X 0 0+(2556609279/5000000000 : ℝ)*X 0 1+(5552611629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1052884517/2000000000 : ℝ)*X 1 0+(-1604929209/10000000000 : ℝ)*X 1 1+(1110522347/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1316105633/2500000000 : ℝ)*X 2 0+(2776305907/5000000000 : ℝ)*X 2 1+(-160492917/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2121462719/5000000000 : ℝ)*X 0 0+(954747133/2000000000 : ℝ)*X 0 1+(752663213/2000000000 : ℝ)*X 0 2+(2121462719/5000000000 : ℝ)*X 1 0+(954747133/2000000000 : ℝ)*X 1 1+(752663213/2000000000 : ℝ)*X 1 2+(2121462719/5000000000 : ℝ)*X 2 0+(954747133/2000000000 : ℝ)*X 2 1+(752663213/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1003469503208244381536271753/86511718750000000000000000000000 : ℝ) := by norm_num
    linear_combination (968858103/100000000000000 : ℝ)*(base19) + (758824417/50000000000000 : ℝ)*(base23) + (162019123/50000000000000 : ℝ)*(upper3) + (21231213/20000000000000 : ℝ)*(upper4) + (11889401/100000000000000 : ℝ)*(upper5) + (399251779853161/25000000000000 : ℝ)*(major0) + (399251779853161/25000000000000 : ℝ)*(major1) + (399251779853161/25000000000000 : ℝ)*(major2) + (1112997182438013/50000000000000 : ℝ)*(sp0) + (2226006239537207/100000000000000 : ℝ)*(sp1) + (2226005690746477/100000000000000 : ℝ)*(sp2) + (968000540678279/100000000000000 : ℝ)*(sp3) + (3210879821/25000000000000 : ℝ)*(sp4) + (3051555313/50000000000000 : ℝ)*(sp7) + (193601328757781/20000000000000 : ℝ)*(f.failure) + (222600720839531/10000000000000 : ℝ)*(f.sum) + (98980529487917/27683750000000000000000000000 : ℝ)*base66 + (245084154777080249/173023437500000000000000000000000 : ℝ)*base68 + (111783433385014563/86511718750000000000000000000000 : ℝ)*base69 + (1958646122261769873/346046875000000000000000000000000 : ℝ)*base72 + (48520679575269/55367500000000000000000000000 : ℝ)*base74 + (161630680333780719/43255859375000000000000000000000 : ℝ)*base75 + (1153825477310613623/346046875000000000000000000000000 : ℝ)*base78 + (1248579215260394873/346046875000000000000000000000000 : ℝ)*base80 + (239507323432867/110735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1823851/1000000000000000000000 : ℝ)*base89 + (1823851/1000000000000000000000 : ℝ)*base91 + (1823851/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (682553761457831100891611547/173023437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (640461597/100000000000000 : ℝ)*(base19) + (711052169/100000000000000 : ℝ)*(base23) + (109673639/100000000000000 : ℝ)*(upper3) + (35040269/100000000000000 : ℝ)*(lower4) + (59176253/100000000000000 : ℝ)*(upper5) + (1632776828497747/100000000000000 : ℝ)*(major0) + (1632776828497747/100000000000000 : ℝ)*(major1) + (1632776828497747/100000000000000 : ℝ)*(major2) + (4485687229/100000000000000 : ℝ)*(sp1) + (710188793/12500000000000 : ℝ)*(sp2) + (2275865503074899/100000000000000 : ℝ)*(sp4) + (2275860376926073/100000000000000 : ℝ)*(sp5) + (1137929555256193/50000000000000 : ℝ)*(sp6) + (989688022425157/100000000000000 : ℝ)*(sp7) + (989688022425157/100000000000000 : ℝ)*(f.failure) + (2275865503074899/100000000000000 : ℝ)*(f.sum) + (616087713964381/110735000000000000000000000000 : ℝ)*base65 + (983086923897560099/346046875000000000000000000000000 : ℝ)*base68 + (558977400242915263/173023437500000000000000000000000 : ℝ)*base69 + (581632390134477763/173023437500000000000000000000000 : ℝ)*base71 + (16532997502369/27683750000000000000000000000 : ℝ)*base73 + (812569643662696513/173023437500000000000000000000000 : ℝ)*base75 + (35179250265227389/21627929687500000000000000000000 : ℝ)*base78 + (719942908891221151/346046875000000000000000000000000 : ℝ)*base79 + (174564483244901/110735000000000000000000000000 : ℝ)*base81 + (11978053/5000000000000000000000 : ℝ)*base90 + (11978053/5000000000000000000000 : ℝ)*base92 + (11978053/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1532_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6307/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1077/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9061/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1532_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1532_s2_0 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1835539711/10000000000 : ℝ)*x 0 + (2725893661/5000000000 : ℝ)*x 1 + (1299908877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1835539711/10000000000 : ℝ)^4561 ≤ (1404511823313/12500000000000 : ℝ)^3537 := by
    have hnat : (1835539711 : ℕ)^4561*12500000000000^3537 ≤ 1404511823313^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835539711 10000000000 1404511823313 12500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725893661/5000000000 : ℝ)^4561 ≤ (5717077292311/12500000000000 : ℝ)^3537 := by
    have hnat : (2725893661 : ℕ)^4561*12500000000000^3537 ≤ 5717077292311^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725893661 5000000000 5717077292311 12500000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299908877/2500000000 : ℝ)^4561 ≤ (21513643533521/50000000000000 : ℝ)^3537 := by
    have hnat : (1299908877 : ℕ)^4561*50000000000000^3537 ≤ 21513643533521^3537*2500000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299908877 2500000000 21513643533521 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1835539711/10000000000 : ℝ), (2725893661/5000000000 : ℝ), (1299908877/2500000000 : ℝ)] ![(1404511823313/12500000000000 : ℝ), (5717077292311/12500000000000 : ℝ), (21513643533521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1835539711/10000000000 : ℝ)|^4561 ≤ (1404511823313/12500000000000 : ℝ)^3537
        have hw : |(-1835539711/10000000000 : ℝ)|=(1835539711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725893661/5000000000 : ℝ)|^4561 ≤ (5717077292311/12500000000000 : ℝ)^3537
        have hw : |(2725893661/5000000000 : ℝ)|=(2725893661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299908877/2500000000 : ℝ)|^4561 ≤ (21513643533521/50000000000000 : ℝ)^3537
        have hw : |(1299908877/2500000000 : ℝ)|=(1299908877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s2_1 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355984213/10000000000 : ℝ)*x 0 + (-982598183/5000000000 : ℝ)*x 1 + (5199635687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355984213/10000000000 : ℝ)^4561 ≤ (11175715033511/25000000000000 : ℝ)^3537 := by
    have hnat : (5355984213 : ℕ)^4561*25000000000000^3537 ≤ 11175715033511^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355984213 10000000000 11175715033511 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982598183/5000000000 : ℝ)^4561 ≤ (95858209943/781250000000 : ℝ)^3537 := by
    have hnat : (982598183 : ℕ)^4561*781250000000^3537 ≤ 95858209943^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982598183 5000000000 95858209943 781250000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5199635687/10000000000 : ℝ)^4561 ≤ (43027288977111/100000000000000 : ℝ)^3537 := by
    have hnat : (5199635687 : ℕ)^4561*100000000000000^3537 ≤ 43027288977111^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199635687 10000000000 43027288977111 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355984213/10000000000 : ℝ), (-982598183/5000000000 : ℝ), (5199635687/10000000000 : ℝ)] ![(11175715033511/25000000000000 : ℝ), (95858209943/781250000000 : ℝ), (43027288977111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355984213/10000000000 : ℝ)|^4561 ≤ (11175715033511/25000000000000 : ℝ)^3537
        have hw : |(5355984213/10000000000 : ℝ)|=(5355984213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-982598183/5000000000 : ℝ)|^4561 ≤ (95858209943/781250000000 : ℝ)^3537
        have hw : |(-982598183/5000000000 : ℝ)|=(982598183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5199635687/10000000000 : ℝ)|^4561 ≤ (43027288977111/100000000000000 : ℝ)^3537
        have hw : |(5199635687/10000000000 : ℝ)|=(5199635687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s2_2 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677992021/5000000000 : ℝ)*x 0 + (5199635733/10000000000 : ℝ)*x 1 + (-982598267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677992021/5000000000 : ℝ)^4561 ≤ (44702858293623/100000000000000 : ℝ)^3537 := by
    have hnat : (2677992021 : ℕ)^4561*100000000000000^3537 ≤ 44702858293623^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677992021 5000000000 44702858293623 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5199635733/10000000000 : ℝ)^4561 ≤ (43027289467967/100000000000000 : ℝ)^3537 := by
    have hnat : (5199635733 : ℕ)^4561*100000000000000^3537 ≤ 43027289467967^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199635733 10000000000 43027289467967 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982598267/5000000000 : ℝ)^4561 ≤ (12269852225299/100000000000000 : ℝ)^3537 := by
    have hnat : (982598267 : ℕ)^4561*100000000000000^3537 ≤ 12269852225299^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982598267 5000000000 12269852225299 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677992021/5000000000 : ℝ), (5199635733/10000000000 : ℝ), (-982598267/5000000000 : ℝ)] ![(44702858293623/100000000000000 : ℝ), (43027289467967/100000000000000 : ℝ), (12269852225299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677992021/5000000000 : ℝ)|^4561 ≤ (44702858293623/100000000000000 : ℝ)^3537
        have hw : |(2677992021/5000000000 : ℝ)|=(2677992021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5199635733/10000000000 : ℝ)|^4561 ≤ (43027289467967/100000000000000 : ℝ)^3537
        have hw : |(5199635733/10000000000 : ℝ)|=(5199635733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-982598267/5000000000 : ℝ)|^4561 ≤ (12269852225299/100000000000000 : ℝ)^3537
        have hw : |(-982598267/5000000000 : ℝ)|=(982598267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s2_3 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170335413/400000000 : ℝ)*x 0 + (1988349961/5000000000 : ℝ)*x 1 + (4556541051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170335413/400000000 : ℝ)^4561 ≤ (8314714555631/25000000000000 : ℝ)^3537 := by
    have hnat : (170335413 : ℕ)^4561*25000000000000^3537 ≤ 8314714555631^3537*400000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170335413 400000000 8314714555631 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988349961/5000000000 : ℝ)^4561 ≤ (30449510697957/100000000000000 : ℝ)^3537 := by
    have hnat : (1988349961 : ℕ)^4561*100000000000000^3537 ≤ 30449510697957^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988349961 5000000000 30449510697957 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4556541051/10000000000 : ℝ)^4561 ≤ (9072907765721/25000000000000 : ℝ)^3537 := by
    have hnat : (4556541051 : ℕ)^4561*25000000000000^3537 ≤ 9072907765721^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556541051 10000000000 9072907765721 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170335413/400000000 : ℝ), (1988349961/5000000000 : ℝ), (4556541051/10000000000 : ℝ)] ![(8314714555631/25000000000000 : ℝ), (30449510697957/100000000000000 : ℝ), (9072907765721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170335413/400000000 : ℝ)|^4561 ≤ (8314714555631/25000000000000 : ℝ)^3537
        have hw : |(170335413/400000000 : ℝ)|=(170335413/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1988349961/5000000000 : ℝ)|^4561 ≤ (30449510697957/100000000000000 : ℝ)^3537
        have hw : |(1988349961/5000000000 : ℝ)|=(1988349961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4556541051/10000000000 : ℝ)|^4561 ≤ (9072907765721/25000000000000 : ℝ)^3537
        have hw : |(4556541051/10000000000 : ℝ)|=(4556541051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s2_4 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1835585921/10000000000 : ℝ)*x 0 + (208047377/400000000 : ℝ)*x 1 + (2725112823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1835585921/10000000000 : ℝ)^4561 ≤ (2809114838087/25000000000000 : ℝ)^3537 := by
    have hnat : (1835585921 : ℕ)^4561*25000000000000^3537 ≤ 2809114838087^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835585921 10000000000 2809114838087 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208047377/400000000 : ℝ)^4561 ≤ (10760953982201/25000000000000 : ℝ)^3537 := by
    have hnat : (208047377 : ℕ)^4561*25000000000000^3537 ≤ 10760953982201^3537*400000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208047377 400000000 10760953982201 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725112823/5000000000 : ℝ)^4561 ≤ (4571972470437/10000000000000 : ℝ)^3537 := by
    have hnat : (2725112823 : ℕ)^4561*10000000000000^3537 ≤ 4571972470437^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725112823 5000000000 4571972470437 10000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1835585921/10000000000 : ℝ), (208047377/400000000 : ℝ), (2725112823/5000000000 : ℝ)] ![(2809114838087/25000000000000 : ℝ), (10760953982201/25000000000000 : ℝ), (4571972470437/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1835585921/10000000000 : ℝ)|^4561 ≤ (2809114838087/25000000000000 : ℝ)^3537
        have hw : |(-1835585921/10000000000 : ℝ)|=(1835585921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208047377/400000000 : ℝ)|^4561 ≤ (10760953982201/25000000000000 : ℝ)^3537
        have hw : |(208047377/400000000 : ℝ)|=(208047377/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725112823/5000000000 : ℝ)|^4561 ≤ (4571972470437/10000000000000 : ℝ)^3537
        have hw : |(2725112823/5000000000 : ℝ)|=(2725112823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s2_5 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644792321/5000000000 : ℝ)*x 0 + (-1714607257/10000000000 : ℝ)*x 1 + (5450227321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644792321/5000000000 : ℝ)^4561 ≤ (21994754027961/50000000000000 : ℝ)^3537 := by
    have hnat : (2644792321 : ℕ)^4561*50000000000000^3537 ≤ 21994754027961^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644792321 5000000000 21994754027961 50000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1714607257/10000000000 : ℝ)^4561 ≤ (10290749101727/100000000000000 : ℝ)^3537 := by
    have hnat : (1714607257 : ℕ)^4561*100000000000000^3537 ≤ 10290749101727^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714607257 10000000000 10290749101727 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450227321/10000000000 : ℝ)^4561 ≤ (45719742823151/100000000000000 : ℝ)^3537 := by
    have hnat : (5450227321 : ℕ)^4561*100000000000000^3537 ≤ 45719742823151^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450227321 10000000000 45719742823151 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644792321/5000000000 : ℝ), (-1714607257/10000000000 : ℝ), (5450227321/10000000000 : ℝ)] ![(21994754027961/50000000000000 : ℝ), (10290749101727/100000000000000 : ℝ), (45719742823151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644792321/5000000000 : ℝ)|^4561 ≤ (21994754027961/50000000000000 : ℝ)^3537
        have hw : |(2644792321/5000000000 : ℝ)|=(2644792321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1714607257/10000000000 : ℝ)|^4561 ≤ (10290749101727/100000000000000 : ℝ)^3537
        have hw : |(-1714607257/10000000000 : ℝ)|=(1714607257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450227321/10000000000 : ℝ)|^4561 ≤ (45719742823151/100000000000000 : ℝ)^3537
        have hw : |(5450227321/10000000000 : ℝ)|=(5450227321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s2_6 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644792707/5000000000 : ℝ)*x 0 + (2725113827/5000000000 : ℝ)*x 1 + (-857302861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644792707/5000000000 : ℝ)^4561 ≤ (43989516334769/100000000000000 : ℝ)^3537 := by
    have hnat : (2644792707 : ℕ)^4561*100000000000000^3537 ≤ 43989516334769^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644792707 5000000000 43989516334769 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725113827/5000000000 : ℝ)^4561 ≤ (45719746425273/100000000000000 : ℝ)^3537 := by
    have hnat : (2725113827 : ℕ)^4561*100000000000000^3537 ≤ 45719746425273^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725113827 5000000000 45719746425273 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857302861/5000000000 : ℝ)^4561 ≤ (2572684305437/25000000000000 : ℝ)^3537 := by
    have hnat : (857302861 : ℕ)^4561*25000000000000^3537 ≤ 2572684305437^3537*5000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857302861 5000000000 2572684305437 25000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644792707/5000000000 : ℝ), (2725113827/5000000000 : ℝ), (-857302861/5000000000 : ℝ)] ![(43989516334769/100000000000000 : ℝ), (45719746425273/100000000000000 : ℝ), (2572684305437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644792707/5000000000 : ℝ)|^4561 ≤ (43989516334769/100000000000000 : ℝ)^3537
        have hw : |(2644792707/5000000000 : ℝ)|=(2644792707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725113827/5000000000 : ℝ)|^4561 ≤ (45719746425273/100000000000000 : ℝ)^3537
        have hw : |(2725113827/5000000000 : ℝ)|=(2725113827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-857302861/5000000000 : ℝ)|^4561 ≤ (2572684305437/25000000000000 : ℝ)^3537
        have hw : |(-857302861/5000000000 : ℝ)|=(857302861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1532_s2_7 (p : ℝ) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4258494481/10000000000 : ℝ)*x 0 + (569122867/1250000000 : ℝ)*x 1 + (3980288819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4258494481/10000000000 : ℝ)^4561 ≤ (33259957574131/100000000000000 : ℝ)^3537 := by
    have hnat : (4258494481 : ℕ)^4561*100000000000000^3537 ≤ 33259957574131^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258494481 10000000000 33259957574131 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569122867/1250000000 : ℝ)^4561 ≤ (36255091185147/100000000000000 : ℝ)^3537 := by
    have hnat : (569122867 : ℕ)^4561*100000000000000^3537 ≤ 36255091185147^3537*1250000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569122867 1250000000 36255091185147 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3980288819/10000000000 : ℝ)^4561 ≤ (30484951229289/100000000000000 : ℝ)^3537 := by
    have hnat : (3980288819 : ℕ)^4561*100000000000000^3537 ≤ 30484951229289^3537*10000000000^4561 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3980288819 10000000000 30484951229289 100000000000000 4561 3537 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4561/1024 : ℝ)) 4561 3537 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4258494481/10000000000 : ℝ), (569122867/1250000000 : ℝ), (3980288819/10000000000 : ℝ)] ![(33259957574131/100000000000000 : ℝ), (36255091185147/100000000000000 : ℝ), (30484951229289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4258494481/10000000000 : ℝ)|^4561 ≤ (33259957574131/100000000000000 : ℝ)^3537
        have hw : |(4258494481/10000000000 : ℝ)|=(4258494481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569122867/1250000000 : ℝ)|^4561 ≤ (36255091185147/100000000000000 : ℝ)^3537
        have hw : |(569122867/1250000000 : ℝ)|=(569122867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3980288819/10000000000 : ℝ)|^4561 ≤ (30484951229289/100000000000000 : ℝ)^3537
        have hw : |(3980288819/10000000000 : ℝ)|=(3980288819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1532_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1077/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2117/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (637/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1077/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1077/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1077/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1077/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1077/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1077/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (1077/12500 : ℝ) ^ (4559/1024 : ℝ) ≤ (909479463543993/50000000000000000000 : ℝ) := by
    have hpowers : (1077/12500 : ℝ)^4559 ≤ (909479463543993/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1077 : ℕ)^4559*50000000000000000000^1024 ≤ 909479463543993^1024*12500^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1077 12500 909479463543993 50000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1077/12500 : ℝ)) (X := (909479463543993/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9061/50000 : ℝ) ^ (4559/1024 : ℝ) ≤ (12455568999205659/25000000000000000000 : ℝ) := by
    have hpowers : (9061/50000 : ℝ)^4559 ≤ (12455568999205659/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9061 : ℕ)^4559*25000000000000000000^1024 ≤ 12455568999205659^1024*50000^4559 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9061 50000 12455568999205659 25000000000000000000 4559 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9061/50000 : ℝ)) (X := (12455568999205659/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000909479463543993/25000000000000000000 : ℝ) ≤ (400003268414427/400000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (25000909479463543993/25000000000000000000 : ℝ)^1024 ≤ (400003268414427/400000000000000 : ℝ)^4559 := by
      have hnat : (25000909479463543993 : ℕ)^1024*400000000000000^4559 ≤ 400003268414427^4559*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000909479463543993 25000000000000000000 400003268414427 400000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400003268414427/400000000000000 : ℝ)) (X := (25000909479463543993/25000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025820617461955311/50000000000000000000 : ℝ) ≤ (10001159685030709/10000000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (50025820617461955311/50000000000000000000 : ℝ)^1024 ≤ (10001159685030709/10000000000000000 : ℝ)^4559 := by
      have hnat : (50025820617461955311 : ℕ)^1024*10000000000000000^4559 ≤ 10001159685030709^4559*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025820617461955311 50000000000000000000 10001159685030709 10000000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001159685030709/10000000000000000 : ℝ)) (X := (50025820617461955311/50000000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12512455568999205659/12500000000000000000 : ℝ) ≤ (10002237659700743/10000000000000000 : ℝ) ^ (4559/1024 : ℝ) := by
    have hpowers : (12512455568999205659/12500000000000000000 : ℝ)^1024 ≤ (10002237659700743/10000000000000000 : ℝ)^4559 := by
      have hnat : (12512455568999205659 : ℕ)^1024*10000000000000000^4559 ≤ 10002237659700743^4559*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12512455568999205659 12500000000000000000 10002237659700743 10000000000000000 1024 4559 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002237659700743/10000000000000000 : ℝ)) (X := (12512455568999205659/12500000000000000000 : ℝ)) (by norm_num) 4559 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(909479463543993/50000000000000000000 : ℝ) ≤ ((47521100539587275331/47530000000000000000 : ℝ)+2*(538987335017/475300000000000 : ℝ)*(1077/12500 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (47521100539587275331/47530000000000000000 : ℝ)+2*(538987335017/475300000000000 : ℝ)*(1077/12500 : ℝ)=(400003268414427/400000000000000 : ℝ) by norm_num, show 1+2*(909479463543993/50000000000000000000 : ℝ)=(25000909479463543993/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12455568999205659/25000000000000000000 : ℝ)+(909479463543993/50000000000000000000 : ℝ) ≤ ((47521100539587275331/47530000000000000000 : ℝ)+(538987335017/475300000000000 : ℝ)*((9061/50000 : ℝ)+(1077/12500 : ℝ)))^(4559/1024 : ℝ) := by
    rw [show (47521100539587275331/47530000000000000000 : ℝ)+(538987335017/475300000000000 : ℝ)*((9061/50000 : ℝ)+(1077/12500 : ℝ))=(10001159685030709/10000000000000000 : ℝ) by norm_num, show 1+(12455568999205659/25000000000000000000 : ℝ)+(909479463543993/50000000000000000000 : ℝ)=(50025820617461955311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12455568999205659/25000000000000000000 : ℝ) ≤ ((47521100539587275331/47530000000000000000 : ℝ)+2*(538987335017/475300000000000 : ℝ)*(9061/50000 : ℝ))^(4559/1024 : ℝ) := by
    rw [show (47521100539587275331/47530000000000000000 : ℝ)+2*(538987335017/475300000000000 : ℝ)*(9061/50000 : ℝ)=(10002237659700743/10000000000000000 : ℝ) by norm_num, show 1+2*(12455568999205659/25000000000000000000 : ℝ)=(12512455568999205659/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47521100539587275331/47530000000000000000 : ℝ)*(X 1 0+X 2 0)+(538987335017/475300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (1077/12500 : ℝ)) (hi := (9061/50000 : ℝ)) (c := (47521100539587275331/47530000000000000000 : ℝ)) (alpha := (538987335017/475300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47521100539587275331/47530000000000000000 : ℝ)*(X 0 1+X 2 1)+(538987335017/475300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (1077/12500 : ℝ)) (hi := (9061/50000 : ℝ)) (c := (47521100539587275331/47530000000000000000 : ℝ)) (alpha := (538987335017/475300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47521100539587275331/47530000000000000000 : ℝ)*(X 0 2+X 1 2)+(538987335017/475300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4559/1024 : ℝ)) (lo := (1077/12500 : ℝ)) (hi := (9061/50000 : ℝ)) (c := (47521100539587275331/47530000000000000000 : ℝ)) (alpha := (538987335017/475300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1835539711/10000000000 : ℝ)*X 0 0+(2725893661/5000000000 : ℝ)*X 0 1+(1299908877/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355984213/10000000000 : ℝ)*X 1 0+(-982598183/5000000000 : ℝ)*X 1 1+(5199635687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677992021/5000000000 : ℝ)*X 2 0+(5199635733/10000000000 : ℝ)*X 2 1+(-982598267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((170335413/400000000 : ℝ)*X 0 0+(1988349961/5000000000 : ℝ)*X 0 1+(4556541051/10000000000 : ℝ)*X 0 2+(170335413/400000000 : ℝ)*X 1 0+(1988349961/5000000000 : ℝ)*X 1 1+(4556541051/10000000000 : ℝ)*X 1 2+(170335413/400000000 : ℝ)*X 2 0+(1988349961/5000000000 : ℝ)*X 2 1+(4556541051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1835585921/10000000000 : ℝ)*X 0 0+(208047377/400000000 : ℝ)*X 0 1+(2725112823/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644792321/5000000000 : ℝ)*X 1 0+(-1714607257/10000000000 : ℝ)*X 1 1+(5450227321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644792707/5000000000 : ℝ)*X 2 0+(2725113827/5000000000 : ℝ)*X 2 1+(-857302861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4258494481/10000000000 : ℝ)*X 0 0+(569122867/1250000000 : ℝ)*X 0 1+(3980288819/10000000000 : ℝ)*X 0 2+(4258494481/10000000000 : ℝ)*X 1 0+(569122867/1250000000 : ℝ)*X 1 1+(3980288819/10000000000 : ℝ)*X 1 2+(4258494481/10000000000 : ℝ)*X 2 0+(569122867/1250000000 : ℝ)*X 2 1+(3980288819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1532_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78084544657621144552005093/14853125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1024760437/100000000000000 : ℝ)*(base19) + (873083687/100000000000000 : ℝ)*(base23) + (4910561/20000000000000 : ℝ)*(lower2) + (183010633/100000000000000 : ℝ)*(upper3) + (11131853/100000000000000 : ℝ)*(lower4) + (8891438155769/312500000000 : ℝ)*(major0) + (8891438155769/312500000000 : ℝ)*(major1) + (8891438155769/312500000000 : ℝ)*(major2) + (991471213414753/25000000000000 : ℝ)*(sp0) + (991474747291203/25000000000000 : ℝ)*(sp1) + (3965899140841561/100000000000000 : ℝ)*(sp2) + (862307248833127/50000000000000 : ℝ)*(sp3) + (3790066559/25000000000000 : ℝ)*(sp4) + (5732863579/100000000000000 : ℝ)*(sp7) + (1724620230529833/100000000000000 : ℝ)*(f.failure) + (30983593858791/781250000000 : ℝ)*(f.sum) + (4750062001561/4753000000000000000000000000 : ℝ)*base66 + (2575499286812923/2121875000000000000000000000000 : ℝ)*base68 + (586776444413387/530468750000000000000000000000 : ℝ)*base70 + (5748464236236149/1060937500000000000000000000000 : ℝ)*base72 + (3015555532713/1188250000000000000000000000 : ℝ)*base73 + (116139922667689/66308593750000000000000000000 : ℝ)*base76 + (2895056520832137/530468750000000000000000000000 : ℝ)*base78 + (1048563053045101/1060937500000000000000000000000 : ℝ)*base79 + (3864154377179/4753000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (26111657/5000000000000000000000 : ℝ)*base90 + (26111657/5000000000000000000000 : ℝ)*base92 + (26111657/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16653931605119218376039206209/2376500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14896957/20000000000000 : ℝ)*(base8) + (546947389/50000000000000 : ℝ)*(base15) + (107537411/50000000000000 : ℝ)*(base29) + (8765261/4000000000000 : ℝ)*(lower2) + (271500039/100000000000000 : ℝ)*(lower4) + (2880768176158291/100000000000000 : ℝ)*(major0) + (2880768391233113/100000000000000 : ℝ)*(major1) + (2880768391233113/100000000000000 : ℝ)*(major2) + (23029542711/100000000000000 : ℝ)*(sp2) + (1595721227/25000000000000 : ℝ)*(sp3) + (2007696693544957/50000000000000 : ℝ)*(sp4) + (2007696076302549/50000000000000 : ℝ)*(sp5) + (2007685108478583/50000000000000 : ℝ)*(sp6) + (6984546817659/400000000000 : ℝ)*(sp7) + (873071543649829/50000000000000 : ℝ)*(f.failure) + (2007696730787349/50000000000000 : ℝ)*(f.sum) + (126208109702081/23765000000000000000000000000 : ℝ)*base65 + (4552620548378666371/679000000000000000000000000000000 : ℝ)*base68 + (8328200303682666371/679000000000000000000000000000000 : ℝ)*base70 + (12623860194649519321/4753000000000000000000000000000000 : ℝ)*base71 + (604732760013/742656250000000000000000000 : ℝ)*base74 + (1732582999481935403/4753000000000000000000000000000000 : ℝ)*base75 + (28908280006860480679/4753000000000000000000000000000000 : ℝ)*base78 + (28911542682429064597/4753000000000000000000000000000000 : ℝ)*base80 + (49141652210727/11882500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (21549541/2500000000000000000000 : ℝ)*base90 + (21549541/2500000000000000000000 : ℝ)*base92 + (21549541/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1532_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1077/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2117/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (637/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1532_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1532_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2117/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (637/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1532_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1532_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1532_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2117/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (637/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1532_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
