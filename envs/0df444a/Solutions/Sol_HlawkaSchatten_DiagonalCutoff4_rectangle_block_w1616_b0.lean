-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1616_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:52:32.025132+00:00
-- url     : https://prove2.me/submissions/7d2dc10a-2f0d-4542-b522-731d7e45c497

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
theorem support_rectangle_w1616_s0_0 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-62169591/400000000 : ℝ)*x 0 + (1165810207/2000000000 : ℝ)*x 1 + (4897472647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62169591/400000000 : ℝ)^4783 ≤ (9360027343627/100000000000000 : ℝ)^3759 := by
    have hnat : (62169591 : ℕ)^4783*100000000000000^3759 ≤ 9360027343627^3759*400000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62169591 400000000 9360027343627 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165810207/2000000000 : ℝ)^4783 ≤ (5032035496897/10000000000000 : ℝ)^3759 := by
    have hnat : (1165810207 : ℕ)^4783*10000000000000^3759 ≤ 5032035496897^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165810207 2000000000 5032035496897 10000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4897472647/10000000000 : ℝ)^4783 ≤ (40319617666991/100000000000000 : ℝ)^3759 := by
    have hnat : (4897472647 : ℕ)^4783*100000000000000^3759 ≤ 40319617666991^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4897472647 10000000000 40319617666991 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62169591/400000000 : ℝ), (1165810207/2000000000 : ℝ), (4897472647/10000000000 : ℝ)] ![(9360027343627/100000000000000 : ℝ), (5032035496897/10000000000000 : ℝ), (40319617666991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62169591/400000000 : ℝ)|^4783 ≤ (9360027343627/100000000000000 : ℝ)^3759
        have hw : |(-62169591/400000000 : ℝ)|=(62169591/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1165810207/2000000000 : ℝ)|^4783 ≤ (5032035496897/10000000000000 : ℝ)^3759
        have hw : |(1165810207/2000000000 : ℝ)|=(1165810207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4897472647/10000000000 : ℝ)|^4783 ≤ (40319617666991/100000000000000 : ℝ)^3759
        have hw : |(4897472647/10000000000 : ℝ)|=(4897472647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s0_1 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5451251071/10000000000 : ℝ)*x 0 + (-1034667099/5000000000 : ℝ)*x 1 + (4897472573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5451251071/10000000000 : ℝ)^4783 ≤ (721995314247/1562500000000 : ℝ)^3759 := by
    have hnat : (5451251071 : ℕ)^4783*1562500000000^3759 ≤ 721995314247^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451251071 10000000000 721995314247 1562500000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034667099/5000000000 : ℝ)^4783 ≤ (13472682982063/100000000000000 : ℝ)^3759 := by
    have hnat : (1034667099 : ℕ)^4783*100000000000000^3759 ≤ 13472682982063^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034667099 5000000000 13472682982063 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4897472573/10000000000 : ℝ)^4783 ≤ (1259988027869/3125000000000 : ℝ)^3759 := by
    have hnat : (4897472573 : ℕ)^4783*3125000000000^3759 ≤ 1259988027869^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4897472573 10000000000 1259988027869 3125000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5451251071/10000000000 : ℝ), (-1034667099/5000000000 : ℝ), (4897472573/10000000000 : ℝ)] ![(721995314247/1562500000000 : ℝ), (13472682982063/100000000000000 : ℝ), (1259988027869/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5451251071/10000000000 : ℝ)|^4783 ≤ (721995314247/1562500000000 : ℝ)^3759
        have hw : |(5451251071/10000000000 : ℝ)|=(5451251071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034667099/5000000000 : ℝ)|^4783 ≤ (13472682982063/100000000000000 : ℝ)^3759
        have hw : |(-1034667099/5000000000 : ℝ)|=(1034667099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4897472573/10000000000 : ℝ)|^4783 ≤ (1259988027869/3125000000000 : ℝ)^3759
        have hw : |(4897472573/10000000000 : ℝ)|=(4897472573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s0_2 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5451250911/10000000000 : ℝ)*x 0 + (4897472633/10000000000 : ℝ)*x 1 + (-2069334331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5451250911/10000000000 : ℝ)^4783 ≤ (9241539677221/20000000000000 : ℝ)^3759 := by
    have hnat : (5451250911 : ℕ)^4783*20000000000000^3759 ≤ 9241539677221^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451250911 10000000000 9241539677221 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4897472633/10000000000 : ℝ)^4783 ≤ (8063923504067/20000000000000 : ℝ)^3759 := by
    have hnat : (4897472633 : ℕ)^4783*20000000000000^3759 ≤ 8063923504067^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4897472633 10000000000 8063923504067 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069334331/10000000000 : ℝ)^4783 ≤ (1684085510483/12500000000000 : ℝ)^3759 := by
    have hnat : (2069334331 : ℕ)^4783*12500000000000^3759 ≤ 1684085510483^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069334331 10000000000 1684085510483 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5451250911/10000000000 : ℝ), (4897472633/10000000000 : ℝ), (-2069334331/10000000000 : ℝ)] ![(9241539677221/20000000000000 : ℝ), (8063923504067/20000000000000 : ℝ), (1684085510483/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5451250911/10000000000 : ℝ)|^4783 ≤ (9241539677221/20000000000000 : ℝ)^3759
        have hw : |(5451250911/10000000000 : ℝ)|=(5451250911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4897472633/10000000000 : ℝ)|^4783 ≤ (8063923504067/20000000000000 : ℝ)^3759
        have hw : |(4897472633/10000000000 : ℝ)|=(4897472633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069334331/10000000000 : ℝ)|^4783 ≤ (1684085510483/12500000000000 : ℝ)^3759
        have hw : |(-2069334331/10000000000 : ℝ)|=(2069334331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s0_3 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4106846377/10000000000 : ℝ)*x 0 + (768828141/2500000000 : ℝ)*x 1 + (1345654143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4106846377/10000000000 : ℝ)^4783 ≤ (6445449066607/20000000000000 : ℝ)^3759 := by
    have hnat : (4106846377 : ℕ)^4783*20000000000000^3759 ≤ 6445449066607^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4106846377 10000000000 6445449066607 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (768828141/2500000000 : ℝ)^4783 ≤ (1115202432781/5000000000000 : ℝ)^3759 := by
    have hnat : (768828141 : ℕ)^4783*5000000000000^3759 ≤ 1115202432781^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768828141 2500000000 1115202432781 5000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1345654143/2500000000 : ℝ)^4783 ≤ (22734352997759/50000000000000 : ℝ)^3759 := by
    have hnat : (1345654143 : ℕ)^4783*50000000000000^3759 ≤ 22734352997759^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345654143 2500000000 22734352997759 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4106846377/10000000000 : ℝ), (768828141/2500000000 : ℝ), (1345654143/2500000000 : ℝ)] ![(6445449066607/20000000000000 : ℝ), (1115202432781/5000000000000 : ℝ), (22734352997759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4106846377/10000000000 : ℝ)|^4783 ≤ (6445449066607/20000000000000 : ℝ)^3759
        have hw : |(4106846377/10000000000 : ℝ)|=(4106846377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(768828141/2500000000 : ℝ)|^4783 ≤ (1115202432781/5000000000000 : ℝ)^3759
        have hw : |(768828141/2500000000 : ℝ)|=(768828141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1345654143/2500000000 : ℝ)|^4783 ≤ (22734352997759/50000000000000 : ℝ)^3759
        have hw : |(1345654143/2500000000 : ℝ)|=(1345654143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s0_4 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1556953171/10000000000 : ℝ)*x 0 + (984197021/2000000000 : ℝ)*x 1 + (2902353017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1556953171/10000000000 : ℝ)^4783 ≤ (9380824480443/100000000000000 : ℝ)^3759 := by
    have hnat : (1556953171 : ℕ)^4783*100000000000000^3759 ≤ 9380824480443^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1556953171 10000000000 9380824480443 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984197021/2000000000 : ℝ)^4783 ≤ (20283040990159/50000000000000 : ℝ)^3759 := by
    have hnat : (984197021 : ℕ)^4783*50000000000000^3759 ≤ 20283040990159^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984197021 2000000000 20283040990159 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2902353017/5000000000 : ℝ)^4783 ≤ (25026546761443/50000000000000 : ℝ)^3759 := by
    have hnat : (2902353017 : ℕ)^4783*50000000000000^3759 ≤ 25026546761443^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2902353017 5000000000 25026546761443 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1556953171/10000000000 : ℝ), (984197021/2000000000 : ℝ), (2902353017/5000000000 : ℝ)] ![(9380824480443/100000000000000 : ℝ), (20283040990159/50000000000000 : ℝ), (25026546761443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1556953171/10000000000 : ℝ)|^4783 ≤ (9380824480443/100000000000000 : ℝ)^3759
        have hw : |(-1556953171/10000000000 : ℝ)|=(1556953171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(984197021/2000000000 : ℝ)|^4783 ≤ (20283040990159/50000000000000 : ℝ)^3759
        have hw : |(984197021/2000000000 : ℝ)|=(984197021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2902353017/5000000000 : ℝ)|^4783 ≤ (25026546761443/50000000000000 : ℝ)^3759
        have hw : |(2902353017/5000000000 : ℝ)|=(2902353017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s0_5 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196841707/10000000000 : ℝ)*x 0 + (-23242017/200000000 : ℝ)*x 1 + (580470611/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196841707/10000000000 : ℝ)^4783 ≤ (43481374606913/100000000000000 : ℝ)^3759 := by
    have hnat : (5196841707 : ℕ)^4783*100000000000000^3759 ≤ 43481374606913^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196841707 10000000000 43481374606913 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23242017/200000000 : ℝ)^4783 ≤ (404095688481/6250000000000 : ℝ)^3759 := by
    have hnat : (23242017 : ℕ)^4783*6250000000000^3759 ≤ 404095688481^3759*200000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23242017 200000000 404095688481 6250000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (580470611/1000000000 : ℝ)^4783 ≤ (6256636794593/12500000000000 : ℝ)^3759 := by
    have hnat : (580470611 : ℕ)^4783*12500000000000^3759 ≤ 6256636794593^3759*1000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580470611 1000000000 6256636794593 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196841707/10000000000 : ℝ), (-23242017/200000000 : ℝ), (580470611/1000000000 : ℝ)] ![(43481374606913/100000000000000 : ℝ), (404095688481/6250000000000 : ℝ), (6256636794593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196841707/10000000000 : ℝ)|^4783 ≤ (43481374606913/100000000000000 : ℝ)^3759
        have hw : |(5196841707/10000000000 : ℝ)|=(5196841707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23242017/200000000 : ℝ)|^4783 ≤ (404095688481/6250000000000 : ℝ)^3759
        have hw : |(-23242017/200000000 : ℝ)|=(23242017/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(580470611/1000000000 : ℝ)|^4783 ≤ (6256636794593/12500000000000 : ℝ)^3759
        have hw : |(580470611/1000000000 : ℝ)|=(580470611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s0_6 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196841743/10000000000 : ℝ)*x 0 + (2902353273/5000000000 : ℝ)*x 1 + (-1162100121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196841743/10000000000 : ℝ)^4783 ≤ (21740687495087/50000000000000 : ℝ)^3759 := by
    have hnat : (5196841743 : ℕ)^4783*50000000000000^3759 ≤ 21740687495087^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196841743 10000000000 21740687495087 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2902353273/5000000000 : ℝ)^4783 ≤ (50053099140459/100000000000000 : ℝ)^3759 := by
    have hnat : (2902353273 : ℕ)^4783*100000000000000^3759 ≤ 50053099140459^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2902353273 5000000000 50053099140459 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1162100121/10000000000 : ℝ)^4783 ≤ (6465525854909/100000000000000 : ℝ)^3759 := by
    have hnat : (1162100121 : ℕ)^4783*100000000000000^3759 ≤ 6465525854909^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162100121 10000000000 6465525854909 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196841743/10000000000 : ℝ), (2902353273/5000000000 : ℝ), (-1162100121/10000000000 : ℝ)] ![(21740687495087/50000000000000 : ℝ), (50053099140459/100000000000000 : ℝ), (6465525854909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196841743/10000000000 : ℝ)|^4783 ≤ (21740687495087/50000000000000 : ℝ)^3759
        have hw : |(5196841743/10000000000 : ℝ)|=(5196841743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2902353273/5000000000 : ℝ)|^4783 ≤ (50053099140459/100000000000000 : ℝ)^3759
        have hw : |(2902353273/5000000000 : ℝ)|=(2902353273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1162100121/10000000000 : ℝ)|^4783 ≤ (6465525854909/100000000000000 : ℝ)^3759
        have hw : |(-1162100121/10000000000 : ℝ)|=(1162100121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s0_7 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164542623/400000000 : ℝ)*x 0 + (106487607/200000000 : ℝ)*x 1 + (783902447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164542623/400000000 : ℝ)^4783 ≤ (16147175326671/50000000000000 : ℝ)^3759 := by
    have hnat : (164542623 : ℕ)^4783*50000000000000^3759 ≤ 16147175326671^3759*400000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164542623 400000000 16147175326671 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106487607/200000000 : ℝ)^4783 ≤ (44843679778689/100000000000000 : ℝ)^3759 := by
    have hnat : (106487607 : ℕ)^4783*100000000000000^3759 ≤ 44843679778689^3759*200000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106487607 200000000 44843679778689 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (783902447/2500000000 : ℝ)^4783 ≤ (22861969558381/100000000000000 : ℝ)^3759 := by
    have hnat : (783902447 : ℕ)^4783*100000000000000^3759 ≤ 22861969558381^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783902447 2500000000 22861969558381 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164542623/400000000 : ℝ), (106487607/200000000 : ℝ), (783902447/2500000000 : ℝ)] ![(16147175326671/50000000000000 : ℝ), (44843679778689/100000000000000 : ℝ), (22861969558381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164542623/400000000 : ℝ)|^4783 ≤ (16147175326671/50000000000000 : ℝ)^3759
        have hw : |(164542623/400000000 : ℝ)|=(164542623/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(106487607/200000000 : ℝ)|^4783 ≤ (44843679778689/100000000000000 : ℝ)^3759
        have hw : |(106487607/200000000 : ℝ)|=(106487607/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(783902447/2500000000 : ℝ)|^4783 ≤ (22861969558381/100000000000000 : ℝ)^3759
        have hw : |(783902447/2500000000 : ℝ)|=(783902447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1616_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (519/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4821/20000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4779/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4779 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4779*1^1024 ≤ 0^1024*1^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4779/1024 : ℝ) ≤ (694683674447352351/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4779 ≤ (694683674447352351/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4779*50000000000000000000^1024 ≤ 694683674447352351^1024*5^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 694683674447352351 50000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (694683674447352351/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4779 := by
      have hnat : (1 : ℕ)^1024*1^4779 ≤ 1^4779*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50694683674447352351/50000000000000000000 : ℝ) ≤ (2005921783371707/2000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (50694683674447352351/50000000000000000000 : ℝ)^1024 ≤ (2005921783371707/2000000000000000 : ℝ)^4779 := by
      have hnat : (50694683674447352351 : ℕ)^1024*2000000000000000^4779 ≤ 2005921783371707^4779*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50694683674447352351 50000000000000000000 2005921783371707 2000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005921783371707/2000000000000000 : ℝ)) (X := (50694683674447352351/50000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25694683674447352351/25000000000000000000 : ℝ) ≤ (1005921783371707/1000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (25694683674447352351/25000000000000000000 : ℝ)^1024 ≤ (1005921783371707/1000000000000000 : ℝ)^4779 := by
      have hnat : (25694683674447352351 : ℕ)^1024*1000000000000000^4779 ≤ 1005921783371707^4779*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25694683674447352351 25000000000000000000 1005921783371707 1000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005921783371707/1000000000000000 : ℝ)) (X := (25694683674447352351/25000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5921783371707/800000000000000 : ℝ)*(0 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5921783371707/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(694683674447352351/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5921783371707/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4779/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5921783371707/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2005921783371707/2000000000000000 : ℝ) by norm_num, show 1+(694683674447352351/50000000000000000000 : ℝ)+(0 : ℝ)=(50694683674447352351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(694683674447352351/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5921783371707/800000000000000 : ℝ)*(2/5 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5921783371707/800000000000000 : ℝ)*(2/5 : ℝ)=(1005921783371707/1000000000000000 : ℝ) by norm_num, show 1+2*(694683674447352351/50000000000000000000 : ℝ)=(25694683674447352351/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5921783371707/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5921783371707/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5921783371707/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5921783371707/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5921783371707/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5921783371707/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-62169591/400000000 : ℝ)*X 0 0+(1165810207/2000000000 : ℝ)*X 0 1+(4897472647/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5451251071/10000000000 : ℝ)*X 1 0+(-1034667099/5000000000 : ℝ)*X 1 1+(4897472573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5451250911/10000000000 : ℝ)*X 2 0+(4897472633/10000000000 : ℝ)*X 2 1+(-2069334331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4106846377/10000000000 : ℝ)*X 0 0+(768828141/2500000000 : ℝ)*X 0 1+(1345654143/2500000000 : ℝ)*X 0 2+(4106846377/10000000000 : ℝ)*X 1 0+(768828141/2500000000 : ℝ)*X 1 1+(1345654143/2500000000 : ℝ)*X 1 2+(4106846377/10000000000 : ℝ)*X 2 0+(768828141/2500000000 : ℝ)*X 2 1+(1345654143/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1556953171/10000000000 : ℝ)*X 0 0+(984197021/2000000000 : ℝ)*X 0 1+(2902353017/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5196841707/10000000000 : ℝ)*X 1 0+(-23242017/200000000 : ℝ)*X 1 1+(580470611/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5196841743/10000000000 : ℝ)*X 2 0+(2902353273/5000000000 : ℝ)*X 2 1+(-1162100121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((164542623/400000000 : ℝ)*X 0 0+(106487607/200000000 : ℝ)*X 0 1+(783902447/2500000000 : ℝ)*X 0 2+(164542623/400000000 : ℝ)*X 1 0+(106487607/200000000 : ℝ)*X 1 1+(783902447/2500000000 : ℝ)*X 1 2+(164542623/400000000 : ℝ)*X 2 0+(106487607/200000000 : ℝ)*X 2 1+(783902447/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17301870241829696307627/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (425432609/50000000000000 : ℝ)*(base19) + (397746821/50000000000000 : ℝ)*(base23) + (76732787/50000000000000 : ℝ)*(upper3) + (2601839/20000000000000 : ℝ)*(upper4) + (82891817/100000000000000 : ℝ)*(upper5) + (75343137317271/10000000000000 : ℝ)*(major0) + (75343137317271/10000000000000 : ℝ)*(major1) + (75343137317271/10000000000000 : ℝ)*(major2) + (13418129344723/1250000000000 : ℝ)*(sp0) + (214690500614891/20000000000000 : ℝ)*(sp1) + (67090784902877/6250000000000 : ℝ)*(sp2) + (6771993981519/1562500000000 : ℝ)*(sp3) + (3006361833/100000000000000 : ℝ)*(sp4) + (1633406271/100000000000000 : ℝ)*(sp7) + (433409248223487/100000000000000 : ℝ)*(f.failure) + (536726676969837/50000000000000 : ℝ)*(f.sum) + (18468028595597/4000000000000000000000000000 : ℝ)*base65 + (34668675539597/8000000000000000000000000000 : ℝ)*base67 + (21254431364403/8000000000000000000000000000 : ℝ)*base70 + (12292675355597/8000000000000000000000000000 : ℝ)*base71 + (12813925515597/4000000000000000000000000000 : ℝ)*base73 + (18476129331597/8000000000000000000000000000 : ℝ)*base75 + (60290075420403/8000000000000000000000000000 : ℝ)*base78 + (15722367588403/8000000000000000000000000000 : ℝ)*base80 + (1787545819597/4000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (10621053/2500000000000000000000 : ℝ)*base90 + (10621053/2500000000000000000000 : ℝ)*base92 + (10621053/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79804013514004515038007/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (761391427/50000000000000 : ℝ)*(base19) + (1858709261/100000000000000 : ℝ)*(base23) + (327030399/100000000000000 : ℝ)*(base39) + (23017807/12500000000000 : ℝ)*(upper3) + (372456913/100000000000000 : ℝ)*(upper5) + (397113617646083/50000000000000 : ℝ)*(major0) + (397113617646083/50000000000000 : ℝ)*(major1) + (99278363532721/12500000000000 : ℝ)*(major2) + (5106840413/100000000000000 : ℝ)*(sp1) + (522359317/10000000000000 : ℝ)*(sp2) + (141447115750591/12500000000000 : ℝ)*(sp4) + (1131570296381461/100000000000000 : ℝ)*(sp5) + (141446271341587/12500000000000 : ℝ)*(sp6) + (456876951535823/100000000000000 : ℝ)*(sp7) + (456876951535823/100000000000000 : ℝ)*(f.failure) + (1131577253035127/100000000000000 : ℝ)*(f.sum) + (64918867407331/40000000000000000000000000000 : ℝ)*base66 + (29663344775253/10000000000000000000000000000 : ℝ)*base68 + (91177790533681/40000000000000000000000000000 : ℝ)*base69 + (83872994625253/10000000000000000000000000000 : ℝ)*base72 + (22882534967331/40000000000000000000000000000 : ℝ)*base74 + (140026166253681/40000000000000000000000000000 : ℝ)*base75 + (334027647346319/40000000000000000000000000000 : ℝ)*base78 + (149816545466319/40000000000000000000000000000 : ℝ)*base80 + (88060839186319/20000000000000000000000000000 : ℝ)*base82 + (24070163/2500000000000000000000 : ℝ)*base89 + (24070163/2500000000000000000000 : ℝ)*base91 + (929837/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1616_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (519/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4821/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1616_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1616_s1_0 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1674888331/10000000000 : ℝ)*x 0 + (5524367421/10000000000 : ℝ)*x 1 + (2562035347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674888331/10000000000 : ℝ)^4783 ≤ (257353228669/2500000000000 : ℝ)^3759 := by
    have hnat : (1674888331 : ℕ)^4783*2500000000000^3759 ≤ 257353228669^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674888331 10000000000 257353228669 2500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5524367421/10000000000 : ℝ)^4783 ≤ (23498871670693/50000000000000 : ℝ)^3759 := by
    have hnat : (5524367421 : ℕ)^4783*50000000000000^3759 ≤ 23498871670693^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524367421 10000000000 23498871670693 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2562035347/5000000000 : ℝ)^4783 ≤ (42708127505817/100000000000000 : ℝ)^3759 := by
    have hnat : (2562035347 : ℕ)^4783*100000000000000^3759 ≤ 42708127505817^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562035347 5000000000 42708127505817 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1674888331/10000000000 : ℝ), (5524367421/10000000000 : ℝ), (2562035347/5000000000 : ℝ)] ![(257353228669/2500000000000 : ℝ), (23498871670693/50000000000000 : ℝ), (42708127505817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1674888331/10000000000 : ℝ)|^4783 ≤ (257353228669/2500000000000 : ℝ)^3759
        have hw : |(-1674888331/10000000000 : ℝ)|=(1674888331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5524367421/10000000000 : ℝ)|^4783 ≤ (23498871670693/50000000000000 : ℝ)^3759
        have hw : |(5524367421/10000000000 : ℝ)|=(5524367421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2562035347/5000000000 : ℝ)|^4783 ≤ (42708127505817/100000000000000 : ℝ)^3759
        have hw : |(2562035347/5000000000 : ℝ)|=(2562035347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s1_1 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074037327/2000000000 : ℝ)*x 0 + (-942014989/5000000000 : ℝ)*x 1 + (5124070523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074037327/2000000000 : ℝ)^4783 ≤ (22667572532989/50000000000000 : ℝ)^3759 := by
    have hnat : (1074037327 : ℕ)^4783*50000000000000^3759 ≤ 22667572532989^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074037327 2000000000 22667572532989 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942014989/5000000000 : ℝ)^4783 ≤ (11956729223943/100000000000000 : ℝ)^3759 := by
    have hnat : (942014989 : ℕ)^4783*100000000000000^3759 ≤ 11956729223943^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942014989 5000000000 11956729223943 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5124070523/10000000000 : ℝ)^4783 ≤ (42708125692309/100000000000000 : ℝ)^3759 := by
    have hnat : (5124070523 : ℕ)^4783*100000000000000^3759 ≤ 42708125692309^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124070523 10000000000 42708125692309 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074037327/2000000000 : ℝ), (-942014989/5000000000 : ℝ), (5124070523/10000000000 : ℝ)] ![(22667572532989/50000000000000 : ℝ), (11956729223943/100000000000000 : ℝ), (42708125692309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074037327/2000000000 : ℝ)|^4783 ≤ (22667572532989/50000000000000 : ℝ)^3759
        have hw : |(1074037327/2000000000 : ℝ)|=(1074037327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-942014989/5000000000 : ℝ)|^4783 ≤ (11956729223943/100000000000000 : ℝ)^3759
        have hw : |(-942014989/5000000000 : ℝ)|=(942014989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5124070523/10000000000 : ℝ)|^4783 ≤ (42708125692309/100000000000000 : ℝ)^3759
        have hw : |(5124070523/10000000000 : ℝ)|=(5124070523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s1_2 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685093307/5000000000 : ℝ)*x 0 + (1024814091/2000000000 : ℝ)*x 1 + (-376806019/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685093307/5000000000 : ℝ)^4783 ≤ (22667572420201/50000000000000 : ℝ)^3759 := by
    have hnat : (2685093307 : ℕ)^4783*50000000000000^3759 ≤ 22667572420201^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685093307 5000000000 22667572420201 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024814091/2000000000 : ℝ)^4783 ≤ (10677031242787/25000000000000 : ℝ)^3759 := by
    have hnat : (1024814091 : ℕ)^4783*25000000000000^3759 ≤ 10677031242787^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024814091 2000000000 10677031242787 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376806019/2000000000 : ℝ)^4783 ≤ (597836508437/5000000000000 : ℝ)^3759 := by
    have hnat : (376806019 : ℕ)^4783*5000000000000^3759 ≤ 597836508437^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376806019 2000000000 597836508437 5000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685093307/5000000000 : ℝ), (1024814091/2000000000 : ℝ), (-376806019/2000000000 : ℝ)] ![(22667572420201/50000000000000 : ℝ), (10677031242787/25000000000000 : ℝ), (597836508437/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685093307/5000000000 : ℝ)|^4783 ≤ (22667572420201/50000000000000 : ℝ)^3759
        have hw : |(2685093307/5000000000 : ℝ)|=(2685093307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1024814091/2000000000 : ℝ)|^4783 ≤ (10677031242787/25000000000000 : ℝ)^3759
        have hw : |(1024814091/2000000000 : ℝ)|=(1024814091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-376806019/2000000000 : ℝ)|^4783 ≤ (597836508437/5000000000000 : ℝ)^3759
        have hw : |(-376806019/2000000000 : ℝ)|=(376806019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s1_3 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2098535431/5000000000 : ℝ)*x 0 + (3723623093/10000000000 : ℝ)*x 1 + (943013099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098535431/5000000000 : ℝ)^4783 ≤ (6626161475591/20000000000000 : ℝ)^3759 := by
    have hnat : (2098535431 : ℕ)^4783*20000000000000^3759 ≤ 6626161475591^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098535431 5000000000 6626161475591 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3723623093/10000000000 : ℝ)^4783 ≤ (28450588333513/100000000000000 : ℝ)^3759 := by
    have hnat : (3723623093 : ℕ)^4783*100000000000000^3759 ≤ 28450588333513^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3723623093 10000000000 28450588333513 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943013099/2000000000 : ℝ)^4783 ≤ (38418604279021/100000000000000 : ℝ)^3759 := by
    have hnat : (943013099 : ℕ)^4783*100000000000000^3759 ≤ 38418604279021^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943013099 2000000000 38418604279021 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098535431/5000000000 : ℝ), (3723623093/10000000000 : ℝ), (943013099/2000000000 : ℝ)] ![(6626161475591/20000000000000 : ℝ), (28450588333513/100000000000000 : ℝ), (38418604279021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098535431/5000000000 : ℝ)|^4783 ≤ (6626161475591/20000000000000 : ℝ)^3759
        have hw : |(2098535431/5000000000 : ℝ)|=(2098535431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3723623093/10000000000 : ℝ)|^4783 ≤ (28450588333513/100000000000000 : ℝ)^3759
        have hw : |(3723623093/10000000000 : ℝ)|=(3723623093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(943013099/2000000000 : ℝ)|^4783 ≤ (38418604279021/100000000000000 : ℝ)^3759
        have hw : |(943013099/2000000000 : ℝ)|=(943013099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s1_4 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-837549517/5000000000 : ℝ)*x 0 + (5128377801/10000000000 : ℝ)*x 1 + (5519994491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837549517/5000000000 : ℝ)^4783 ≤ (2573944241881/25000000000000 : ℝ)^3759 := by
    have hnat : (837549517 : ℕ)^4783*25000000000000^3759 ≤ 2573944241881^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837549517 5000000000 2573944241881 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128377801/10000000000 : ℝ)^4783 ≤ (668028296101/1562500000000 : ℝ)^3759 := by
    have hnat : (5128377801 : ℕ)^4783*1562500000000^3759 ≤ 668028296101^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128377801 10000000000 668028296101 1562500000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5519994491/10000000000 : ℝ)^4783 ≤ (23475206033689/50000000000000 : ℝ)^3759 := by
    have hnat : (5519994491 : ℕ)^4783*50000000000000^3759 ≤ 23475206033689^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519994491 10000000000 23475206033689 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-837549517/5000000000 : ℝ), (5128377801/10000000000 : ℝ), (5519994491/10000000000 : ℝ)] ![(2573944241881/25000000000000 : ℝ), (668028296101/1562500000000 : ℝ), (23475206033689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-837549517/5000000000 : ℝ)|^4783 ≤ (2573944241881/25000000000000 : ℝ)^3759
        have hw : |(-837549517/5000000000 : ℝ)|=(837549517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128377801/10000000000 : ℝ)|^4783 ≤ (668028296101/1562500000000 : ℝ)^3759
        have hw : |(5128377801/10000000000 : ℝ)|=(5128377801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5519994491/10000000000 : ℝ)|^4783 ≤ (23475206033689/50000000000000 : ℝ)^3759
        have hw : |(5519994491/10000000000 : ℝ)|=(5519994491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s1_5 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263602833/10000000000 : ℝ)*x 0 + (-744052759/5000000000 : ℝ)*x 1 + (1379998707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263602833/10000000000 : ℝ)^4783 ≤ (8838672427307/20000000000000 : ℝ)^3759 := by
    have hnat : (5263602833 : ℕ)^4783*20000000000000^3759 ≤ 8838672427307^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263602833 10000000000 8838672427307 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744052759/5000000000 : ℝ)^4783 ≤ (8856222139643/100000000000000 : ℝ)^3759 := by
    have hnat : (744052759 : ℕ)^4783*100000000000000^3759 ≤ 8856222139643^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744052759 5000000000 8856222139643 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379998707/2500000000 : ℝ)^4783 ≤ (4695041571457/10000000000000 : ℝ)^3759 := by
    have hnat : (1379998707 : ℕ)^4783*10000000000000^3759 ≤ 4695041571457^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379998707 2500000000 4695041571457 10000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263602833/10000000000 : ℝ), (-744052759/5000000000 : ℝ), (1379998707/2500000000 : ℝ)] ![(8838672427307/20000000000000 : ℝ), (8856222139643/100000000000000 : ℝ), (4695041571457/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263602833/10000000000 : ℝ)|^4783 ≤ (8838672427307/20000000000000 : ℝ)^3759
        have hw : |(5263602833/10000000000 : ℝ)|=(5263602833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-744052759/5000000000 : ℝ)|^4783 ≤ (8856222139643/100000000000000 : ℝ)^3759
        have hw : |(-744052759/5000000000 : ℝ)|=(744052759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379998707/2500000000 : ℝ)|^4783 ≤ (4695041571457/10000000000000 : ℝ)^3759
        have hw : |(1379998707/2500000000 : ℝ)|=(1379998707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s1_6 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263602183/10000000000 : ℝ)*x 0 + (2759997537/5000000000 : ℝ)*x 1 + (-744053041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263602183/10000000000 : ℝ)^4783 ≤ (8838671038489/20000000000000 : ℝ)^3759 := by
    have hnat : (5263602183 : ℕ)^4783*20000000000000^3759 ≤ 8838671038489^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263602183 10000000000 8838671038489 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2759997537/5000000000 : ℝ)^4783 ≤ (46950418376913/100000000000000 : ℝ)^3759 := by
    have hnat : (2759997537 : ℕ)^4783*100000000000000^3759 ≤ 46950418376913^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759997537 5000000000 46950418376913 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (744053041/5000000000 : ℝ)^4783 ≤ (1107028301321/12500000000000 : ℝ)^3759 := by
    have hnat : (744053041 : ℕ)^4783*12500000000000^3759 ≤ 1107028301321^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744053041 5000000000 1107028301321 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263602183/10000000000 : ℝ), (2759997537/5000000000 : ℝ), (-744053041/5000000000 : ℝ)] ![(8838671038489/20000000000000 : ℝ), (46950418376913/100000000000000 : ℝ), (1107028301321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263602183/10000000000 : ℝ)|^4783 ≤ (8838671038489/20000000000000 : ℝ)^3759
        have hw : |(5263602183/10000000000 : ℝ)|=(5263602183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2759997537/5000000000 : ℝ)|^4783 ≤ (46950418376913/100000000000000 : ℝ)^3759
        have hw : |(2759997537/5000000000 : ℝ)|=(2759997537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-744053041/5000000000 : ℝ)|^4783 ≤ (1107028301321/12500000000000 : ℝ)^3759
        have hw : |(-744053041/5000000000 : ℝ)|=(744053041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s1_7 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4197591027/10000000000 : ℝ)*x 0 + (2352199479/5000000000 : ℝ)*x 1 + (3734452893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197591027/10000000000 : ℝ)^4783 ≤ (16568016044223/50000000000000 : ℝ)^3759 := by
    have hnat : (4197591027 : ℕ)^4783*50000000000000^3759 ≤ 16568016044223^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197591027 10000000000 16568016044223 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2352199479/5000000000 : ℝ)^4783 ≤ (9577012762003/25000000000000 : ℝ)^3759 := by
    have hnat : (2352199479 : ℕ)^4783*25000000000000^3759 ≤ 9577012762003^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2352199479 5000000000 9577012762003 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3734452893/10000000000 : ℝ)^4783 ≤ (2855591683749/10000000000000 : ℝ)^3759 := by
    have hnat : (3734452893 : ℕ)^4783*10000000000000^3759 ≤ 2855591683749^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734452893 10000000000 2855591683749 10000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197591027/10000000000 : ℝ), (2352199479/5000000000 : ℝ), (3734452893/10000000000 : ℝ)] ![(16568016044223/50000000000000 : ℝ), (9577012762003/25000000000000 : ℝ), (2855591683749/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197591027/10000000000 : ℝ)|^4783 ≤ (16568016044223/50000000000000 : ℝ)^3759
        have hw : |(4197591027/10000000000 : ℝ)|=(4197591027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2352199479/5000000000 : ℝ)|^4783 ≤ (9577012762003/25000000000000 : ℝ)^3759
        have hw : |(2352199479/5000000000 : ℝ)|=(2352199479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3734452893/10000000000 : ℝ)|^4783 ≤ (2855591683749/10000000000000 : ℝ)^3759
        have hw : |(3734452893/10000000000 : ℝ)|=(3734452893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1616_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (519/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2309/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8861/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (519/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (519/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (519/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (519/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (519/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (519/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (519/12500 : ℝ) ^ (4779/1024 : ℝ) ≤ (3559736266911/10000000000000000000 : ℝ) := by
    have hpowers : (519/12500 : ℝ)^4779 ≤ (3559736266911/10000000000000000000 : ℝ)^1024 := by
      have hnat : (519 : ℕ)^4779*10000000000000000000^1024 ≤ 3559736266911^1024*12500^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        519 12500 3559736266911 10000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (519/12500 : ℝ)) (X := (3559736266911/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4821/20000 : ℝ) ^ (4779/1024 : ℝ) ≤ (32676748747652577/25000000000000000000 : ℝ) := by
    have hpowers : (4821/20000 : ℝ)^4779 ≤ (32676748747652577/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4821 : ℕ)^4779*25000000000000000000^1024 ≤ 32676748747652577^1024*20000^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4821 20000 32676748747652577 25000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4821/20000 : ℝ)) (X := (32676748747652577/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000003559736266911/5000000000000000000 : ℝ) ≤ (10000001525494421/10000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (5000003559736266911/5000000000000000000 : ℝ)^1024 ≤ (10000001525494421/10000000000000000 : ℝ)^4779 := by
      have hnat : (5000003559736266911 : ℕ)^1024*10000000000000000^4779 ≤ 10000001525494421^4779*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000003559736266911 5000000000000000000 10000001525494421 10000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001525494421/10000000000000000 : ℝ)) (X := (5000003559736266911/5000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50065371296176639709/50000000000000000000 : ℝ) ≤ (2000559998750853/2000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (50065371296176639709/50000000000000000000 : ℝ)^1024 ≤ (2000559998750853/2000000000000000 : ℝ)^4779 := by
      have hnat : (50065371296176639709 : ℕ)^1024*2000000000000000^4779 ≤ 2000559998750853^4779*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065371296176639709 50000000000000000000 2000559998750853 2000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000559998750853/2000000000000000 : ℝ)) (X := (50065371296176639709/50000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12532676748747652577/12500000000000000000 : ℝ) ≤ (10005598462014109/10000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (12532676748747652577/12500000000000000000 : ℝ)^1024 ≤ (10005598462014109/10000000000000000 : ℝ)^4779 := by
      have hnat : (12532676748747652577 : ℕ)^1024*10000000000000000^4779 ≤ 10005598462014109^4779*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12532676748747652577 12500000000000000000 10005598462014109 10000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005598462014109/10000000000000000 : ℝ)) (X := (12532676748747652577/12500000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3559736266911/10000000000000000000 : ℝ) ≤ ((66502263985920145879/66510000000000000000 : ℝ)+2*(699617064961/498825000000000 : ℝ)*(519/12500 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (66502263985920145879/66510000000000000000 : ℝ)+2*(699617064961/498825000000000 : ℝ)*(519/12500 : ℝ)=(10000001525494421/10000000000000000 : ℝ) by norm_num, show 1+2*(3559736266911/10000000000000000000 : ℝ)=(5000003559736266911/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32676748747652577/25000000000000000000 : ℝ)+(3559736266911/10000000000000000000 : ℝ) ≤ ((66502263985920145879/66510000000000000000 : ℝ)+(699617064961/498825000000000 : ℝ)*((4821/20000 : ℝ)+(519/12500 : ℝ)))^(4779/1024 : ℝ) := by
    rw [show (66502263985920145879/66510000000000000000 : ℝ)+(699617064961/498825000000000 : ℝ)*((4821/20000 : ℝ)+(519/12500 : ℝ))=(2000559998750853/2000000000000000 : ℝ) by norm_num, show 1+(32676748747652577/25000000000000000000 : ℝ)+(3559736266911/10000000000000000000 : ℝ)=(50065371296176639709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32676748747652577/25000000000000000000 : ℝ) ≤ ((66502263985920145879/66510000000000000000 : ℝ)+2*(699617064961/498825000000000 : ℝ)*(4821/20000 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (66502263985920145879/66510000000000000000 : ℝ)+2*(699617064961/498825000000000 : ℝ)*(4821/20000 : ℝ)=(10005598462014109/10000000000000000 : ℝ) by norm_num, show 1+2*(32676748747652577/25000000000000000000 : ℝ)=(12532676748747652577/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (66502263985920145879/66510000000000000000 : ℝ)*(X 1 0+X 2 0)+(699617064961/498825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (519/12500 : ℝ)) (hi := (4821/20000 : ℝ)) (c := (66502263985920145879/66510000000000000000 : ℝ)) (alpha := (699617064961/498825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (66502263985920145879/66510000000000000000 : ℝ)*(X 0 1+X 2 1)+(699617064961/498825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (519/12500 : ℝ)) (hi := (4821/20000 : ℝ)) (c := (66502263985920145879/66510000000000000000 : ℝ)) (alpha := (699617064961/498825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (66502263985920145879/66510000000000000000 : ℝ)*(X 0 2+X 1 2)+(699617064961/498825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (519/12500 : ℝ)) (hi := (4821/20000 : ℝ)) (c := (66502263985920145879/66510000000000000000 : ℝ)) (alpha := (699617064961/498825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1674888331/10000000000 : ℝ)*X 0 0+(5524367421/10000000000 : ℝ)*X 0 1+(2562035347/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074037327/2000000000 : ℝ)*X 1 0+(-942014989/5000000000 : ℝ)*X 1 1+(5124070523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685093307/5000000000 : ℝ)*X 2 0+(1024814091/2000000000 : ℝ)*X 2 1+(-376806019/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098535431/5000000000 : ℝ)*X 0 0+(3723623093/10000000000 : ℝ)*X 0 1+(943013099/2000000000 : ℝ)*X 0 2+(2098535431/5000000000 : ℝ)*X 1 0+(3723623093/10000000000 : ℝ)*X 1 1+(943013099/2000000000 : ℝ)*X 1 2+(2098535431/5000000000 : ℝ)*X 2 0+(3723623093/10000000000 : ℝ)*X 2 1+(943013099/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-837549517/5000000000 : ℝ)*X 0 0+(5128377801/10000000000 : ℝ)*X 0 1+(5519994491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5263602833/10000000000 : ℝ)*X 1 0+(-744052759/5000000000 : ℝ)*X 1 1+(1379998707/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5263602183/10000000000 : ℝ)*X 2 0+(2759997537/5000000000 : ℝ)*X 2 1+(-744053041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4197591027/10000000000 : ℝ)*X 0 0+(2352199479/5000000000 : ℝ)*X 0 1+(3734452893/10000000000 : ℝ)*X 0 2+(4197591027/10000000000 : ℝ)*X 1 0+(2352199479/5000000000 : ℝ)*X 1 1+(3734452893/10000000000 : ℝ)*X 1 2+(4197591027/10000000000 : ℝ)*X 2 0+(2352199479/5000000000 : ℝ)*X 2 1+(3734452893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (608092721586341489959864489/103921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (208665779/100000000000000 : ℝ)*(base1) + (1209768327/100000000000000 : ℝ)*(base19) + (47999973/4000000000000 : ℝ)*(base23) + (165796323/100000000000000 : ℝ)*(upper3) + (96200471/100000000000000 : ℝ)*(upper5) + (109587503237303/6250000000000 : ℝ)*(major0) + (109587503237303/6250000000000 : ℝ)*(major1) + (109587503237303/6250000000000 : ℝ)*(major2) + (2498154807480059/100000000000000 : ℝ)*(sp0) + (2498160320627269/100000000000000 : ℝ)*(sp1) + (156135020649767/6250000000000 : ℝ)*(sp2) + (126079322857019/12500000000000 : ℝ)*(sp3) + (1732895329/25000000000000 : ℝ)*(sp4) + (112082129/3125000000000 : ℝ)*(sp7) + (1008638378150061/100000000000000 : ℝ)*(f.failure) + (624540382598899/25000000000000 : ℝ)*(f.sum) + (286795417370357/99765000000000000000000000000 : ℝ)*base65 + (4138621141467085511/1247062500000000000000000000000000 : ℝ)*base67 + (1724634957889398011/1247062500000000000000000000000000 : ℝ)*base69 + (4714056208733335511/1247062500000000000000000000000000 : ℝ)*base71 + (28476984980521/49882500000000000000000000000 : ℝ)*base73 + (4963168246482835511/1247062500000000000000000000000000 : ℝ)*base75 + (1709192779987773011/1247062500000000000000000000000000 : ℝ)*base77 + (787051019105726989/1247062500000000000000000000000000 : ℝ)*base80 + (21785885630269/12470625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6184441/2500000000000000000000 : ℝ)*base89 + (6184441/2500000000000000000000 : ℝ)*base91 + (6184441/2500000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1576138433608727322265750099/207843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1551378743/100000000000000 : ℝ)*(base19) + (649950471/50000000000000 : ℝ)*(base23) + (1020503/2500000000000 : ℝ)*(upper2) + (39565271/12500000000000 : ℝ)*(upper3) + (17349131/25000000000000 : ℝ)*(upper5) + (112015561368659/6250000000000 : ℝ)*(major0) + (112015561368659/6250000000000 : ℝ)*(major1) + (112015561368659/6250000000000 : ℝ)*(major2) + (11733294633/100000000000000 : ℝ)*(sp1) + (11056777843/100000000000000 : ℝ)*(sp2) + (1276755798324013/50000000000000 : ℝ)*(sp4) + (51069966239493/2000000000000 : ℝ)*(sp5) + (2553499239969241/100000000000000 : ℝ)*(sp6) + (257746528593221/25000000000000 : ℝ)*(sp7) + (257746528593221/25000000000000 : ℝ)*(f.failure) + (1276755798324013/50000000000000 : ℝ)*(f.sum) + (48922902067297/12470625000000000000000000000 : ℝ)*base65 + (7103956658306706217/1247062500000000000000000000000000 : ℝ)*base68 + (7578654091646706217/1247062500000000000000000000000000 : ℝ)*base70 + (7341646240805143717/1247062500000000000000000000000000 : ℝ)*base72 + (67364908464917/49882500000000000000000000000 : ℝ)*base74 + (4474077647948518717/1247062500000000000000000000000000 : ℝ)*base76 + (2369400167986393717/1247062500000000000000000000000000 : ℝ)*base78 + (12712715743373518717/1247062500000000000000000000000000 : ℝ)*base80 + (97232141739911/99765000000000000000000000000 : ℝ)*base81 + (4100401/625000000000000000000 : ℝ)*base89 + (4100401/625000000000000000000 : ℝ)*base91 + (4100401/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1616_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (519/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2309/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8861/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1616_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1616_s2_0 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67519589/400000000 : ℝ)*x 0 + (218567239/400000000 : ℝ)*x 1 + (5175669767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67519589/400000000 : ℝ)^4783 ≤ (259917422917/2500000000000 : ℝ)^3759 := by
    have hnat : (67519589 : ℕ)^4783*2500000000000^3759 ≤ 259917422917^3759*400000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67519589 400000000 259917422917 2500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218567239/400000000 : ℝ)^4783 ≤ (46347202527407/100000000000000 : ℝ)^3759 := by
    have hnat : (218567239 : ℕ)^4783*100000000000000^3759 ≤ 46347202527407^3759*400000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218567239 400000000 46347202527407 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175669767/10000000000 : ℝ)^4783 ≤ (43256100545701/100000000000000 : ℝ)^3759 := by
    have hnat : (5175669767 : ℕ)^4783*100000000000000^3759 ≤ 43256100545701^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175669767 10000000000 43256100545701 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67519589/400000000 : ℝ), (218567239/400000000 : ℝ), (5175669767/10000000000 : ℝ)] ![(259917422917/2500000000000 : ℝ), (46347202527407/100000000000000 : ℝ), (43256100545701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67519589/400000000 : ℝ)|^4783 ≤ (259917422917/2500000000000 : ℝ)^3759
        have hw : |(-67519589/400000000 : ℝ)|=(67519589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218567239/400000000 : ℝ)|^4783 ≤ (46347202527407/100000000000000 : ℝ)^3759
        have hw : |(218567239/400000000 : ℝ)|=(218567239/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175669767/10000000000 : ℝ)|^4783 ≤ (43256100545701/100000000000000 : ℝ)^3759
        have hw : |(5175669767/10000000000 : ℝ)|=(5175669767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s2_1 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354461877/10000000000 : ℝ)*x 0 + (-459229587/2500000000 : ℝ)*x 1 + (2587834893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354461877/10000000000 : ℝ)^4783 ≤ (45166301589059/100000000000000 : ℝ)^3759 := by
    have hnat : (5354461877 : ℕ)^4783*100000000000000^3759 ≤ 45166301589059^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354461877 10000000000 45166301589059 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (459229587/2500000000 : ℝ)^4783 ≤ (11577597642853/100000000000000 : ℝ)^3759 := by
    have hnat : (459229587 : ℕ)^4783*100000000000000^3759 ≤ 11577597642853^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459229587 2500000000 11577597642853 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587834893/5000000000 : ℝ)^4783 ≤ (5407012593469/12500000000000 : ℝ)^3759 := by
    have hnat : (2587834893 : ℕ)^4783*12500000000000^3759 ≤ 5407012593469^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587834893 5000000000 5407012593469 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354461877/10000000000 : ℝ), (-459229587/2500000000 : ℝ), (2587834893/5000000000 : ℝ)] ![(45166301589059/100000000000000 : ℝ), (11577597642853/100000000000000 : ℝ), (5407012593469/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354461877/10000000000 : ℝ)|^4783 ≤ (45166301589059/100000000000000 : ℝ)^3759
        have hw : |(5354461877/10000000000 : ℝ)|=(5354461877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-459229587/2500000000 : ℝ)|^4783 ≤ (11577597642853/100000000000000 : ℝ)^3759
        have hw : |(-459229587/2500000000 : ℝ)|=(459229587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587834893/5000000000 : ℝ)|^4783 ≤ (5407012593469/12500000000000 : ℝ)^3759
        have hw : |(2587834893/5000000000 : ℝ)|=(2587834893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s2_2 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669307733/1250000000 : ℝ)*x 0 + (2587834863/5000000000 : ℝ)*x 1 + (-367383689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669307733/1250000000 : ℝ)^4783 ≤ (5645787681191/12500000000000 : ℝ)^3759 := by
    have hnat : (669307733 : ℕ)^4783*12500000000000^3759 ≤ 5645787681191^3759*1250000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669307733 1250000000 5645787681191 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587834863/5000000000 : ℝ)^4783 ≤ (21628050054847/50000000000000 : ℝ)^3759 := by
    have hnat : (2587834863 : ℕ)^4783*50000000000000^3759 ≤ 21628050054847^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587834863 5000000000 21628050054847 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (367383689/2000000000 : ℝ)^4783 ≤ (5788799210381/50000000000000 : ℝ)^3759 := by
    have hnat : (367383689 : ℕ)^4783*50000000000000^3759 ≤ 5788799210381^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367383689 2000000000 5788799210381 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669307733/1250000000 : ℝ), (2587834863/5000000000 : ℝ), (-367383689/2000000000 : ℝ)] ![(5645787681191/12500000000000 : ℝ), (21628050054847/50000000000000 : ℝ), (5788799210381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669307733/1250000000 : ℝ)|^4783 ≤ (5645787681191/12500000000000 : ℝ)^3759
        have hw : |(669307733/1250000000 : ℝ)|=(669307733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587834863/5000000000 : ℝ)|^4783 ≤ (21628050054847/50000000000000 : ℝ)^3759
        have hw : |(2587834863/5000000000 : ℝ)|=(2587834863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-367383689/2000000000 : ℝ)|^4783 ≤ (5788799210381/50000000000000 : ℝ)^3759
        have hw : |(-367383689/2000000000 : ℝ)|=(367383689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s2_3 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525844237/1250000000 : ℝ)*x 0 + (772208069/2000000000 : ℝ)*x 1 + (4575615363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525844237/1250000000 : ℝ)^4783 ≤ (33228095899829/100000000000000 : ℝ)^3759 := by
    have hnat : (525844237 : ℕ)^4783*100000000000000^3759 ≤ 33228095899829^3759*1250000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525844237 1250000000 33228095899829 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772208069/2000000000 : ℝ)^4783 ≤ (7448302200831/25000000000000 : ℝ)^3759 := by
    have hnat : (772208069 : ℕ)^4783*25000000000000^3759 ≤ 7448302200831^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772208069 2000000000 7448302200831 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4575615363/10000000000 : ℝ)^4783 ≤ (36978695283907/100000000000000 : ℝ)^3759 := by
    have hnat : (4575615363 : ℕ)^4783*100000000000000^3759 ≤ 36978695283907^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575615363 10000000000 36978695283907 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525844237/1250000000 : ℝ), (772208069/2000000000 : ℝ), (4575615363/10000000000 : ℝ)] ![(33228095899829/100000000000000 : ℝ), (7448302200831/25000000000000 : ℝ), (36978695283907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525844237/1250000000 : ℝ)|^4783 ≤ (33228095899829/100000000000000 : ℝ)^3759
        have hw : |(525844237/1250000000 : ℝ)|=(525844237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772208069/2000000000 : ℝ)|^4783 ≤ (7448302200831/25000000000000 : ℝ)^3759
        have hw : |(772208069/2000000000 : ℝ)|=(772208069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4575615363/10000000000 : ℝ)|^4783 ≤ (36978695283907/100000000000000 : ℝ)^3759
        have hw : |(4575615363/10000000000 : ℝ)|=(4575615363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s2_4 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-168806857/1000000000 : ℝ)*x 0 + (517791421/1000000000 : ℝ)*x 1 + (2730955971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168806857/1000000000 : ℝ)^4783 ≤ (5198657417137/50000000000000 : ℝ)^3759 := by
    have hnat : (168806857 : ℕ)^4783*50000000000000^3759 ≤ 5198657417137^3759*1000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168806857 1000000000 5198657417137 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517791421/1000000000 : ℝ)^4783 ≤ (10819992508267/25000000000000 : ℝ)^3759 := by
    have hnat : (517791421 : ℕ)^4783*25000000000000^3759 ≤ 10819992508267^3759*1000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517791421 1000000000 10819992508267 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730955971/5000000000 : ℝ)^4783 ≤ (23161357561573/50000000000000 : ℝ)^3759 := by
    have hnat : (2730955971 : ℕ)^4783*50000000000000^3759 ≤ 23161357561573^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730955971 5000000000 23161357561573 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168806857/1000000000 : ℝ), (517791421/1000000000 : ℝ), (2730955971/5000000000 : ℝ)] ![(5198657417137/50000000000000 : ℝ), (10819992508267/25000000000000 : ℝ), (23161357561573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168806857/1000000000 : ℝ)|^4783 ≤ (5198657417137/50000000000000 : ℝ)^3759
        have hw : |(-168806857/1000000000 : ℝ)|=(168806857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517791421/1000000000 : ℝ)|^4783 ≤ (10819992508267/25000000000000 : ℝ)^3759
        have hw : |(517791421/1000000000 : ℝ)|=(517791421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730955971/5000000000 : ℝ)|^4783 ≤ (23161357561573/50000000000000 : ℝ)^3759
        have hw : |(2730955971/5000000000 : ℝ)|=(2730955971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s2_5 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263887509/500000000 : ℝ)*x 0 + (-775338007/5000000000 : ℝ)*x 1 + (5461912013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263887509/500000000 : ℝ)^4783 ≤ (22172278293513/50000000000000 : ℝ)^3759 := by
    have hnat : (263887509 : ℕ)^4783*50000000000000^3759 ≤ 22172278293513^3759*500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263887509 500000000 22172278293513 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775338007/5000000000 : ℝ)^4783 ≤ (1166590938811/12500000000000 : ℝ)^3759 := by
    have hnat : (775338007 : ℕ)^4783*12500000000000^3759 ≤ 1166590938811^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775338007 5000000000 1166590938811 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461912013/10000000000 : ℝ)^4783 ≤ (23161357944667/50000000000000 : ℝ)^3759 := by
    have hnat : (5461912013 : ℕ)^4783*50000000000000^3759 ≤ 23161357944667^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461912013 10000000000 23161357944667 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263887509/500000000 : ℝ), (-775338007/5000000000 : ℝ), (5461912013/10000000000 : ℝ)] ![(22172278293513/50000000000000 : ℝ), (1166590938811/12500000000000 : ℝ), (23161357944667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263887509/500000000 : ℝ)|^4783 ≤ (22172278293513/50000000000000 : ℝ)^3759
        have hw : |(263887509/500000000 : ℝ)|=(263887509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-775338007/5000000000 : ℝ)|^4783 ≤ (1166590938811/12500000000000 : ℝ)^3759
        have hw : |(-775338007/5000000000 : ℝ)|=(775338007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461912013/10000000000 : ℝ)|^4783 ≤ (23161357944667/50000000000000 : ℝ)^3759
        have hw : |(5461912013/10000000000 : ℝ)|=(5461912013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s2_6 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277750217/10000000000 : ℝ)*x 0 + (1365477971/2500000000 : ℝ)*x 1 + (-96917259/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277750217/10000000000 : ℝ)^4783 ≤ (22172278491297/50000000000000 : ℝ)^3759 := by
    have hnat : (5277750217 : ℕ)^4783*50000000000000^3759 ≤ 22172278491297^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277750217 10000000000 22172278491297 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365477971/2500000000 : ℝ)^4783 ≤ (9264542899449/20000000000000 : ℝ)^3759 := by
    have hnat : (1365477971 : ℕ)^4783*20000000000000^3759 ≤ 9264542899449^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365477971 2500000000 9264542899449 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96917259/625000000 : ℝ)^4783 ≤ (2333182126507/25000000000000 : ℝ)^3759 := by
    have hnat : (96917259 : ℕ)^4783*25000000000000^3759 ≤ 2333182126507^3759*625000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96917259 625000000 2333182126507 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277750217/10000000000 : ℝ), (1365477971/2500000000 : ℝ), (-96917259/625000000 : ℝ)] ![(22172278491297/50000000000000 : ℝ), (9264542899449/20000000000000 : ℝ), (2333182126507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277750217/10000000000 : ℝ)|^4783 ≤ (22172278491297/50000000000000 : ℝ)^3759
        have hw : |(5277750217/10000000000 : ℝ)|=(5277750217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365477971/2500000000 : ℝ)|^4783 ≤ (9264542899449/20000000000000 : ℝ)^3759
        have hw : |(1365477971/2500000000 : ℝ)|=(1365477971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96917259/625000000 : ℝ)|^4783 ≤ (2333182126507/25000000000000 : ℝ)^3759
        have hw : |(-96917259/625000000 : ℝ)|=(96917259/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s2_7 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206949349/10000000000 : ℝ)*x 0 + (4570056473/10000000000 : ℝ)*x 1 + (3866660261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206949349/10000000000 : ℝ)^4783 ≤ (33230060306923/100000000000000 : ℝ)^3759 := by
    have hnat : (4206949349 : ℕ)^4783*100000000000000^3759 ≤ 33230060306923^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206949349 10000000000 33230060306923 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4570056473/10000000000 : ℝ)^4783 ≤ (36921541325139/100000000000000 : ℝ)^3759 := by
    have hnat : (4570056473 : ℕ)^4783*100000000000000^3759 ≤ 36921541325139^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570056473 10000000000 36921541325139 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3866660261/10000000000 : ℝ)^4783 ≤ (29848398357017/100000000000000 : ℝ)^3759 := by
    have hnat : (3866660261 : ℕ)^4783*100000000000000^3759 ≤ 29848398357017^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3866660261 10000000000 29848398357017 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206949349/10000000000 : ℝ), (4570056473/10000000000 : ℝ), (3866660261/10000000000 : ℝ)] ![(33230060306923/100000000000000 : ℝ), (36921541325139/100000000000000 : ℝ), (29848398357017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206949349/10000000000 : ℝ)|^4783 ≤ (33230060306923/100000000000000 : ℝ)^3759
        have hw : |(4206949349/10000000000 : ℝ)|=(4206949349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4570056473/10000000000 : ℝ)|^4783 ≤ (36921541325139/100000000000000 : ℝ)^3759
        have hw : |(4570056473/10000000000 : ℝ)|=(4570056473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3866660261/10000000000 : ℝ)|^4783 ≤ (29848398357017/100000000000000 : ℝ)^3759
        have hw : |(3866660261/10000000000 : ℝ)|=(3866660261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1616_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8861/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2309/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (207/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16469/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8861/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2309/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8861/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2309/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8861/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2309/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8861/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2309/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8861/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2309/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8861/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2309/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2309/25000 : ℝ) ^ (4779/1024 : ℝ) ≤ (742833636495331/50000000000000000000 : ℝ) := by
    have hpowers : (2309/25000 : ℝ)^4779 ≤ (742833636495331/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2309 : ℕ)^4779*50000000000000000000^1024 ≤ 742833636495331^1024*25000^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2309 25000 742833636495331 50000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2309/25000 : ℝ)) (X := (742833636495331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8861/50000 : ℝ) ^ (4779/1024 : ℝ) ≤ (3110389608177423/10000000000000000000 : ℝ) := by
    have hpowers : (8861/50000 : ℝ)^4779 ≤ (3110389608177423/10000000000000000000 : ℝ)^1024 := by
      have hnat : (8861 : ℕ)^4779*10000000000000000000^1024 ≤ 3110389608177423^1024*50000^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8861 50000 3110389608177423 10000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8861/50000 : ℝ)) (X := (3110389608177423/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000742833636495331/25000000000000000000 : ℝ) ≤ (5000031833135153/5000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (25000742833636495331/25000000000000000000 : ℝ)^1024 ≤ (5000031833135153/5000000000000000 : ℝ)^4779 := by
      have hnat : (25000742833636495331 : ℕ)^1024*5000000000000000^4779 ≤ 5000031833135153^4779*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000742833636495331 25000000000000000000 5000031833135153 5000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000031833135153/5000000000000000 : ℝ)) (X := (25000742833636495331/25000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008147390838691223/25000000000000000000 : ℝ) ≤ (5000349104844403/5000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (25008147390838691223/25000000000000000000 : ℝ)^1024 ≤ (5000349104844403/5000000000000000 : ℝ)^4779 := by
      have hnat : (25008147390838691223 : ℕ)^1024*5000000000000000^4779 ≤ 5000349104844403^4779*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008147390838691223 25000000000000000000 5000349104844403 5000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000349104844403/5000000000000000 : ℝ)) (X := (25008147390838691223/25000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003110389608177423/5000000000000000000 : ℝ) ≤ (5000666376553653/5000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (5003110389608177423/5000000000000000000 : ℝ)^1024 ≤ (5000666376553653/5000000000000000 : ℝ)^4779 := by
      have hnat : (5003110389608177423 : ℕ)^1024*5000000000000000^4779 ≤ 5000666376553653^4779*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003110389608177423 5000000000000000000 5000666376553653 5000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000666376553653/5000000000000000 : ℝ)) (X := (5003110389608177423/5000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(742833636495331/50000000000000000000 : ℝ) ≤ ((21212204746485821179/21215000000000000000 : ℝ)+2*(1269086837/1697200000000 : ℝ)*(2309/25000 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (21212204746485821179/21215000000000000000 : ℝ)+2*(1269086837/1697200000000 : ℝ)*(2309/25000 : ℝ)=(5000031833135153/5000000000000000 : ℝ) by norm_num, show 1+2*(742833636495331/50000000000000000000 : ℝ)=(25000742833636495331/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3110389608177423/10000000000000000000 : ℝ)+(742833636495331/50000000000000000000 : ℝ) ≤ ((21212204746485821179/21215000000000000000 : ℝ)+(1269086837/1697200000000 : ℝ)*((8861/50000 : ℝ)+(2309/25000 : ℝ)))^(4779/1024 : ℝ) := by
    rw [show (21212204746485821179/21215000000000000000 : ℝ)+(1269086837/1697200000000 : ℝ)*((8861/50000 : ℝ)+(2309/25000 : ℝ))=(5000349104844403/5000000000000000 : ℝ) by norm_num, show 1+(3110389608177423/10000000000000000000 : ℝ)+(742833636495331/50000000000000000000 : ℝ)=(25008147390838691223/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3110389608177423/10000000000000000000 : ℝ) ≤ ((21212204746485821179/21215000000000000000 : ℝ)+2*(1269086837/1697200000000 : ℝ)*(8861/50000 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (21212204746485821179/21215000000000000000 : ℝ)+2*(1269086837/1697200000000 : ℝ)*(8861/50000 : ℝ)=(5000666376553653/5000000000000000 : ℝ) by norm_num, show 1+2*(3110389608177423/10000000000000000000 : ℝ)=(5003110389608177423/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21212204746485821179/21215000000000000000 : ℝ)*(X 1 0+X 2 0)+(1269086837/1697200000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (2309/25000 : ℝ)) (hi := (8861/50000 : ℝ)) (c := (21212204746485821179/21215000000000000000 : ℝ)) (alpha := (1269086837/1697200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21212204746485821179/21215000000000000000 : ℝ)*(X 0 1+X 2 1)+(1269086837/1697200000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (2309/25000 : ℝ)) (hi := (8861/50000 : ℝ)) (c := (21212204746485821179/21215000000000000000 : ℝ)) (alpha := (1269086837/1697200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21212204746485821179/21215000000000000000 : ℝ)*(X 0 2+X 1 2)+(1269086837/1697200000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (2309/25000 : ℝ)) (hi := (8861/50000 : ℝ)) (c := (21212204746485821179/21215000000000000000 : ℝ)) (alpha := (1269086837/1697200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-67519589/400000000 : ℝ)*X 0 0+(218567239/400000000 : ℝ)*X 0 1+(5175669767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354461877/10000000000 : ℝ)*X 1 0+(-459229587/2500000000 : ℝ)*X 1 1+(2587834893/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669307733/1250000000 : ℝ)*X 2 0+(2587834863/5000000000 : ℝ)*X 2 1+(-367383689/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((525844237/1250000000 : ℝ)*X 0 0+(772208069/2000000000 : ℝ)*X 0 1+(4575615363/10000000000 : ℝ)*X 0 2+(525844237/1250000000 : ℝ)*X 1 0+(772208069/2000000000 : ℝ)*X 1 1+(4575615363/10000000000 : ℝ)*X 1 2+(525844237/1250000000 : ℝ)*X 2 0+(772208069/2000000000 : ℝ)*X 2 1+(4575615363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-168806857/1000000000 : ℝ)*X 0 0+(517791421/1000000000 : ℝ)*X 0 1+(2730955971/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((263887509/500000000 : ℝ)*X 1 0+(-775338007/5000000000 : ℝ)*X 1 1+(5461912013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277750217/10000000000 : ℝ)*X 2 0+(1365477971/2500000000 : ℝ)*X 2 1+(-96917259/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4206949349/10000000000 : ℝ)*X 0 0+(4570056473/10000000000 : ℝ)*X 0 1+(3866660261/10000000000 : ℝ)*X 0 2+(4206949349/10000000000 : ℝ)*X 1 0+(4570056473/10000000000 : ℝ)*X 1 1+(3866660261/10000000000 : ℝ)*X 1 2+(4206949349/10000000000 : ℝ)*X 2 0+(4570056473/10000000000 : ℝ)*X 2 1+(3866660261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (502038048316773765790637493/53037500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (307802871/20000000000000 : ℝ)*(base19) + (729688521/50000000000000 : ℝ)*(base23) + (38135561/100000000000000 : ℝ)*(lower2) + (275786457/100000000000000 : ℝ)*(upper3) + (149453757/100000000000000 : ℝ)*(upper5) + (243277653157811/10000000000000 : ℝ)*(major0) + (243277653157811/10000000000000 : ℝ)*(major1) + (243277653157811/10000000000000 : ℝ)*(major2) + (3466088453518693/100000000000000 : ℝ)*(sp0) + (1733051724211573/50000000000000 : ℝ)*(sp1) + (173305176403023/5000000000000 : ℝ)*(sp2) + (1399439869160933/100000000000000 : ℝ)*(sp3) + (16533918809/100000000000000 : ℝ)*(sp4) + (7891033827/100000000000000 : ℝ)*(sp7) + (34986194004869/2500000000000 : ℝ)*(f.failure) + (1733052493718751/50000000000000 : ℝ)*(f.sum) + (99545559719/530375000000000000000000000 : ℝ)*base65 + (1585282458405429169/212150000000000000000000000000000 : ℝ)*base67 + (181553342339670831/212150000000000000000000000000000 : ℝ)*base70 + (2221396622409629169/212150000000000000000000000000000 : ℝ)*base71 + (2452423450441/1060750000000000000000000000 : ℝ)*base74 + (1721369542224279169/212150000000000000000000000000000 : ℝ)*base75 + (962309200173929169/212150000000000000000000000000000 : ℝ)*base77 + (1136629251806179169/212150000000000000000000000000000 : ℝ)*base79 + (11638077556109/2121500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (50111/62500000000000000000 : ℝ)*base90 + (50111/62500000000000000000 : ℝ)*base92 + (50111/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4485966527486570914351128537/530375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68341803/5000000000000 : ℝ)*(base19) + (1499191137/100000000000000 : ℝ)*(base23) + (189641373/100000000000000 : ℝ)*(upper3) + (56705949/100000000000000 : ℝ)*(lower4) + (169296339/100000000000000 : ℝ)*(upper5) + (1235706929681667/50000000000000 : ℝ)*(major0) + (1235706929681667/50000000000000 : ℝ)*(major1) + (1235706929681667/50000000000000 : ℝ)*(major2) + (15918023441/100000000000000 : ℝ)*(sp1) + (15933610429/100000000000000 : ℝ)*(sp2) + (2816922931201/80000000000 : ℝ)*(sp4) + (3521136379141749/100000000000000 : ℝ)*(sp5) + (880284057799921/25000000000000 : ℝ)*(sp6) + (1421673772788637/100000000000000 : ℝ)*(sp7) + (1421673772788637/100000000000000 : ℝ)*(f.failure) + (2816922931201/80000000000 : ℝ)*(f.sum) + (25400723983659/4243000000000000000000000000 : ℝ)*base66 + (10102798068366624607/1060750000000000000000000000000000 : ℝ)*base68 + (2522595783193624607/1060750000000000000000000000000000 : ℝ)*base70 + (7996160331023374607/1060750000000000000000000000000000 : ℝ)*base72 + (22258182243421/4243000000000000000000000000 : ℝ)*base74 + (7867138900620874607/1060750000000000000000000000000000 : ℝ)*base76 + (4026184129073624607/1060750000000000000000000000000000 : ℝ)*base78 + (595353745924124607/1060750000000000000000000000000000 : ℝ)*base80 + (1163769085027/1060750000000000000000000000 : ℝ)*base82 + (15581097/2500000000000000000000 : ℝ)*base89 + (15581097/2500000000000000000000 : ℝ)*base91 + (15581097/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1616_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8861/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2309/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16469/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1616_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1616_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16469/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1616_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1616_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1616_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16469/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1616_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
