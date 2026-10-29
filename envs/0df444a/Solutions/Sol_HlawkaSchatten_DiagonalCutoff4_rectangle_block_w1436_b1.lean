-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1436_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:53.483086+00:00
-- url     : https://prove2.me/submissions/890a69fd-b7d5-4f4e-9609-93f196378a18

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
theorem support_rectangle_w1436_s3_0 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-392890101/2000000000 : ℝ)*x 0 + (1083315237/2000000000 : ℝ)*x 1 + (5239011209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (392890101/2000000000 : ℝ)^1099 ≤ (11984348333507/100000000000000 : ℝ)^843 := by
    have hnat : (392890101 : ℕ)^1099*100000000000000^843 ≤ 11984348333507^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392890101 2000000000 11984348333507 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083315237/2000000000 : ℝ)^1099 ≤ (11240953114939/25000000000000 : ℝ)^843 := by
    have hnat : (1083315237 : ℕ)^1099*25000000000000^843 ≤ 11240953114939^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083315237 2000000000 11240953114939 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239011209/10000000000 : ℝ)^1099 ≤ (43051839195069/100000000000000 : ℝ)^843 := by
    have hnat : (5239011209 : ℕ)^1099*100000000000000^843 ≤ 43051839195069^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239011209 10000000000 43051839195069 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-392890101/2000000000 : ℝ), (1083315237/2000000000 : ℝ), (5239011209/10000000000 : ℝ)] ![(11984348333507/100000000000000 : ℝ), (11240953114939/25000000000000 : ℝ), (43051839195069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-392890101/2000000000 : ℝ)|^1099 ≤ (11984348333507/100000000000000 : ℝ)^843
        have hw : |(-392890101/2000000000 : ℝ)|=(392890101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083315237/2000000000 : ℝ)|^1099 ≤ (11240953114939/25000000000000 : ℝ)^843
        have hw : |(1083315237/2000000000 : ℝ)|=(1083315237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239011209/10000000000 : ℝ)|^1099 ≤ (43051839195069/100000000000000 : ℝ)^843
        have hw : |(5239011209/10000000000 : ℝ)|=(5239011209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s3_1 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349432217/10000000000 : ℝ)*x 0 + (-513753619/2500000000 : ℝ)*x 1 + (130975273/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349432217/10000000000 : ℝ)^1099 ≤ (44238550620693/100000000000000 : ℝ)^843 := by
    have hnat : (5349432217 : ℕ)^1099*100000000000000^843 ≤ 44238550620693^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349432217 10000000000 44238550620693 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513753619/2500000000 : ℝ)^1099 ≤ (12709613267523/100000000000000 : ℝ)^843 := by
    have hnat : (513753619 : ℕ)^1099*100000000000000^843 ≤ 12709613267523^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513753619 2500000000 12709613267523 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130975273/250000000 : ℝ)^1099 ≤ (21525918049501/50000000000000 : ℝ)^843 := by
    have hnat : (130975273 : ℕ)^1099*50000000000000^843 ≤ 21525918049501^843*250000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130975273 250000000 21525918049501 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349432217/10000000000 : ℝ), (-513753619/2500000000 : ℝ), (130975273/250000000 : ℝ)] ![(44238550620693/100000000000000 : ℝ), (12709613267523/100000000000000 : ℝ), (21525918049501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349432217/10000000000 : ℝ)|^1099 ≤ (44238550620693/100000000000000 : ℝ)^843
        have hw : |(5349432217/10000000000 : ℝ)|=(5349432217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513753619/2500000000 : ℝ)|^1099 ≤ (12709613267523/100000000000000 : ℝ)^843
        have hw : |(-513753619/2500000000 : ℝ)|=(513753619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130975273/250000000 : ℝ)|^1099 ≤ (21525918049501/50000000000000 : ℝ)^843
        have hw : |(130975273/250000000 : ℝ)|=(130975273/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s3_2 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349432191/10000000000 : ℝ)*x 0 + (5239010861/10000000000 : ℝ)*x 1 + (-2055014589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349432191/10000000000 : ℝ)^1099 ≤ (1382454698137/3125000000000 : ℝ)^843 := by
    have hnat : (5349432191 : ℕ)^1099*3125000000000^843 ≤ 1382454698137^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349432191 10000000000 1382454698137 3125000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239010861/10000000000 : ℝ)^1099 ≤ (43051835466933/100000000000000 : ℝ)^843 := by
    have hnat : (5239010861 : ℕ)^1099*100000000000000^843 ≤ 43051835466933^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239010861 10000000000 43051835466933 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055014589/10000000000 : ℝ)^1099 ≤ (12709614178623/100000000000000 : ℝ)^843 := by
    have hnat : (2055014589 : ℕ)^1099*100000000000000^843 ≤ 12709614178623^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055014589 10000000000 12709614178623 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349432191/10000000000 : ℝ), (5239010861/10000000000 : ℝ), (-2055014589/10000000000 : ℝ)] ![(1382454698137/3125000000000 : ℝ), (43051835466933/100000000000000 : ℝ), (12709614178623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349432191/10000000000 : ℝ)|^1099 ≤ (1382454698137/3125000000000 : ℝ)^843
        have hw : |(5349432191/10000000000 : ℝ)|=(5349432191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239010861/10000000000 : ℝ)|^1099 ≤ (43051835466933/100000000000000 : ℝ)^843
        have hw : |(5239010861/10000000000 : ℝ)|=(5239010861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055014589/10000000000 : ℝ)|^1099 ≤ (12709614178623/100000000000000 : ℝ)^843
        have hw : |(-2055014589/10000000000 : ℝ)|=(2055014589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s3_3 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4302005863/10000000000 : ℝ)*x 0 + (4113310741/10000000000 : ℝ)*x 1 + (899685609/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302005863/10000000000 : ℝ)^1099 ≤ (33298539082569/100000000000000 : ℝ)^843 := by
    have hnat : (4302005863 : ℕ)^1099*100000000000000^843 ≤ 33298539082569^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302005863 10000000000 33298539082569 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4113310741/10000000000 : ℝ)^1099 ≤ (15703636352709/50000000000000 : ℝ)^843 := by
    have hnat : (4113310741 : ℕ)^1099*50000000000000^843 ≤ 15703636352709^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4113310741 10000000000 15703636352709 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899685609/2000000000 : ℝ)^1099 ≤ (17647094095161/50000000000000 : ℝ)^843 := by
    have hnat : (899685609 : ℕ)^1099*50000000000000^843 ≤ 17647094095161^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899685609 2000000000 17647094095161 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302005863/10000000000 : ℝ), (4113310741/10000000000 : ℝ), (899685609/2000000000 : ℝ)] ![(33298539082569/100000000000000 : ℝ), (15703636352709/50000000000000 : ℝ), (17647094095161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302005863/10000000000 : ℝ)|^1099 ≤ (33298539082569/100000000000000 : ℝ)^843
        have hw : |(4302005863/10000000000 : ℝ)|=(4302005863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4113310741/10000000000 : ℝ)|^1099 ≤ (15703636352709/50000000000000 : ℝ)^843
        have hw : |(4113310741/10000000000 : ℝ)|=(4113310741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899685609/2000000000 : ℝ)|^1099 ≤ (17647094095161/50000000000000 : ℝ)^843
        have hw : |(899685609/2000000000 : ℝ)|=(899685609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s3_4 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1964465391/10000000000 : ℝ)*x 0 + (523971839/1000000000 : ℝ)*x 1 + (5415865157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1964465391/10000000000 : ℝ)^1099 ≤ (59922333627/500000000000 : ℝ)^843 := by
    have hnat : (1964465391 : ℕ)^1099*500000000000^843 ≤ 59922333627^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964465391 10000000000 59922333627 500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523971839/1000000000 : ℝ)^1099 ≤ (10764853851181/25000000000000 : ℝ)^843 := by
    have hnat : (523971839 : ℕ)^1099*25000000000000^843 ≤ 10764853851181^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523971839 1000000000 10764853851181 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415865157/10000000000 : ℝ)^1099 ≤ (44956117852877/100000000000000 : ℝ)^843 := by
    have hnat : (5415865157 : ℕ)^1099*100000000000000^843 ≤ 44956117852877^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415865157 10000000000 44956117852877 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1964465391/10000000000 : ℝ), (523971839/1000000000 : ℝ), (5415865157/10000000000 : ℝ)] ![(59922333627/500000000000 : ℝ), (10764853851181/25000000000000 : ℝ), (44956117852877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1964465391/10000000000 : ℝ)|^1099 ≤ (59922333627/500000000000 : ℝ)^843
        have hw : |(-1964465391/10000000000 : ℝ)|=(1964465391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523971839/1000000000 : ℝ)|^1099 ≤ (10764853851181/25000000000000 : ℝ)^843
        have hw : |(523971839/1000000000 : ℝ)|=(523971839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415865157/10000000000 : ℝ)|^1099 ≤ (44956117852877/100000000000000 : ℝ)^843
        have hw : |(5415865157/10000000000 : ℝ)|=(5415865157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s3_5 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (331452457/625000000 : ℝ)*x 0 + (-1878160413/10000000000 : ℝ)*x 1 + (541586511/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331452457/625000000 : ℝ)^1099 ≤ (43741194288933/100000000000000 : ℝ)^843 := by
    have hnat : (331452457 : ℕ)^1099*100000000000000^843 ≤ 43741194288933^843*625000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331452457 625000000 43741194288933 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1878160413/10000000000 : ℝ)^1099 ≤ (2260537671813/20000000000000 : ℝ)^843 := by
    have hnat : (1878160413 : ℕ)^1099*20000000000000^843 ≤ 2260537671813^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878160413 10000000000 2260537671813 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541586511/1000000000 : ℝ)^1099 ≤ (22478058672131/50000000000000 : ℝ)^843 := by
    have hnat : (541586511 : ℕ)^1099*50000000000000^843 ≤ 22478058672131^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541586511 1000000000 22478058672131 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331452457/625000000 : ℝ), (-1878160413/10000000000 : ℝ), (541586511/1000000000 : ℝ)] ![(43741194288933/100000000000000 : ℝ), (2260537671813/20000000000000 : ℝ), (22478058672131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331452457/625000000 : ℝ)|^1099 ≤ (43741194288933/100000000000000 : ℝ)^843
        have hw : |(331452457/625000000 : ℝ)|=(331452457/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1878160413/10000000000 : ℝ)|^1099 ≤ (2260537671813/20000000000000 : ℝ)^843
        have hw : |(-1878160413/10000000000 : ℝ)|=(1878160413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541586511/1000000000 : ℝ)|^1099 ≤ (22478058672131/50000000000000 : ℝ)^843
        have hw : |(541586511/1000000000 : ℝ)|=(541586511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s3_6 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5303239001/10000000000 : ℝ)*x 0 + (676983179/1250000000 : ℝ)*x 1 + (-375632079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303239001/10000000000 : ℝ)^1099 ≤ (10935297736207/25000000000000 : ℝ)^843 := by
    have hnat : (5303239001 : ℕ)^1099*25000000000000^843 ≤ 10935297736207^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303239001 10000000000 10935297736207 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676983179/1250000000 : ℝ)^1099 ≤ (22478060414407/50000000000000 : ℝ)^843 := by
    have hnat : (676983179 : ℕ)^1099*50000000000000^843 ≤ 22478060414407^843*1250000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676983179 1250000000 22478060414407 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375632079/2000000000 : ℝ)^1099 ≤ (5651344108923/50000000000000 : ℝ)^843 := by
    have hnat : (375632079 : ℕ)^1099*50000000000000^843 ≤ 5651344108923^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375632079 2000000000 5651344108923 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303239001/10000000000 : ℝ), (676983179/1250000000 : ℝ), (-375632079/2000000000 : ℝ)] ![(10935297736207/25000000000000 : ℝ), (22478060414407/50000000000000 : ℝ), (5651344108923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303239001/10000000000 : ℝ)|^1099 ≤ (10935297736207/25000000000000 : ℝ)^843
        have hw : |(5303239001/10000000000 : ℝ)|=(5303239001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676983179/1250000000 : ℝ)|^1099 ≤ (22478060414407/50000000000000 : ℝ)^843
        have hw : |(676983179/1250000000 : ℝ)|=(676983179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-375632079/2000000000 : ℝ)|^1099 ≤ (5651344108923/50000000000000 : ℝ)^843
        have hw : |(-375632079/2000000000 : ℝ)|=(375632079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s3_7 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4302038563/10000000000 : ℝ)*x 0 + (179875793/400000000 : ℝ)*x 1 + (2057426443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302038563/10000000000 : ℝ)^1099 ≤ (33298869051123/100000000000000 : ℝ)^843 := by
    have hnat : (4302038563 : ℕ)^1099*100000000000000^843 ≤ 33298869051123^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302038563 10000000000 33298869051123 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179875793/400000000 : ℝ)^1099 ≤ (35278506440011/100000000000000 : ℝ)^843 := by
    have hnat : (179875793 : ℕ)^1099*100000000000000^843 ≤ 35278506440011^843*400000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179875793 400000000 35278506440011 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057426443/5000000000 : ℝ)^1099 ≤ (3927828060747/12500000000000 : ℝ)^843 := by
    have hnat : (2057426443 : ℕ)^1099*12500000000000^843 ≤ 3927828060747^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057426443 5000000000 3927828060747 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302038563/10000000000 : ℝ), (179875793/400000000 : ℝ), (2057426443/5000000000 : ℝ)] ![(33298869051123/100000000000000 : ℝ), (35278506440011/100000000000000 : ℝ), (3927828060747/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302038563/10000000000 : ℝ)|^1099 ≤ (33298869051123/100000000000000 : ℝ)^843
        have hw : |(4302038563/10000000000 : ℝ)|=(4302038563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179875793/400000000 : ℝ)|^1099 ≤ (35278506440011/100000000000000 : ℝ)^843
        have hw : |(179875793/400000000 : ℝ)|=(179875793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2057426443/5000000000 : ℝ)|^1099 ≤ (3927828060747/12500000000000 : ℝ)^843
        have hw : |(2057426443/5000000000 : ℝ)|=(2057426443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1436_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7889/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5591/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14943/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7889/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2081/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7889/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2081/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7889/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2081/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7889/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2081/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7889/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2081/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7889/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2081/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2081/20000 : ℝ) ^ (4395/1024 : ℝ) ≤ (3026778978182981/50000000000000000000 : ℝ) := by
    have hpowers : (2081/20000 : ℝ)^4395 ≤ (3026778978182981/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2081 : ℕ)^4395*50000000000000000000^1024 ≤ 3026778978182981^1024*20000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2081 20000 3026778978182981 50000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2081/20000 : ℝ)) (X := (3026778978182981/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7889/50000 : ℝ) ^ (4395/1024 : ℝ) ≤ (36144751396749439/100000000000000000000 : ℝ) := by
    have hpowers : (7889/50000 : ℝ)^4395 ≤ (36144751396749439/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7889 : ℕ)^4395*100000000000000000000^1024 ≤ 36144751396749439^1024*50000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7889 50000 36144751396749439 100000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7889/50000 : ℝ)) (X := (36144751396749439/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003026778978182981/25000000000000000000 : ℝ) ≤ (2000056414612493/2000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (25003026778978182981/25000000000000000000 : ℝ)^1024 ≤ (2000056414612493/2000000000000000 : ℝ)^4395 := by
      have hnat : (25003026778978182981 : ℕ)^1024*2000000000000000^4395 ≤ 2000056414612493^4395*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003026778978182981 25000000000000000000 2000056414612493 2000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056414612493/2000000000000000 : ℝ)) (X := (25003026778978182981/25000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042198309353115401/100000000000000000000 : ℝ) ≤ (10000983027931127/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (100042198309353115401/100000000000000000000 : ℝ)^1024 ≤ (10000983027931127/10000000000000000 : ℝ)^4395 := by
      have hnat : (100042198309353115401 : ℕ)^1024*10000000000000000^4395 ≤ 10000983027931127^4395*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042198309353115401 100000000000000000000 10000983027931127 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000983027931127/10000000000000000 : ℝ)) (X := (100042198309353115401/100000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036144751396749439/50000000000000000000 : ℝ) ≤ (10001683982799789/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (50036144751396749439/50000000000000000000 : ℝ)^1024 ≤ (10001683982799789/10000000000000000 : ℝ)^4395 := by
      have hnat : (50036144751396749439 : ℕ)^1024*10000000000000000^4395 ≤ 10001683982799789^4395*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036144751396749439 50000000000000000000 10001683982799789 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001683982799789/10000000000000000 : ℝ)) (X := (50036144751396749439/50000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3026778978182981/50000000000000000000 : ℝ) ≤ ((2148677148309910729/2149200000000000000 : ℝ)+2*(350477434331/268650000000000 : ℝ)*(2081/20000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (2148677148309910729/2149200000000000000 : ℝ)+2*(350477434331/268650000000000 : ℝ)*(2081/20000 : ℝ)=(2000056414612493/2000000000000000 : ℝ) by norm_num, show 1+2*(3026778978182981/50000000000000000000 : ℝ)=(25003026778978182981/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36144751396749439/100000000000000000000 : ℝ)+(3026778978182981/50000000000000000000 : ℝ) ≤ ((2148677148309910729/2149200000000000000 : ℝ)+(350477434331/268650000000000 : ℝ)*((7889/50000 : ℝ)+(2081/20000 : ℝ)))^(4395/1024 : ℝ) := by
    rw [show (2148677148309910729/2149200000000000000 : ℝ)+(350477434331/268650000000000 : ℝ)*((7889/50000 : ℝ)+(2081/20000 : ℝ))=(10000983027931127/10000000000000000 : ℝ) by norm_num, show 1+(36144751396749439/100000000000000000000 : ℝ)+(3026778978182981/50000000000000000000 : ℝ)=(100042198309353115401/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36144751396749439/100000000000000000000 : ℝ) ≤ ((2148677148309910729/2149200000000000000 : ℝ)+2*(350477434331/268650000000000 : ℝ)*(7889/50000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (2148677148309910729/2149200000000000000 : ℝ)+2*(350477434331/268650000000000 : ℝ)*(7889/50000 : ℝ)=(10001683982799789/10000000000000000 : ℝ) by norm_num, show 1+2*(36144751396749439/100000000000000000000 : ℝ)=(50036144751396749439/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2148677148309910729/2149200000000000000 : ℝ)*(X 1 0+X 2 0)+(350477434331/268650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (2081/20000 : ℝ)) (hi := (7889/50000 : ℝ)) (c := (2148677148309910729/2149200000000000000 : ℝ)) (alpha := (350477434331/268650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2148677148309910729/2149200000000000000 : ℝ)*(X 0 1+X 2 1)+(350477434331/268650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (2081/20000 : ℝ)) (hi := (7889/50000 : ℝ)) (c := (2148677148309910729/2149200000000000000 : ℝ)) (alpha := (350477434331/268650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2148677148309910729/2149200000000000000 : ℝ)*(X 0 2+X 1 2)+(350477434331/268650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (2081/20000 : ℝ)) (hi := (7889/50000 : ℝ)) (c := (2148677148309910729/2149200000000000000 : ℝ)) (alpha := (350477434331/268650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-392890101/2000000000 : ℝ)*X 0 0+(1083315237/2000000000 : ℝ)*X 0 1+(5239011209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349432217/10000000000 : ℝ)*X 1 0+(-513753619/2500000000 : ℝ)*X 1 1+(130975273/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349432191/10000000000 : ℝ)*X 2 0+(5239010861/10000000000 : ℝ)*X 2 1+(-2055014589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302005863/10000000000 : ℝ)*X 0 0+(4113310741/10000000000 : ℝ)*X 0 1+(899685609/2000000000 : ℝ)*X 0 2+(4302005863/10000000000 : ℝ)*X 1 0+(4113310741/10000000000 : ℝ)*X 1 1+(899685609/2000000000 : ℝ)*X 1 2+(4302005863/10000000000 : ℝ)*X 2 0+(4113310741/10000000000 : ℝ)*X 2 1+(899685609/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1964465391/10000000000 : ℝ)*X 0 0+(523971839/1000000000 : ℝ)*X 0 1+(5415865157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331452457/625000000 : ℝ)*X 1 0+(-1878160413/10000000000 : ℝ)*X 1 1+(541586511/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303239001/10000000000 : ℝ)*X 2 0+(676983179/1250000000 : ℝ)*X 2 1+(-375632079/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302038563/10000000000 : ℝ)*X 0 0+(179875793/400000000 : ℝ)*X 0 1+(2057426443/5000000000 : ℝ)*X 0 2+(4302038563/10000000000 : ℝ)*X 1 0+(179875793/400000000 : ℝ)*X 1 1+(2057426443/5000000000 : ℝ)*X 1 2+(4302038563/10000000000 : ℝ)*X 2 0+(179875793/400000000 : ℝ)*X 2 1+(2057426443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24662376466346065813218163/2238750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (366630943/20000000000000 : ℝ)*(base19) + (1789925481/100000000000000 : ℝ)*(base23) + (57737509/20000000000000 : ℝ)*(upper3) + (339301/4000000000000 : ℝ)*(upper4) + (28055593/20000000000000 : ℝ)*(upper5) + (257138335838147/6250000000000 : ℝ)*(major0) + (257138335838147/6250000000000 : ℝ)*(major1) + (257138335838147/6250000000000 : ℝ)*(major2) + (1407942552709151/25000000000000 : ℝ)*(sp0) + (2815896100267601/50000000000000 : ℝ)*(sp1) + (1407948060941109/25000000000000 : ℝ)*(sp2) + (1298310432688873/50000000000000 : ℝ)*(sp3) + (372232083/1562500000000 : ℝ)*(sp4) + (1435068559/12500000000000 : ℝ)*(sp7) + (1298316172963109/50000000000000 : ℝ)*(f.failure) + (5631794033689917/100000000000000 : ℝ)*(f.sum) + (75178486717253/13432500000000000000000000000 : ℝ)*base66 + (33772342544940163/13432500000000000000000000000000 : ℝ)*base67 + (72728716330679837/13432500000000000000000000000000 : ℝ)*base70 + (9530135394375163/13432500000000000000000000000000 : ℝ)*base71 + (22020744959693/13432500000000000000000000000 : ℝ)*base74 + (55482214041329837/13432500000000000000000000000000 : ℝ)*base76 + (107842464512789837/13432500000000000000000000000000 : ℝ)*base78 + (240493194352679837/13432500000000000000000000000000 : ℝ)*base80 + (25418857491323/13432500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (7980909/5000000000000000000000 : ℝ)*base89 + (7980909/5000000000000000000000 : ℝ)*base91 + (7980909/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17339817037783704359093077/1791000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (676591749/100000000000000 : ℝ)*(base19) + (538288869/100000000000000 : ℝ)*(base23) + (91358239/100000000000000 : ℝ)*(upper3) + (723937/800000000000 : ℝ)*(lower4) + (87599709/100000000000000 : ℝ)*(upper5) + (414729611220413/10000000000000 : ℝ)*(major0) + (414729611220413/10000000000000 : ℝ)*(major1) + (414729611220413/10000000000000 : ℝ)*(major2) + (2172617659/20000000000000 : ℝ)*(sp1) + (13616611749/100000000000000 : ℝ)*(sp2) + (567707981476357/10000000000000 : ℝ)*(sp4) + (2838534137541763/50000000000000 : ℝ)*(sp5) + (5677065659862953/100000000000000 : ℝ)*(sp6) + (327189010865419/12500000000000 : ℝ)*(sp7) + (327189010865419/12500000000000 : ℝ)*(f.failure) + (567707981476357/10000000000000 : ℝ)*(f.sum) + (103006004837/2686500000000000000000000000 : ℝ)*base65 + (160756811742264923/21492000000000000000000000000000 : ℝ)*base68 + (886268374031077/21492000000000000000000000000000 : ℝ)*base69 + (190142642873940923/21492000000000000000000000000000 : ℝ)*base72 + (14956606917023/2686500000000000000000000000 : ℝ)*base73 + (434808770750808923/21492000000000000000000000000000 : ℝ)*base76 + (159165533058360923/21492000000000000000000000000000 : ℝ)*base78 + (350107656515484923/21492000000000000000000000000000 : ℝ)*base80 + (944680226179/335812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6985219/1250000000000000000000 : ℝ)*base89 + (6985219/1250000000000000000000 : ℝ)*base91 + (6985219/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1436_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7889/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14943/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1436_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1436_s4_0 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-982658773/5000000000 : ℝ)*x 0 + (5409165967/10000000000 : ℝ)*x 1 + (5245850179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (982658773/5000000000 : ℝ)^1099 ≤ (5995622285313/50000000000000 : ℝ)^843 := by
    have hnat : (982658773 : ℕ)^1099*50000000000000^843 ≤ 5995622285313^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982658773 5000000000 5995622285313 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409165967/10000000000 : ℝ)^1099 ≤ (8976727117049/20000000000000 : ℝ)^843 := by
    have hnat : (5409165967 : ℕ)^1099*20000000000000^843 ≤ 8976727117049^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409165967 10000000000 8976727117049 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245850179/10000000000 : ℝ)^1099 ≤ (10781279958397/25000000000000 : ℝ)^843 := by
    have hnat : (5245850179 : ℕ)^1099*25000000000000^843 ≤ 10781279958397^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245850179 10000000000 10781279958397 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-982658773/5000000000 : ℝ), (5409165967/10000000000 : ℝ), (5245850179/10000000000 : ℝ)] ![(5995622285313/50000000000000 : ℝ), (8976727117049/20000000000000 : ℝ), (10781279958397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-982658773/5000000000 : ℝ)|^1099 ≤ (5995622285313/50000000000000 : ℝ)^843
        have hw : |(-982658773/5000000000 : ℝ)|=(982658773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409165967/10000000000 : ℝ)|^1099 ≤ (8976727117049/20000000000000 : ℝ)^843
        have hw : |(5409165967/10000000000 : ℝ)|=(5409165967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245850179/10000000000 : ℝ)|^1099 ≤ (10781279958397/25000000000000 : ℝ)^843
        have hw : |(5245850179/10000000000 : ℝ)|=(5245850179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s4_1 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347517149/10000000000 : ℝ)*x 0 + (-2048482453/10000000000 : ℝ)*x 1 + (1049170089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347517149/10000000000 : ℝ)^1099 ≤ (5527238148981/12500000000000 : ℝ)^843 := by
    have hnat : (5347517149 : ℕ)^1099*12500000000000^843 ≤ 5527238148981^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347517149 10000000000 5527238148981 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2048482453/10000000000 : ℝ)^1099 ≤ (1265697210593/10000000000000 : ℝ)^843 := by
    have hnat : (2048482453 : ℕ)^1099*10000000000000^843 ≤ 1265697210593^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048482453 10000000000 1265697210593 10000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049170089/2000000000 : ℝ)^1099 ≤ (1347660083887/3125000000000 : ℝ)^843 := by
    have hnat : (1049170089 : ℕ)^1099*3125000000000^843 ≤ 1347660083887^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049170089 2000000000 1347660083887 3125000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347517149/10000000000 : ℝ), (-2048482453/10000000000 : ℝ), (1049170089/2000000000 : ℝ)] ![(5527238148981/12500000000000 : ℝ), (1265697210593/10000000000000 : ℝ), (1347660083887/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347517149/10000000000 : ℝ)|^1099 ≤ (5527238148981/12500000000000 : ℝ)^843
        have hw : |(5347517149/10000000000 : ℝ)|=(5347517149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2048482453/10000000000 : ℝ)|^1099 ≤ (1265697210593/10000000000000 : ℝ)^843
        have hw : |(-2048482453/10000000000 : ℝ)|=(2048482453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049170089/2000000000 : ℝ)|^1099 ≤ (1347660083887/3125000000000 : ℝ)^843
        have hw : |(1049170089/2000000000 : ℝ)|=(1049170089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s4_2 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336879301/2500000000 : ℝ)*x 0 + (1049170089/2000000000 : ℝ)*x 1 + (-2048482379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336879301/2500000000 : ℝ)^1099 ≤ (5527238223093/12500000000000 : ℝ)^843 := by
    have hnat : (1336879301 : ℕ)^1099*12500000000000^843 ≤ 5527238223093^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336879301 2500000000 5527238223093 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049170089/2000000000 : ℝ)^1099 ≤ (1347660083887/3125000000000 : ℝ)^843 := by
    have hnat : (1049170089 : ℕ)^1099*3125000000000^843 ≤ 1347660083887^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049170089 2000000000 1347660083887 3125000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048482379/10000000000 : ℝ)^1099 ≤ (12656971509857/100000000000000 : ℝ)^843 := by
    have hnat : (2048482379 : ℕ)^1099*100000000000000^843 ≤ 12656971509857^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048482379 10000000000 12656971509857 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336879301/2500000000 : ℝ), (1049170089/2000000000 : ℝ), (-2048482379/10000000000 : ℝ)] ![(5527238223093/12500000000000 : ℝ), (1347660083887/3125000000000 : ℝ), (12656971509857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336879301/2500000000 : ℝ)|^1099 ≤ (5527238223093/12500000000000 : ℝ)^843
        have hw : |(1336879301/2500000000 : ℝ)|=(1336879301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049170089/2000000000 : ℝ)|^1099 ≤ (1347660083887/3125000000000 : ℝ)^843
        have hw : |(1049170089/2000000000 : ℝ)|=(1049170089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2048482379/10000000000 : ℝ)|^1099 ≤ (12656971509857/100000000000000 : ℝ)^843
        have hw : |(-2048482379/10000000000 : ℝ)|=(2048482379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s4_3 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4302536733/10000000000 : ℝ)*x 0 + (1032174819/2500000000 : ℝ)*x 1 + (56036397/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302536733/10000000000 : ℝ)^1099 ≤ (6660779213983/20000000000000 : ℝ)^843 := by
    have hnat : (4302536733 : ℕ)^1099*20000000000000^843 ≤ 6660779213983^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302536733 10000000000 6660779213983 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032174819/2500000000 : ℝ)^1099 ≤ (7890135267057/25000000000000 : ℝ)^843 := by
    have hnat : (1032174819 : ℕ)^1099*25000000000000^843 ≤ 7890135267057^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032174819 2500000000 7890135267057 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56036397/125000000 : ℝ)^1099 ≤ (17567781421011/50000000000000 : ℝ)^843 := by
    have hnat : (56036397 : ℕ)^1099*50000000000000^843 ≤ 17567781421011^843*125000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56036397 125000000 17567781421011 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302536733/10000000000 : ℝ), (1032174819/2500000000 : ℝ), (56036397/125000000 : ℝ)] ![(6660779213983/20000000000000 : ℝ), (7890135267057/25000000000000 : ℝ), (17567781421011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302536733/10000000000 : ℝ)|^1099 ≤ (6660779213983/20000000000000 : ℝ)^843
        have hw : |(4302536733/10000000000 : ℝ)|=(4302536733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032174819/2500000000 : ℝ)|^1099 ≤ (7890135267057/25000000000000 : ℝ)^843
        have hw : |(1032174819/2500000000 : ℝ)|=(1032174819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56036397/125000000 : ℝ)|^1099 ≤ (17567781421011/50000000000000 : ℝ)^843
        have hw : |(56036397/125000000 : ℝ)|=(56036397/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s4_4 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-98266469/500000000 : ℝ)*x 0 + (262322443/500000000 : ℝ)*x 1 + (5408564111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98266469/500000000 : ℝ)^1099 ≤ (11991338701829/100000000000000 : ℝ)^843 := by
    have hnat : (98266469 : ℕ)^1099*100000000000000^843 ≤ 11991338701829^843*500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98266469 500000000 11991338701829 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262322443/500000000 : ℝ)^1099 ≤ (43131536176269/100000000000000 : ℝ)^843 := by
    have hnat : (262322443 : ℕ)^1099*100000000000000^843 ≤ 43131536176269^843*500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262322443 500000000 43131536176269 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408564111/10000000000 : ℝ)^1099 ≤ (897542502079/2000000000000 : ℝ)^843 := by
    have hnat : (5408564111 : ℕ)^1099*2000000000000^843 ≤ 897542502079^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408564111 10000000000 897542502079 2000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98266469/500000000 : ℝ), (262322443/500000000 : ℝ), (5408564111/10000000000 : ℝ)] ![(11991338701829/100000000000000 : ℝ), (43131536176269/100000000000000 : ℝ), (897542502079/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98266469/500000000 : ℝ)|^1099 ≤ (11991338701829/100000000000000 : ℝ)^843
        have hw : |(-98266469/500000000 : ℝ)|=(98266469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262322443/500000000 : ℝ)|^1099 ≤ (43131536176269/100000000000000 : ℝ)^843
        have hw : |(262322443/500000000 : ℝ)|=(262322443/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408564111/10000000000 : ℝ)|^1099 ≤ (897542502079/2000000000000 : ℝ)^843
        have hw : |(5408564111/10000000000 : ℝ)|=(5408564111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s4_5 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (212201237/400000000 : ℝ)*x 0 + (-1885768599/10000000000 : ℝ)*x 1 + (1352141027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212201237/400000000 : ℝ)^1099 ≤ (43760460042883/100000000000000 : ℝ)^843 := by
    have hnat : (212201237 : ℕ)^1099*100000000000000^843 ≤ 43760460042883^843*400000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212201237 400000000 43760460042883 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1885768599/10000000000 : ℝ)^1099 ≤ (2840603716041/25000000000000 : ℝ)^843 := by
    have hnat : (1885768599 : ℕ)^1099*25000000000000^843 ≤ 2840603716041^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885768599 10000000000 2840603716041 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352141027/2500000000 : ℝ)^1099 ≤ (22438562535749/50000000000000 : ℝ)^843 := by
    have hnat : (1352141027 : ℕ)^1099*50000000000000^843 ≤ 22438562535749^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352141027 2500000000 22438562535749 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212201237/400000000 : ℝ), (-1885768599/10000000000 : ℝ), (1352141027/2500000000 : ℝ)] ![(43760460042883/100000000000000 : ℝ), (2840603716041/25000000000000 : ℝ), (22438562535749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212201237/400000000 : ℝ)|^1099 ≤ (43760460042883/100000000000000 : ℝ)^843
        have hw : |(212201237/400000000 : ℝ)|=(212201237/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1885768599/10000000000 : ℝ)|^1099 ≤ (2840603716041/25000000000000 : ℝ)^843
        have hw : |(-1885768599/10000000000 : ℝ)|=(1885768599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352141027/2500000000 : ℝ)|^1099 ≤ (22438562535749/50000000000000 : ℝ)^843
        have hw : |(1352141027/2500000000 : ℝ)|=(1352141027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s4_6 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305030929/10000000000 : ℝ)*x 0 + (5408564087/10000000000 : ℝ)*x 1 + (-942884311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305030929/10000000000 : ℝ)^1099 ≤ (21880230042949/50000000000000 : ℝ)^843 := by
    have hnat : (5305030929 : ℕ)^1099*50000000000000^843 ≤ 21880230042949^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305030929 10000000000 21880230042949 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408564087/10000000000 : ℝ)^1099 ≤ (22438562422169/50000000000000 : ℝ)^843 := by
    have hnat : (5408564087 : ℕ)^1099*50000000000000^843 ≤ 22438562422169^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408564087 10000000000 22438562422169 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (942884311/5000000000 : ℝ)^1099 ≤ (11362415044831/100000000000000 : ℝ)^843 := by
    have hnat : (942884311 : ℕ)^1099*100000000000000^843 ≤ 11362415044831^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942884311 5000000000 11362415044831 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305030929/10000000000 : ℝ), (5408564087/10000000000 : ℝ), (-942884311/5000000000 : ℝ)] ![(21880230042949/50000000000000 : ℝ), (22438562422169/50000000000000 : ℝ), (11362415044831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305030929/10000000000 : ℝ)|^1099 ≤ (21880230042949/50000000000000 : ℝ)^843
        have hw : |(5305030929/10000000000 : ℝ)|=(5305030929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408564087/10000000000 : ℝ)|^1099 ≤ (22438562422169/50000000000000 : ℝ)^843
        have hw : |(5408564087/10000000000 : ℝ)|=(5408564087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-942884311/5000000000 : ℝ)|^1099 ≤ (11362415044831/100000000000000 : ℝ)^843
        have hw : |(-942884311/5000000000 : ℝ)|=(942884311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s4_7 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2151281217/5000000000 : ℝ)*x 0 + (448161349/1000000000 : ℝ)*x 1 + (4130004261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151281217/5000000000 : ℝ)^1099 ≤ (4163019427843/12500000000000 : ℝ)^843 := by
    have hnat : (2151281217 : ℕ)^1099*12500000000000^843 ≤ 4163019427843^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151281217 5000000000 4163019427843 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448161349/1000000000 : ℝ)^1099 ≤ (17561148989571/50000000000000 : ℝ)^843 := by
    have hnat : (448161349 : ℕ)^1099*50000000000000^843 ≤ 17561148989571^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448161349 1000000000 17561148989571 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4130004261/10000000000 : ℝ)^1099 ≤ (15786773293307/50000000000000 : ℝ)^843 := by
    have hnat : (4130004261 : ℕ)^1099*50000000000000^843 ≤ 15786773293307^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130004261 10000000000 15786773293307 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151281217/5000000000 : ℝ), (448161349/1000000000 : ℝ), (4130004261/10000000000 : ℝ)] ![(4163019427843/12500000000000 : ℝ), (17561148989571/50000000000000 : ℝ), (15786773293307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151281217/5000000000 : ℝ)|^1099 ≤ (4163019427843/12500000000000 : ℝ)^843
        have hw : |(2151281217/5000000000 : ℝ)|=(2151281217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448161349/1000000000 : ℝ)|^1099 ≤ (17561148989571/50000000000000 : ℝ)^843
        have hw : |(448161349/1000000000 : ℝ)|=(448161349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4130004261/10000000000 : ℝ)|^1099 ≤ (15786773293307/50000000000000 : ℝ)^843
        have hw : |(4130004261/10000000000 : ℝ)|=(4130004261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1436_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14943/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (354/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3697/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14943/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14943/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14943/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14943/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14943/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14943/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5591/50000 : ℝ) ^ (4395/1024 : ℝ) ≤ (4123092517094923/50000000000000000000 : ℝ) := by
    have hpowers : (5591/50000 : ℝ)^4395 ≤ (4123092517094923/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5591 : ℕ)^4395*50000000000000000000^1024 ≤ 4123092517094923^1024*50000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5591 50000 4123092517094923 50000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5591/50000 : ℝ)) (X := (4123092517094923/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14943/100000 : ℝ) ^ (4395/1024 : ℝ) ≤ (3577696409202957/12500000000000000000 : ℝ) := by
    have hpowers : (14943/100000 : ℝ)^4395 ≤ (3577696409202957/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14943 : ℕ)^4395*12500000000000000000^1024 ≤ 3577696409202957^1024*100000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14943 100000 3577696409202957 12500000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14943/100000 : ℝ)) (X := (3577696409202957/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004123092517094923/25000000000000000000 : ℝ) ≤ (156256003668549/156250000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (25004123092517094923/25000000000000000000 : ℝ)^1024 ≤ (156256003668549/156250000000000 : ℝ)^4395 := by
      have hnat : (25004123092517094923 : ℕ)^1024*156250000000000^4395 ≤ 156256003668549^4395*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004123092517094923 25000000000000000000 156256003668549 156250000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156256003668549/156250000000000 : ℝ)) (X := (25004123092517094923/25000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018433878153906751/50000000000000000000 : ℝ) ≤ (2000171773587287/2000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (50018433878153906751/50000000000000000000 : ℝ)^1024 ≤ (2000171773587287/2000000000000000 : ℝ)^4395 := by
      have hnat : (50018433878153906751 : ℕ)^1024*2000000000000000^4395 ≤ 2000171773587287^4395*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018433878153906751 50000000000000000000 2000171773587287 2000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000171773587287/2000000000000000 : ℝ)) (X := (50018433878153906751/50000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253577696409202957/6250000000000000000 : ℝ) ≤ (5000666750542867/5000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (6253577696409202957/6250000000000000000 : ℝ)^1024 ≤ (5000666750542867/5000000000000000 : ℝ)^4395 := by
      have hnat : (6253577696409202957 : ℕ)^1024*5000000000000000^4395 ≤ 5000666750542867^4395*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253577696409202957 6250000000000000000 5000666750542867 5000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000666750542867/5000000000000000 : ℝ)) (X := (6253577696409202957/6250000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4123092517094923/50000000000000000000 : ℝ) ≤ ((1880041520564174783/1880500000000000000 : ℝ)+2*(474633149299/376100000000000 : ℝ)*(5591/50000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (1880041520564174783/1880500000000000000 : ℝ)+2*(474633149299/376100000000000 : ℝ)*(5591/50000 : ℝ)=(156256003668549/156250000000000 : ℝ) by norm_num, show 1+2*(4123092517094923/50000000000000000000 : ℝ)=(25004123092517094923/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3577696409202957/12500000000000000000 : ℝ)+(4123092517094923/50000000000000000000 : ℝ) ≤ ((1880041520564174783/1880500000000000000 : ℝ)+(474633149299/376100000000000 : ℝ)*((14943/100000 : ℝ)+(5591/50000 : ℝ)))^(4395/1024 : ℝ) := by
    rw [show (1880041520564174783/1880500000000000000 : ℝ)+(474633149299/376100000000000 : ℝ)*((14943/100000 : ℝ)+(5591/50000 : ℝ))=(2000171773587287/2000000000000000 : ℝ) by norm_num, show 1+(3577696409202957/12500000000000000000 : ℝ)+(4123092517094923/50000000000000000000 : ℝ)=(50018433878153906751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3577696409202957/12500000000000000000 : ℝ) ≤ ((1880041520564174783/1880500000000000000 : ℝ)+2*(474633149299/376100000000000 : ℝ)*(14943/100000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (1880041520564174783/1880500000000000000 : ℝ)+2*(474633149299/376100000000000 : ℝ)*(14943/100000 : ℝ)=(5000666750542867/5000000000000000 : ℝ) by norm_num, show 1+2*(3577696409202957/12500000000000000000 : ℝ)=(6253577696409202957/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1880041520564174783/1880500000000000000 : ℝ)*(X 1 0+X 2 0)+(474633149299/376100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (14943/100000 : ℝ)) (c := (1880041520564174783/1880500000000000000 : ℝ)) (alpha := (474633149299/376100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1880041520564174783/1880500000000000000 : ℝ)*(X 0 1+X 2 1)+(474633149299/376100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (14943/100000 : ℝ)) (c := (1880041520564174783/1880500000000000000 : ℝ)) (alpha := (474633149299/376100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1880041520564174783/1880500000000000000 : ℝ)*(X 0 2+X 1 2)+(474633149299/376100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (14943/100000 : ℝ)) (c := (1880041520564174783/1880500000000000000 : ℝ)) (alpha := (474633149299/376100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-982658773/5000000000 : ℝ)*X 0 0+(5409165967/10000000000 : ℝ)*X 0 1+(5245850179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347517149/10000000000 : ℝ)*X 1 0+(-2048482453/10000000000 : ℝ)*X 1 1+(1049170089/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336879301/2500000000 : ℝ)*X 2 0+(1049170089/2000000000 : ℝ)*X 2 1+(-2048482379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302536733/10000000000 : ℝ)*X 0 0+(1032174819/2500000000 : ℝ)*X 0 1+(56036397/125000000 : ℝ)*X 0 2+(4302536733/10000000000 : ℝ)*X 1 0+(1032174819/2500000000 : ℝ)*X 1 1+(56036397/125000000 : ℝ)*X 1 2+(4302536733/10000000000 : ℝ)*X 2 0+(1032174819/2500000000 : ℝ)*X 2 1+(56036397/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98266469/500000000 : ℝ)*X 0 0+(262322443/500000000 : ℝ)*X 0 1+(5408564111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212201237/400000000 : ℝ)*X 1 0+(-1885768599/10000000000 : ℝ)*X 1 1+(1352141027/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305030929/10000000000 : ℝ)*X 2 0+(5408564087/10000000000 : ℝ)*X 2 1+(-942884311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2151281217/5000000000 : ℝ)*X 0 0+(448161349/1000000000 : ℝ)*X 0 1+(4130004261/10000000000 : ℝ)*X 0 2+(2151281217/5000000000 : ℝ)*X 1 0+(448161349/1000000000 : ℝ)*X 1 1+(4130004261/10000000000 : ℝ)*X 1 2+(2151281217/5000000000 : ℝ)*X 2 0+(448161349/1000000000 : ℝ)*X 2 1+(4130004261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (564996802044921334421253681/47012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171549841/10000000000000 : ℝ)*(base19) + (1619390497/100000000000000 : ℝ)*(base23) + (42535723/50000000000000 : ℝ)*(lower2) + (224233969/100000000000000 : ℝ)*(upper3) + (211825421/100000000000000 : ℝ)*(upper5) + (2236599834346469/50000000000000 : ℝ)*(major0) + (2236599834346469/50000000000000 : ℝ)*(major1) + (2236599834346469/50000000000000 : ℝ)*(major2) + (765393837482649/12500000000000 : ℝ)*(sp0) + (1224639067334693/20000000000000 : ℝ)*(sp1) + (3061597716390689/50000000000000 : ℝ)*(sp2) + (1411591214135519/50000000000000 : ℝ)*(sp3) + (46352310683/100000000000000 : ℝ)*(sp4) + (4864085637/25000000000000 : ℝ)*(sp7) + (1411600942306793/50000000000000 : ℝ)*(f.failure) + (391884611339/6400000000 : ℝ)*(f.sum) + (7843858162673/4701250000000000000000000000 : ℝ)*base65 + (931762015956746227/94025000000000000000000000000000 : ℝ)*base67 + (463069714772178773/94025000000000000000000000000000 : ℝ)*base70 + (207272528602228773/94025000000000000000000000000000 : ℝ)*base72 + (27128653330753/18805000000000000000000000000 : ℝ)*base74 + (450460091976778773/94025000000000000000000000000000 : ℝ)*base76 + (369472783235903773/94025000000000000000000000000000 : ℝ)*base78 + (2174077749623596227/94025000000000000000000000000000 : ℝ)*base79 + (8994817190321/2350625000000000000000000000 : ℝ)*base82 + (13757393/5000000000000000000000 : ℝ)*base89 + (13757393/5000000000000000000000 : ℝ)*base91 + (13757393/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69964763880318917374713/9402500000000000000000000000 : ℝ) := by norm_num
    linear_combination (313843153/25000000000000 : ℝ)*(base19) + (1398923089/100000000000000 : ℝ)*(base23) + (78602049/50000000000000 : ℝ)*(upper3) + (32465433/50000000000000 : ℝ)*(lower4) + (14722827/10000000000000 : ℝ)*(upper5) + (281641114305269/6250000000000 : ℝ)*(major0) + (281641114305269/6250000000000 : ℝ)*(major1) + (281641114305269/6250000000000 : ℝ)*(major2) + (12824419479/50000000000000 : ℝ)*(sp1) + (2770964519/10000000000000 : ℝ)*(sp2) + (3084224648293799/50000000000000 : ℝ)*(sp4) + (6168422392376029/100000000000000 : ℝ)*(sp5) + (6168420188019319/100000000000000 : ℝ)*(sp6) + (284406611314497/10000000000000 : ℝ)*(sp7) + (284406611314497/10000000000000 : ℝ)*(f.failure) + (3084224648293799/50000000000000 : ℝ)*(f.sum) + (31489345763049/4701250000000000000000000000 : ℝ)*base65 + (2762030914799127/11753125000000000000000000000000 : ℝ)*base67 + (45450215762774127/11753125000000000000000000000000 : ℝ)*base69 + (18959092262381813/2938281250000000000000000000000 : ℝ)*base71 + (37981947509121/18805000000000000000000000000 : ℝ)*base73 + (43122604326925873/11753125000000000000000000000000 : ℝ)*base76 + (24784212975105687/2938281250000000000000000000000 : ℝ)*base78 + (33810696751380687/2938281250000000000000000000000 : ℝ)*base80 + (57068524472293/9402500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3118103/1000000000000000000000 : ℝ)*base90 + (3118103/1000000000000000000000 : ℝ)*base92 + (3118103/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1436_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14943/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3697/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1436_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1436_s5_0 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1965445941/10000000000 : ℝ)*x 0 + (27040147/50000000 : ℝ)*x 1 + (5246902013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1965445941/10000000000 : ℝ)^1099 ≤ (5996132936177/50000000000000 : ℝ)^843 := by
    have hnat : (1965445941 : ℕ)^1099*50000000000000^843 ≤ 5996132936177^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965445941 10000000000 5996132936177 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27040147/50000000 : ℝ)^1099 ≤ (44871341137539/100000000000000 : ℝ)^843 := by
    have hnat : (27040147 : ℕ)^1099*100000000000000^843 ≤ 44871341137539^843*50000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27040147 50000000 44871341137539 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246902013/10000000000 : ℝ)^1099 ≤ (21568196487773/50000000000000 : ℝ)^843 := by
    have hnat : (5246902013 : ℕ)^1099*50000000000000^843 ≤ 21568196487773^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246902013 10000000000 21568196487773 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1965445941/10000000000 : ℝ), (27040147/50000000 : ℝ), (5246902013/10000000000 : ℝ)] ![(5996132936177/50000000000000 : ℝ), (44871341137539/100000000000000 : ℝ), (21568196487773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1965445941/10000000000 : ℝ)|^1099 ≤ (5996132936177/50000000000000 : ℝ)^843
        have hw : |(-1965445941/10000000000 : ℝ)|=(1965445941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27040147/50000000 : ℝ)|^1099 ≤ (44871341137539/100000000000000 : ℝ)^843
        have hw : |(27040147/50000000 : ℝ)|=(27040147/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246902013/10000000000 : ℝ)|^1099 ≤ (21568196487773/50000000000000 : ℝ)^843
        have hw : |(5246902013/10000000000 : ℝ)|=(5246902013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s5_1 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347223179/10000000000 : ℝ)*x 0 + (-204747663/1000000000 : ℝ)*x 1 + (5246902013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347223179/10000000000 : ℝ)^1099 ≤ (8842947248229/20000000000000 : ℝ)^843 := by
    have hnat : (5347223179 : ℕ)^1099*20000000000000^843 ≤ 8842947248229^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347223179 10000000000 8842947248229 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204747663/1000000000 : ℝ)^1099 ≤ (12648870765699/100000000000000 : ℝ)^843 := by
    have hnat : (204747663 : ℕ)^1099*100000000000000^843 ≤ 12648870765699^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204747663 1000000000 12648870765699 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246902013/10000000000 : ℝ)^1099 ≤ (21568196487773/50000000000000 : ℝ)^843 := by
    have hnat : (5246902013 : ℕ)^1099*50000000000000^843 ≤ 21568196487773^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246902013 10000000000 21568196487773 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347223179/10000000000 : ℝ), (-204747663/1000000000 : ℝ), (5246902013/10000000000 : ℝ)] ![(8842947248229/20000000000000 : ℝ), (12648870765699/100000000000000 : ℝ), (21568196487773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347223179/10000000000 : ℝ)|^1099 ≤ (8842947248229/20000000000000 : ℝ)^843
        have hw : |(5347223179/10000000000 : ℝ)|=(5347223179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204747663/1000000000 : ℝ)|^1099 ≤ (12648870765699/100000000000000 : ℝ)^843
        have hw : |(-204747663/1000000000 : ℝ)|=(204747663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246902013/10000000000 : ℝ)|^1099 ≤ (21568196487773/50000000000000 : ℝ)^843
        have hw : |(5246902013/10000000000 : ℝ)|=(5246902013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s5_2 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347223179/10000000000 : ℝ)*x 0 + (5246902013/10000000000 : ℝ)*x 1 + (-204747663/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347223179/10000000000 : ℝ)^1099 ≤ (8842947248229/20000000000000 : ℝ)^843 := by
    have hnat : (5347223179 : ℕ)^1099*20000000000000^843 ≤ 8842947248229^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347223179 10000000000 8842947248229 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246902013/10000000000 : ℝ)^1099 ≤ (21568196487773/50000000000000 : ℝ)^843 := by
    have hnat : (5246902013 : ℕ)^1099*50000000000000^843 ≤ 21568196487773^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246902013 10000000000 21568196487773 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204747663/1000000000 : ℝ)^1099 ≤ (12648870765699/100000000000000 : ℝ)^843 := by
    have hnat : (204747663 : ℕ)^1099*100000000000000^843 ≤ 12648870765699^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204747663 1000000000 12648870765699 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347223179/10000000000 : ℝ), (5246902013/10000000000 : ℝ), (-204747663/1000000000 : ℝ)] ![(8842947248229/20000000000000 : ℝ), (21568196487773/50000000000000 : ℝ), (12648870765699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347223179/10000000000 : ℝ)|^1099 ≤ (8842947248229/20000000000000 : ℝ)^843
        have hw : |(5347223179/10000000000 : ℝ)|=(5347223179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246902013/10000000000 : ℝ)|^1099 ≤ (21568196487773/50000000000000 : ℝ)^843
        have hw : |(5246902013/10000000000 : ℝ)|=(5246902013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-204747663/1000000000 : ℝ)|^1099 ≤ (12648870765699/100000000000000 : ℝ)^843
        have hw : |(-204747663/1000000000 : ℝ)|=(204747663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s5_3 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1344567/3125000 : ℝ)*x 0 + (1032765709/2500000000 : ℝ)*x 1 + (89610589/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344567/3125000 : ℝ)^1099 ≤ (33304679821251/100000000000000 : ℝ)^843 := by
    have hnat : (1344567 : ℕ)^1099*100000000000000^843 ≤ 33304679821251^843*3125000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344567 3125000 33304679821251 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032765709/2500000000 : ℝ)^1099 ≤ (15792048646289/50000000000000 : ℝ)^843 := by
    have hnat : (1032765709 : ℕ)^1099*50000000000000^843 ≤ 15792048646289^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032765709 2500000000 15792048646289 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89610589/200000000 : ℝ)^1099 ≤ (35111222870429/100000000000000 : ℝ)^843 := by
    have hnat : (89610589 : ℕ)^1099*100000000000000^843 ≤ 35111222870429^843*200000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89610589 200000000 35111222870429 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344567/3125000 : ℝ), (1032765709/2500000000 : ℝ), (89610589/200000000 : ℝ)] ![(33304679821251/100000000000000 : ℝ), (15792048646289/50000000000000 : ℝ), (35111222870429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344567/3125000 : ℝ)|^1099 ≤ (33304679821251/100000000000000 : ℝ)^843
        have hw : |(1344567/3125000 : ℝ)|=(1344567/3125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032765709/2500000000 : ℝ)|^1099 ≤ (15792048646289/50000000000000 : ℝ)^843
        have hw : |(1032765709/2500000000 : ℝ)|=(1032765709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89610589/200000000 : ℝ)|^1099 ≤ (35111222870429/100000000000000 : ℝ)^843
        have hw : |(89610589/200000000 : ℝ)|=(89610589/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s5_4 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-491364813/2500000000 : ℝ)*x 0 + (655935281/1250000000 : ℝ)*x 1 + (2703722331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491364813/2500000000 : ℝ)^1099 ≤ (11992371754173/100000000000000 : ℝ)^843 := by
    have hnat : (491364813 : ℕ)^1099*100000000000000^843 ≤ 11992371754173^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491364813 2500000000 11992371754173 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655935281/1250000000 : ℝ)^1099 ≤ (43142611999151/100000000000000 : ℝ)^843 := by
    have hnat : (655935281 : ℕ)^1099*100000000000000^843 ≤ 43142611999151^843*1250000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655935281 1250000000 43142611999151 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703722331/5000000000 : ℝ)^1099 ≤ (44865016228097/100000000000000 : ℝ)^843 := by
    have hnat : (2703722331 : ℕ)^1099*100000000000000^843 ≤ 44865016228097^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703722331 5000000000 44865016228097 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-491364813/2500000000 : ℝ), (655935281/1250000000 : ℝ), (2703722331/5000000000 : ℝ)] ![(11992371754173/100000000000000 : ℝ), (43142611999151/100000000000000 : ℝ), (44865016228097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-491364813/2500000000 : ℝ)|^1099 ≤ (11992371754173/100000000000000 : ℝ)^843
        have hw : |(-491364813/2500000000 : ℝ)|=(491364813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655935281/1250000000 : ℝ)|^1099 ≤ (43142611999151/100000000000000 : ℝ)^843
        have hw : |(655935281/1250000000 : ℝ)|=(655935281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703722331/5000000000 : ℝ)|^1099 ≤ (44865016228097/100000000000000 : ℝ)^843
        have hw : |(2703722331/5000000000 : ℝ)|=(2703722331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s5_5 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326325921/2500000000 : ℝ)*x 0 + (-1886936319/10000000000 : ℝ)*x 1 + (5407444863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326325921/2500000000 : ℝ)^1099 ≤ (8752678655169/20000000000000 : ℝ)^843 := by
    have hnat : (1326325921 : ℕ)^1099*20000000000000^843 ≤ 8752678655169^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326325921 2500000000 8752678655169 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1886936319/10000000000 : ℝ)^1099 ≤ (11371588297401/100000000000000 : ℝ)^843 := by
    have hnat : (1886936319 : ℕ)^1099*100000000000000^843 ≤ 11371588297401^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886936319 10000000000 11371588297401 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407444863/10000000000 : ℝ)^1099 ≤ (44865018402209/100000000000000 : ℝ)^843 := by
    have hnat : (5407444863 : ℕ)^1099*100000000000000^843 ≤ 44865018402209^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407444863 10000000000 44865018402209 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326325921/2500000000 : ℝ), (-1886936319/10000000000 : ℝ), (5407444863/10000000000 : ℝ)] ![(8752678655169/20000000000000 : ℝ), (11371588297401/100000000000000 : ℝ), (44865018402209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326325921/2500000000 : ℝ)|^1099 ≤ (8752678655169/20000000000000 : ℝ)^843
        have hw : |(1326325921/2500000000 : ℝ)|=(1326325921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1886936319/10000000000 : ℝ)|^1099 ≤ (11371588297401/100000000000000 : ℝ)^843
        have hw : |(-1886936319/10000000000 : ℝ)|=(1886936319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407444863/10000000000 : ℝ)|^1099 ≤ (44865018402209/100000000000000 : ℝ)^843
        have hw : |(5407444863/10000000000 : ℝ)|=(5407444863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s5_6 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061061399/2000000000 : ℝ)*x 0 + (1351860689/2500000000 : ℝ)*x 1 + (-188693469/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061061399/2000000000 : ℝ)^1099 ≤ (4376342888241/10000000000000 : ℝ)^843 := by
    have hnat : (1061061399 : ℕ)^1099*10000000000000^843 ≤ 4376342888241^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061061399 2000000000 4376342888241 10000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351860689/2500000000 : ℝ)^1099 ≤ (44864995611891/100000000000000 : ℝ)^843 := by
    have hnat : (1351860689 : ℕ)^1099*100000000000000^843 ≤ 44864995611891^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351860689 2500000000 44864995611891 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188693469/1000000000 : ℝ)^1099 ≤ (568578774951/5000000000000 : ℝ)^843 := by
    have hnat : (188693469 : ℕ)^1099*5000000000000^843 ≤ 568578774951^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188693469 1000000000 568578774951 5000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061061399/2000000000 : ℝ), (1351860689/2500000000 : ℝ), (-188693469/1000000000 : ℝ)] ![(4376342888241/10000000000000 : ℝ), (44864995611891/100000000000000 : ℝ), (568578774951/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061061399/2000000000 : ℝ)|^1099 ≤ (4376342888241/10000000000000 : ℝ)^843
        have hw : |(1061061399/2000000000 : ℝ)|=(1061061399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351860689/2500000000 : ℝ)|^1099 ≤ (44864995611891/100000000000000 : ℝ)^843
        have hw : |(1351860689/2500000000 : ℝ)|=(1351860689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188693469/1000000000 : ℝ)|^1099 ≤ (568578774951/5000000000000 : ℝ)^843
        have hw : |(-188693469/1000000000 : ℝ)|=(188693469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s5_7 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4302639549/10000000000 : ℝ)*x 0 + (1119816229/2500000000 : ℝ)*x 1 + (2066166683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302639549/10000000000 : ℝ)^1099 ≤ (33304933605147/100000000000000 : ℝ)^843 := by
    have hnat : (4302639549 : ℕ)^1099*100000000000000^843 ≤ 33304933605147^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302639549 10000000000 33304933605147 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119816229/2500000000 : ℝ)^1099 ≤ (8774576192657/25000000000000 : ℝ)^843 := by
    have hnat : (1119816229 : ℕ)^1099*25000000000000^843 ≤ 8774576192657^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119816229 2500000000 8774576192657 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066166683/5000000000 : ℝ)^1099 ≤ (31596761615881/100000000000000 : ℝ)^843 := by
    have hnat : (2066166683 : ℕ)^1099*100000000000000^843 ≤ 31596761615881^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066166683 5000000000 31596761615881 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302639549/10000000000 : ℝ), (1119816229/2500000000 : ℝ), (2066166683/5000000000 : ℝ)] ![(33304933605147/100000000000000 : ℝ), (8774576192657/25000000000000 : ℝ), (31596761615881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302639549/10000000000 : ℝ)|^1099 ≤ (33304933605147/100000000000000 : ℝ)^843
        have hw : |(4302639549/10000000000 : ℝ)|=(4302639549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119816229/2500000000 : ℝ)|^1099 ≤ (8774576192657/25000000000000 : ℝ)^843
        have hw : |(1119816229/2500000000 : ℝ)|=(1119816229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066166683/5000000000 : ℝ)|^1099 ≤ (31596761615881/100000000000000 : ℝ)^843
        have hw : |(2066166683/5000000000 : ℝ)|=(2066166683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1436_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3697/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11351/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3691/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3697/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3697/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3697/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3697/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3697/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3697/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (354/3125 : ℝ) ^ (4395/1024 : ℝ) ≤ (1743665170490499/20000000000000000000 : ℝ) := by
    have hpowers : (354/3125 : ℝ)^4395 ≤ (1743665170490499/20000000000000000000 : ℝ)^1024 := by
      have hnat : (354 : ℕ)^4395*20000000000000000000^1024 ≤ 1743665170490499^1024*3125^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        354 3125 1743665170490499 20000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (354/3125 : ℝ)) (X := (1743665170490499/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3697/25000 : ℝ) ^ (4395/1024 : ℝ) ≤ (27368929427028377/100000000000000000000 : ℝ) := by
    have hpowers : (3697/25000 : ℝ)^4395 ≤ (27368929427028377/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3697 : ℕ)^4395*100000000000000000000^1024 ≤ 27368929427028377^1024*25000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3697 25000 27368929427028377 100000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3697/25000 : ℝ)) (X := (27368929427028377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001743665170490499/10000000000000000000 : ℝ) ≤ (2000081246586991/2000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (10001743665170490499/10000000000000000000 : ℝ)^1024 ≤ (2000081246586991/2000000000000000 : ℝ)^4395 := by
      have hnat : (10001743665170490499 : ℕ)^1024*2000000000000000^4395 ≤ 2000081246586991^4395*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001743665170490499 10000000000000000000 2000081246586991 2000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000081246586991/2000000000000000 : ℝ)) (X := (10001743665170490499/10000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504510906909935109/12500000000000000000 : ℝ) ≤ (10000840687970307/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (12504510906909935109/12500000000000000000 : ℝ)^1024 ≤ (10000840687970307/10000000000000000 : ℝ)^4395 := by
      have hnat : (12504510906909935109 : ℕ)^1024*10000000000000000^4395 ≤ 10000840687970307^4395*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504510906909935109 12500000000000000000 10000840687970307 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000840687970307/10000000000000000 : ℝ)) (X := (12504510906909935109/12500000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027368929427028377/50000000000000000000 : ℝ) ≤ (10001275143005659/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (50027368929427028377/50000000000000000000 : ℝ)^1024 ≤ (10001275143005659/10000000000000000 : ℝ)^4395 := by
      have hnat : (50027368929427028377 : ℕ)^1024*10000000000000000^4395 ≤ 10001275143005659^4395*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027368929427028377 50000000000000000000 10001275143005659 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001275143005659/10000000000000000 : ℝ)) (X := (50027368929427028377/50000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1743665170490499/20000000000000000000 : ℝ) ≤ ((8647890638168502347/8650000000000000000 : ℝ)+2*(54306879419/43250000000000 : ℝ)*(354/3125 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (8647890638168502347/8650000000000000000 : ℝ)+2*(54306879419/43250000000000 : ℝ)*(354/3125 : ℝ)=(2000081246586991/2000000000000000 : ℝ) by norm_num, show 1+2*(1743665170490499/20000000000000000000 : ℝ)=(10001743665170490499/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27368929427028377/100000000000000000000 : ℝ)+(1743665170490499/20000000000000000000 : ℝ) ≤ ((8647890638168502347/8650000000000000000 : ℝ)+(54306879419/43250000000000 : ℝ)*((3697/25000 : ℝ)+(354/3125 : ℝ)))^(4395/1024 : ℝ) := by
    rw [show (8647890638168502347/8650000000000000000 : ℝ)+(54306879419/43250000000000 : ℝ)*((3697/25000 : ℝ)+(354/3125 : ℝ))=(10000840687970307/10000000000000000 : ℝ) by norm_num, show 1+(27368929427028377/100000000000000000000 : ℝ)+(1743665170490499/20000000000000000000 : ℝ)=(12504510906909935109/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27368929427028377/100000000000000000000 : ℝ) ≤ ((8647890638168502347/8650000000000000000 : ℝ)+2*(54306879419/43250000000000 : ℝ)*(3697/25000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (8647890638168502347/8650000000000000000 : ℝ)+2*(54306879419/43250000000000 : ℝ)*(3697/25000 : ℝ)=(10001275143005659/10000000000000000 : ℝ) by norm_num, show 1+2*(27368929427028377/100000000000000000000 : ℝ)=(50027368929427028377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8647890638168502347/8650000000000000000 : ℝ)*(X 1 0+X 2 0)+(54306879419/43250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (3697/25000 : ℝ)) (c := (8647890638168502347/8650000000000000000 : ℝ)) (alpha := (54306879419/43250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8647890638168502347/8650000000000000000 : ℝ)*(X 0 1+X 2 1)+(54306879419/43250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (3697/25000 : ℝ)) (c := (8647890638168502347/8650000000000000000 : ℝ)) (alpha := (54306879419/43250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8647890638168502347/8650000000000000000 : ℝ)*(X 0 2+X 1 2)+(54306879419/43250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (3697/25000 : ℝ)) (c := (8647890638168502347/8650000000000000000 : ℝ)) (alpha := (54306879419/43250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1965445941/10000000000 : ℝ)*X 0 0+(27040147/50000000 : ℝ)*X 0 1+(5246902013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347223179/10000000000 : ℝ)*X 1 0+(-204747663/1000000000 : ℝ)*X 1 1+(5246902013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347223179/10000000000 : ℝ)*X 2 0+(5246902013/10000000000 : ℝ)*X 2 1+(-204747663/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1344567/3125000 : ℝ)*X 0 0+(1032765709/2500000000 : ℝ)*X 0 1+(89610589/200000000 : ℝ)*X 0 2+(1344567/3125000 : ℝ)*X 1 0+(1032765709/2500000000 : ℝ)*X 1 1+(89610589/200000000 : ℝ)*X 1 2+(1344567/3125000 : ℝ)*X 2 0+(1032765709/2500000000 : ℝ)*X 2 1+(89610589/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-491364813/2500000000 : ℝ)*X 0 0+(655935281/1250000000 : ℝ)*X 0 1+(2703722331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326325921/2500000000 : ℝ)*X 1 0+(-1886936319/10000000000 : ℝ)*X 1 1+(5407444863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061061399/2000000000 : ℝ)*X 2 0+(1351860689/2500000000 : ℝ)*X 2 1+(-188693469/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302639549/10000000000 : ℝ)*X 0 0+(1119816229/2500000000 : ℝ)*X 0 1+(2066166683/5000000000 : ℝ)*X 0 2+(4302639549/10000000000 : ℝ)*X 1 0+(1119816229/2500000000 : ℝ)*X 1 1+(2066166683/5000000000 : ℝ)*X 1 2+(4302639549/10000000000 : ℝ)*X 2 0+(1119816229/2500000000 : ℝ)*X 2 1+(2066166683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24170153244263649789483/4325000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1985777/195312500000 : ℝ)*(base19) + (947288127/100000000000000 : ℝ)*(base23) + (37125609/100000000000000 : ℝ)*(lower2) + (139521271/100000000000000 : ℝ)*(upper3) + (89046461/100000000000000 : ℝ)*(upper5) + (2266959360077839/50000000000000 : ℝ)*(major0) + (2266959360077839/50000000000000 : ℝ)*(major1) + (2266959360077839/50000000000000 : ℝ)*(major2) + (620629191774447/10000000000000 : ℝ)*(sp0) + (6206312311827841/100000000000000 : ℝ)*(sp1) + (3103156190628769/50000000000000 : ℝ)*(sp2) + (715378310588691/25000000000000 : ℝ)*(sp3) + (5352700299/25000000000000 : ℝ)*(sp4) + (10683128427/100000000000000 : ℝ)*(sp7) + (2861523925483191/100000000000000 : ℝ)*(f.failure) + (1241262665709133/20000000000000 : ℝ)*(f.sum) + (18426176145839/4325000000000000000000000000 : ℝ)*base65 + (3767873236947611867/432500000000000000000000000000000 : ℝ)*base68 + (1816400583197611867/432500000000000000000000000000000 : ℝ)*base70 + (1552835564517388133/432500000000000000000000000000000 : ℝ)*base71 + (10544944896893/2162500000000000000000000000 : ℝ)*base74 + (4179645311094888133/432500000000000000000000000000000 : ℝ)*base75 + (3668043089519888133/432500000000000000000000000000000 : ℝ)*base77 + (605881906392611867/432500000000000000000000000000000 : ℝ)*base80 + (920205959007/2162500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (63074609/10000000000000000000000 : ℝ)*base90 + (63074609/10000000000000000000000 : ℝ)*base92 + (63074609/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48545000860883743826105073/54062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4005879307/100000000000000 : ℝ)*(base23) + (493391039/100000000000000 : ℝ)*(upper2) + (143181827/25000000000000 : ℝ)*(upper4) + (749211877/50000000000000 : ℝ)*(upper5) + (1141751310420953/25000000000000 : ℝ)*(major0) + (1141751310420953/25000000000000 : ℝ)*(major1) + (1141751310420953/25000000000000 : ℝ)*(major2) + (10610244877/50000000000000 : ℝ)*(sp0) + (14523742789/50000000000000 : ℝ)*(sp1) + (15294664947/25000000000000 : ℝ)*(sp2) + (3125791589521231/50000000000000 : ℝ)*(sp4) + (3125787676023319/50000000000000 : ℝ)*(sp5) + (39072120093707/625000000000 : ℝ)*(sp6) + (1441203026951997/50000000000000 : ℝ)*(sp7) + (1441203026951997/50000000000000 : ℝ)*(f.failure) + (1250320879906443/20000000000000 : ℝ)*(f.sum) + (2953759160433/135156250000000000000000000 : ℝ)*base65 + (787257073650123309/216250000000000000000000000000000 : ℝ)*base68 + (1502118973912623309/216250000000000000000000000000000 : ℝ)*base70 + (53570318950123309/216250000000000000000000000000000 : ℝ)*base72 + (4103715780597/2162500000000000000000000000 : ℝ)*base74 + (2035062008820123309/216250000000000000000000000000000 : ℝ)*base76 + (575571515482376691/216250000000000000000000000000000 : ℝ)*base77 + (921161190305123309/216250000000000000000000000000000 : ℝ)*base80 + (2442610527211/1081250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (30019397/5000000000000000000000 : ℝ)*base89 + (30019397/5000000000000000000000 : ℝ)*base91 + (30019397/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1436_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3697/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1436_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1436_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7889/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1436_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1436_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1436_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7889/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1436_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
