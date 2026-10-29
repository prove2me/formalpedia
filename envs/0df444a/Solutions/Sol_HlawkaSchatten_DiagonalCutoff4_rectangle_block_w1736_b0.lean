-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1736_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:08:02.693991+00:00
-- url     : https://prove2.me/submissions/bf57db8e-54ef-427d-872c-efc512e91e34

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
theorem support_rectangle_w1736_s0_0 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1247463061/10000000000 : ℝ)*x 0 + (2838151227/5000000000 : ℝ)*x 1 + (2477416851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1247463061/10000000000 : ℝ)^5551 ≤ (7790236396119/100000000000000 : ℝ)^4527 := by
    have hnat : (1247463061 : ℕ)^5551*100000000000000^4527 ≤ 7790236396119^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247463061 10000000000 7790236396119 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2838151227/5000000000 : ℝ)^5551 ≤ (4993850682413/10000000000000 : ℝ)^4527 := by
    have hnat : (2838151227 : ℕ)^5551*10000000000000^4527 ≤ 4993850682413^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838151227 5000000000 4993850682413 10000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2477416851/5000000000 : ℝ)^5551 ≤ (21135628382469/50000000000000 : ℝ)^4527 := by
    have hnat : (2477416851 : ℕ)^5551*50000000000000^4527 ≤ 21135628382469^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2477416851 5000000000 21135628382469 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1247463061/10000000000 : ℝ), (2838151227/5000000000 : ℝ), (2477416851/5000000000 : ℝ)] ![(7790236396119/100000000000000 : ℝ), (4993850682413/10000000000000 : ℝ), (21135628382469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1247463061/10000000000 : ℝ)|^5551 ≤ (7790236396119/100000000000000 : ℝ)^4527
        have hw : |(-1247463061/10000000000 : ℝ)|=(1247463061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2838151227/5000000000 : ℝ)|^5551 ≤ (4993850682413/10000000000000 : ℝ)^4527
        have hw : |(2838151227/5000000000 : ℝ)|=(2838151227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2477416851/5000000000 : ℝ)|^5551 ≤ (21135628382469/50000000000000 : ℝ)^4527
        have hw : |(2477416851/5000000000 : ℝ)|=(2477416851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s0_1 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5262491/9765625 : ℝ)*x 0 + (-818676533/5000000000 : ℝ)*x 1 + (4954833913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262491/9765625 : ℝ)^5551 ≤ (2342745450657/5000000000000 : ℝ)^4527 := by
    have hnat : (5262491 : ℕ)^5551*5000000000000^4527 ≤ 2342745450657^4527*9765625^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262491 9765625 2342745450657 5000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (818676533/5000000000 : ℝ)^5551 ≤ (33980724983/312500000000 : ℝ)^4527 := by
    have hnat : (818676533 : ℕ)^5551*312500000000^4527 ≤ 33980724983^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818676533 5000000000 33980724983 312500000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4954833913/10000000000 : ℝ)^5551 ≤ (42271258972227/100000000000000 : ℝ)^4527 := by
    have hnat : (4954833913 : ℕ)^5551*100000000000000^4527 ≤ 42271258972227^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4954833913 10000000000 42271258972227 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262491/9765625 : ℝ), (-818676533/5000000000 : ℝ), (4954833913/10000000000 : ℝ)] ![(2342745450657/5000000000000 : ℝ), (33980724983/312500000000 : ℝ), (42271258972227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262491/9765625 : ℝ)|^5551 ≤ (2342745450657/5000000000000 : ℝ)^4527
        have hw : |(5262491/9765625 : ℝ)|=(5262491/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-818676533/5000000000 : ℝ)|^5551 ≤ (33980724983/312500000000 : ℝ)^4527
        have hw : |(-818676533/5000000000 : ℝ)|=(818676533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4954833913/10000000000 : ℝ)|^5551 ≤ (42271258972227/100000000000000 : ℝ)^4527
        have hw : |(4954833913/10000000000 : ℝ)|=(4954833913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s0_2 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388790227/10000000000 : ℝ)*x 0 + (4954834371/10000000000 : ℝ)*x 1 + (-1637353209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388790227/10000000000 : ℝ)^5551 ≤ (234274515373/500000000000 : ℝ)^4527 := by
    have hnat : (5388790227 : ℕ)^5551*500000000000^4527 ≤ 234274515373^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388790227 10000000000 234274515373 500000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4954834371/10000000000 : ℝ)^5551 ≤ (8454252752681/20000000000000 : ℝ)^4527 := by
    have hnat : (4954834371 : ℕ)^5551*20000000000000^4527 ≤ 8454252752681^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4954834371 10000000000 8454252752681 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1637353209/10000000000 : ℝ)^5551 ≤ (10873833159053/100000000000000 : ℝ)^4527 := by
    have hnat : (1637353209 : ℕ)^5551*100000000000000^4527 ≤ 10873833159053^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1637353209 10000000000 10873833159053 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388790227/10000000000 : ℝ), (4954834371/10000000000 : ℝ), (-1637353209/10000000000 : ℝ)] ![(234274515373/500000000000 : ℝ), (8454252752681/20000000000000 : ℝ), (10873833159053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388790227/10000000000 : ℝ)|^5551 ≤ (234274515373/500000000000 : ℝ)^4527
        have hw : |(5388790227/10000000000 : ℝ)|=(5388790227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4954834371/10000000000 : ℝ)|^5551 ≤ (8454252752681/20000000000000 : ℝ)^4527
        have hw : |(4954834371/10000000000 : ℝ)|=(4954834371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1637353209/10000000000 : ℝ)|^5551 ≤ (10873833159053/100000000000000 : ℝ)^4527
        have hw : |(-1637353209/10000000000 : ℝ)|=(1637353209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s0_3 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (9996649/25000000 : ℝ)*x 0 + (742823889/2500000000 : ℝ)*x 1 + (5206697309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9996649/25000000 : ℝ)^5551 ≤ (8124715070159/25000000000000 : ℝ)^4527 := by
    have hnat : (9996649 : ℕ)^5551*25000000000000^4527 ≤ 8124715070159^4527*25000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9996649 25000000 8124715070159 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (742823889/2500000000 : ℝ)^5551 ≤ (4516032541077/20000000000000 : ℝ)^4527 := by
    have hnat : (742823889 : ℕ)^5551*20000000000000^4527 ≤ 4516032541077^4527*2500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742823889 2500000000 4516032541077 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206697309/10000000000 : ℝ)^5551 ≤ (22460488498053/50000000000000 : ℝ)^4527 := by
    have hnat : (5206697309 : ℕ)^5551*50000000000000^4527 ≤ 22460488498053^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206697309 10000000000 22460488498053 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9996649/25000000 : ℝ), (742823889/2500000000 : ℝ), (5206697309/10000000000 : ℝ)] ![(8124715070159/25000000000000 : ℝ), (4516032541077/20000000000000 : ℝ), (22460488498053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9996649/25000000 : ℝ)|^5551 ≤ (8124715070159/25000000000000 : ℝ)^4527
        have hw : |(9996649/25000000 : ℝ)|=(9996649/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(742823889/2500000000 : ℝ)|^5551 ≤ (4516032541077/20000000000000 : ℝ)^4527
        have hw : |(742823889/2500000000 : ℝ)|=(742823889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206697309/10000000000 : ℝ)|^5551 ≤ (22460488498053/50000000000000 : ℝ)^4527
        have hw : |(5206697309/10000000000 : ℝ)|=(5206697309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s0_4 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-624581713/5000000000 : ℝ)*x 0 + (2486814403/5000000000 : ℝ)*x 1 + (1414213493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (624581713/5000000000 : ℝ)^5551 ≤ (7803258847793/100000000000000 : ℝ)^4527 := by
    have hnat : (624581713 : ℕ)^5551*100000000000000^4527 ≤ 7803258847793^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624581713 5000000000 7803258847793 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2486814403/5000000000 : ℝ)^5551 ≤ (42467958251089/100000000000000 : ℝ)^4527 := by
    have hnat : (2486814403 : ℕ)^5551*100000000000000^4527 ≤ 42467958251089^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486814403 5000000000 42467958251089 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414213493/2500000000 : ℝ)^5551 ≤ (9945756578299/20000000000000 : ℝ)^4527 := by
    have hnat : (1414213493 : ℕ)^5551*20000000000000^4527 ≤ 9945756578299^4527*2500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414213493 2500000000 9945756578299 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-624581713/5000000000 : ℝ), (2486814403/5000000000 : ℝ), (1414213493/2500000000 : ℝ)] ![(7803258847793/100000000000000 : ℝ), (42467958251089/100000000000000 : ℝ), (9945756578299/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-624581713/5000000000 : ℝ)|^5551 ≤ (7803258847793/100000000000000 : ℝ)^4527
        have hw : |(-624581713/5000000000 : ℝ)|=(624581713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2486814403/5000000000 : ℝ)|^5551 ≤ (42467958251089/100000000000000 : ℝ)^4527
        have hw : |(2486814403/5000000000 : ℝ)|=(2486814403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414213493/2500000000 : ℝ)|^5551 ≤ (9945756578299/20000000000000 : ℝ)^4527
        have hw : |(1414213493/2500000000 : ℝ)|=(1414213493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s0_5 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597560299/5000000000 : ℝ)*x 0 + (-37413327/400000000 : ℝ)*x 1 + (5656853341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597560299/5000000000 : ℝ)^5551 ≤ (22399268472867/50000000000000 : ℝ)^4527 := by
    have hnat : (2597560299 : ℕ)^5551*50000000000000^4527 ≤ 22399268472867^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597560299 5000000000 22399268472867 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37413327/400000000 : ℝ)^5551 ≤ (2736343475491/50000000000000 : ℝ)^4527 := by
    have hnat : (37413327 : ℕ)^5551*50000000000000^4527 ≤ 2736343475491^4527*400000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37413327 400000000 2736343475491 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5656853341/10000000000 : ℝ)^5551 ≤ (49728776089709/100000000000000 : ℝ)^4527 := by
    have hnat : (5656853341 : ℕ)^5551*100000000000000^4527 ≤ 49728776089709^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5656853341 10000000000 49728776089709 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597560299/5000000000 : ℝ), (-37413327/400000000 : ℝ), (5656853341/10000000000 : ℝ)] ![(22399268472867/50000000000000 : ℝ), (2736343475491/50000000000000 : ℝ), (49728776089709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597560299/5000000000 : ℝ)|^5551 ≤ (22399268472867/50000000000000 : ℝ)^4527
        have hw : |(2597560299/5000000000 : ℝ)|=(2597560299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37413327/400000000 : ℝ)|^5551 ≤ (2736343475491/50000000000000 : ℝ)^4527
        have hw : |(-37413327/400000000 : ℝ)|=(37413327/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5656853341/10000000000 : ℝ)|^5551 ≤ (49728776089709/100000000000000 : ℝ)^4527
        have hw : |(5656853341/10000000000 : ℝ)|=(5656853341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s0_6 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298779899/2500000000 : ℝ)*x 0 + (1131370867/2000000000 : ℝ)*x 1 + (-467666579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298779899/2500000000 : ℝ)^5551 ≤ (44798526350839/100000000000000 : ℝ)^4527 := by
    have hnat : (1298779899 : ℕ)^5551*100000000000000^4527 ≤ 44798526350839^4527*2500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298779899 2500000000 44798526350839 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131370867/2000000000 : ℝ)^5551 ≤ (6216098350551/12500000000000 : ℝ)^4527 := by
    have hnat : (1131370867 : ℕ)^5551*12500000000000^4527 ≤ 6216098350551^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131370867 2000000000 6216098350551 12500000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467666579/5000000000 : ℝ)^5551 ≤ (1094537365803/20000000000000 : ℝ)^4527 := by
    have hnat : (467666579 : ℕ)^5551*20000000000000^4527 ≤ 1094537365803^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467666579 5000000000 1094537365803 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298779899/2500000000 : ℝ), (1131370867/2000000000 : ℝ), (-467666579/5000000000 : ℝ)] ![(44798526350839/100000000000000 : ℝ), (6216098350551/12500000000000 : ℝ), (1094537365803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298779899/2500000000 : ℝ)|^5551 ≤ (44798526350839/100000000000000 : ℝ)^4527
        have hw : |(1298779899/2500000000 : ℝ)|=(1298779899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131370867/2000000000 : ℝ)|^5551 ≤ (6216098350551/12500000000000 : ℝ)^4527
        have hw : |(1131370867/2000000000 : ℝ)|=(1131370867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467666579/5000000000 : ℝ)|^5551 ≤ (1094537365803/20000000000000 : ℝ)^4527
        have hw : |(-467666579/5000000000 : ℝ)|=(467666579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s0_7 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (200196293/500000000 : ℝ)*x 0 + (1287115707/2500000000 : ℝ)*x 1 + (3031554037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200196293/500000000 : ℝ)^5551 ≤ (32551350862613/100000000000000 : ℝ)^4527 := by
    have hnat : (200196293 : ℕ)^5551*100000000000000^4527 ≤ 32551350862613^4527*500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200196293 500000000 32551350862613 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1287115707/2500000000 : ℝ)^5551 ≤ (4430569175711/10000000000000 : ℝ)^4527 := by
    have hnat : (1287115707 : ℕ)^5551*10000000000000^4527 ≤ 4430569175711^4527*2500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287115707 2500000000 4430569175711 10000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3031554037/10000000000 : ℝ)^5551 ≤ (23142957359019/100000000000000 : ℝ)^4527 := by
    have hnat : (3031554037 : ℕ)^5551*100000000000000^4527 ≤ 23142957359019^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031554037 10000000000 23142957359019 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(200196293/500000000 : ℝ), (1287115707/2500000000 : ℝ), (3031554037/10000000000 : ℝ)] ![(32551350862613/100000000000000 : ℝ), (4430569175711/10000000000000 : ℝ), (23142957359019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(200196293/500000000 : ℝ)|^5551 ≤ (32551350862613/100000000000000 : ℝ)^4527
        have hw : |(200196293/500000000 : ℝ)|=(200196293/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1287115707/2500000000 : ℝ)|^5551 ≤ (4430569175711/10000000000000 : ℝ)^4527
        have hw : |(1287115707/2500000000 : ℝ)|=(1287115707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3031554037/10000000000 : ℝ)|^5551 ≤ (23142957359019/100000000000000 : ℝ)^4527
        have hw : |(3031554037/10000000000 : ℝ)|=(3031554037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1736_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6107/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21649/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5535/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5535 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5535*1^1024 ≤ 0^1024*1^5535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5535/1024 : ℝ) ≤ (353179466132985693/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5535 ≤ (353179466132985693/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5535*50000000000000000000^1024 ≤ 353179466132985693^1024*5^5535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 353179466132985693 50000000000000000000 5535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (353179466132985693/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5535 := by
      have hnat : (1 : ℕ)^1024*1^5535 ≤ 1^5535*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50353179466132985693/50000000000000000000 : ℝ) ≤ (2002606100893703/2000000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (50353179466132985693/50000000000000000000 : ℝ)^1024 ≤ (2002606100893703/2000000000000000 : ℝ)^5535 := by
      have hnat : (50353179466132985693 : ℕ)^1024*2000000000000000^5535 ≤ 2002606100893703^5535*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50353179466132985693 50000000000000000000 2002606100893703 2000000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002606100893703/2000000000000000 : ℝ)) (X := (50353179466132985693/50000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25353179466132985693/25000000000000000000 : ℝ) ≤ (1002606100893703/1000000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (25353179466132985693/25000000000000000000 : ℝ)^1024 ≤ (1002606100893703/1000000000000000 : ℝ)^5535 := by
      have hnat : (25353179466132985693 : ℕ)^1024*1000000000000000^5535 ≤ 1002606100893703^5535*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25353179466132985693 25000000000000000000 1002606100893703 1000000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002606100893703/1000000000000000 : ℝ)) (X := (25353179466132985693/25000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2606100893703/800000000000000 : ℝ)*(0 : ℝ))^(5535/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2606100893703/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(353179466132985693/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2606100893703/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5535/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2606100893703/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2002606100893703/2000000000000000 : ℝ) by norm_num, show 1+(353179466132985693/50000000000000000000 : ℝ)+(0 : ℝ)=(50353179466132985693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(353179466132985693/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2606100893703/800000000000000 : ℝ)*(2/5 : ℝ))^(5535/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2606100893703/800000000000000 : ℝ)*(2/5 : ℝ)=(1002606100893703/1000000000000000 : ℝ) by norm_num, show 1+2*(353179466132985693/50000000000000000000 : ℝ)=(25353179466132985693/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2606100893703/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2606100893703/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2606100893703/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2606100893703/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2606100893703/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2606100893703/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1247463061/10000000000 : ℝ)*X 0 0+(2838151227/5000000000 : ℝ)*X 0 1+(2477416851/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5262491/9765625 : ℝ)*X 1 0+(-818676533/5000000000 : ℝ)*X 1 1+(4954833913/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5388790227/10000000000 : ℝ)*X 2 0+(4954834371/10000000000 : ℝ)*X 2 1+(-1637353209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((9996649/25000000 : ℝ)*X 0 0+(742823889/2500000000 : ℝ)*X 0 1+(5206697309/10000000000 : ℝ)*X 0 2+(9996649/25000000 : ℝ)*X 1 0+(742823889/2500000000 : ℝ)*X 1 1+(5206697309/10000000000 : ℝ)*X 1 2+(9996649/25000000 : ℝ)*X 2 0+(742823889/2500000000 : ℝ)*X 2 1+(5206697309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-624581713/5000000000 : ℝ)*X 0 0+(2486814403/5000000000 : ℝ)*X 0 1+(1414213493/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2597560299/5000000000 : ℝ)*X 1 0+(-37413327/400000000 : ℝ)*X 1 1+(5656853341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1298779899/2500000000 : ℝ)*X 2 0+(1131370867/2000000000 : ℝ)*X 2 1+(-467666579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((200196293/500000000 : ℝ)*X 0 0+(1287115707/2500000000 : ℝ)*X 0 1+(3031554037/10000000000 : ℝ)*X 0 2+(200196293/500000000 : ℝ)*X 1 0+(1287115707/2500000000 : ℝ)*X 1 1+(3031554037/10000000000 : ℝ)*X 1 2+(200196293/500000000 : ℝ)*X 2 0+(1287115707/2500000000 : ℝ)*X 2 1+(3031554037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74033940563720990494509/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61335321/100000000000000 : ℝ)*(base1) + (1515051411/100000000000000 : ℝ)*(base19) + (1371783021/100000000000000 : ℝ)*(base23) + (286340623/100000000000000 : ℝ)*(upper3) + (24942987/12500000000000 : ℝ)*(upper5) + (458356748077399/50000000000000 : ℝ)*(major0) + (458356748077399/50000000000000 : ℝ)*(major1) + (458356748077399/50000000000000 : ℝ)*(major2) + (1386068930032381/100000000000000 : ℝ)*(sp0) + (693037073331179/50000000000000 : ℝ)*(sp1) + (1386074289930749/100000000000000 : ℝ)*(sp2) + (223674397459829/50000000000000 : ℝ)*(sp3) + (6793016709/100000000000000 : ℝ)*(sp4) + (2227561041/100000000000000 : ℝ)*(sp7) + (22367554190801/5000000000000 : ℝ)*(f.failure) + (138607566171377/10000000000000 : ℝ)*(f.sum) + (19205440018497/20000000000000000000000000000 : ℝ)*base65 + (31424666758497/40000000000000000000000000000 : ℝ)*base67 + (22905097758497/40000000000000000000000000000 : ℝ)*base69 + (205203086438497/40000000000000000000000000000 : ℝ)*base71 + (16515767641503/20000000000000000000000000000 : ℝ)*base74 + (275712127998497/40000000000000000000000000000 : ℝ)*base75 + (17512167601503/40000000000000000000000000000 : ℝ)*base78 + (59114991281503/40000000000000000000000000000 : ℝ)*base80 + (21873929758497/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (151637/50000000000000000000 : ℝ)*base89 + (151637/50000000000000000000 : ℝ)*base91 + (151637/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8617084958546345567181/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52961257/2500000000000 : ℝ)*(base19) + (982602481/50000000000000 : ℝ)*(base23) + (12973803/20000000000000 : ℝ)*(upper2) + (310833749/100000000000000 : ℝ)*(upper3) + (353114069/100000000000000 : ℝ)*(upper5) + (24200410027191/2500000000000 : ℝ)*(major0) + (24200410027191/2500000000000 : ℝ)*(major1) + (24200410027191/2500000000000 : ℝ)*(major2) + (1840704829/25000000000000 : ℝ)*(sp1) + (18687807/250000000000 : ℝ)*(sp2) + (731822949530563/50000000000000 : ℝ)*(sp4) + (1463636417791529/100000000000000 : ℝ)*(sp5) + (365909114683341/25000000000000 : ℝ)*(sp6) + (236193307938991/50000000000000 : ℝ)*(sp7) + (236193307938991/50000000000000 : ℝ)*(f.failure) + (731822949530563/50000000000000 : ℝ)*(f.sum) + (889206165727/1000000000000000000000000000 : ℝ)*base66 + (5570466625727/2000000000000000000000000000 : ℝ)*base68 + (876819066273/2000000000000000000000000000 : ℝ)*base69 + (3447205466273/2000000000000000000000000000 : ℝ)*base71 + (5361275013273/1000000000000000000000000000 : ℝ)*base73 + (14497780216273/2000000000000000000000000000 : ℝ)*base75 + (5801751449727/2000000000000000000000000000 : ℝ)*base78 + (7590258993727/2000000000000000000000000000 : ℝ)*base80 + (5155266056273/1000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2685333/500000000000000000000 : ℝ)*base90 + (2685333/500000000000000000000 : ℝ)*base92 + (2685333/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1736_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21649/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1736_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1736_s1_0 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1303011619/10000000000 : ℝ)*x 0 + (86294307/156250000 : ℝ)*x 1 + (5071433269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1303011619/10000000000 : ℝ)^5551 ≤ (4108857145843/50000000000000 : ℝ)^4527 := by
    have hnat : (1303011619 : ℕ)^5551*50000000000000^4527 ≤ 4108857145843^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303011619 10000000000 4108857145843 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86294307/156250000 : ℝ)^5551 ≤ (48288043829471/100000000000000 : ℝ)^4527 := by
    have hnat : (86294307 : ℕ)^5551*100000000000000^4527 ≤ 48288043829471^4527*156250000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86294307 156250000 48288043829471 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5071433269/10000000000 : ℝ)^5551 ≤ (5436780232369/12500000000000 : ℝ)^4527 := by
    have hnat : (5071433269 : ℕ)^5551*12500000000000^4527 ≤ 5436780232369^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071433269 10000000000 5436780232369 12500000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1303011619/10000000000 : ℝ), (86294307/156250000 : ℝ), (5071433269/10000000000 : ℝ)] ![(4108857145843/50000000000000 : ℝ), (48288043829471/100000000000000 : ℝ), (5436780232369/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1303011619/10000000000 : ℝ)|^5551 ≤ (4108857145843/50000000000000 : ℝ)^4527
        have hw : |(-1303011619/10000000000 : ℝ)|=(1303011619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86294307/156250000 : ℝ)|^5551 ≤ (48288043829471/100000000000000 : ℝ)^4527
        have hw : |(86294307/156250000 : ℝ)|=(86294307/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5071433269/10000000000 : ℝ)|^5551 ≤ (5436780232369/12500000000000 : ℝ)^4527
        have hw : |(5071433269/10000000000 : ℝ)|=(5071433269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s1_1 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347865211/10000000000 : ℝ)*x 0 + (-1540042431/10000000000 : ℝ)*x 1 + (5071432911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347865211/10000000000 : ℝ)^5551 ≤ (46418950311467/100000000000000 : ℝ)^4527 := by
    have hnat : (5347865211 : ℕ)^5551*100000000000000^4527 ≤ 46418950311467^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347865211 10000000000 46418950311467 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1540042431/10000000000 : ℝ)^5551 ≤ (10086811581383/100000000000000 : ℝ)^4527 := by
    have hnat : (1540042431 : ℕ)^5551*100000000000000^4527 ≤ 10086811581383^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540042431 10000000000 10086811581383 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5071432911/10000000000 : ℝ)^5551 ≤ (43494238094127/100000000000000 : ℝ)^4527 := by
    have hnat : (5071432911 : ℕ)^5551*100000000000000^4527 ≤ 43494238094127^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071432911 10000000000 43494238094127 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347865211/10000000000 : ℝ), (-1540042431/10000000000 : ℝ), (5071432911/10000000000 : ℝ)] ![(46418950311467/100000000000000 : ℝ), (10086811581383/100000000000000 : ℝ), (43494238094127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347865211/10000000000 : ℝ)|^5551 ≤ (46418950311467/100000000000000 : ℝ)^4527
        have hw : |(5347865211/10000000000 : ℝ)|=(5347865211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1540042431/10000000000 : ℝ)|^5551 ≤ (10086811581383/100000000000000 : ℝ)^4527
        have hw : |(-1540042431/10000000000 : ℝ)|=(1540042431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5071432911/10000000000 : ℝ)|^5551 ≤ (43494238094127/100000000000000 : ℝ)^4527
        have hw : |(5071432911/10000000000 : ℝ)|=(5071432911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s1_2 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673932299/5000000000 : ℝ)*x 0 + (5071433537/10000000000 : ℝ)*x 1 + (-770021211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673932299/5000000000 : ℝ)^5551 ≤ (9283788757427/20000000000000 : ℝ)^4527 := by
    have hnat : (2673932299 : ℕ)^5551*20000000000000^4527 ≤ 9283788757427^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673932299 5000000000 9283788757427 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5071433537/10000000000 : ℝ)^5551 ≤ (43494244677313/100000000000000 : ℝ)^4527 := by
    have hnat : (5071433537 : ℕ)^5551*100000000000000^4527 ≤ 43494244677313^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071433537 10000000000 43494244677313 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (770021211/5000000000 : ℝ)^5551 ≤ (5043405754551/50000000000000 : ℝ)^4527 := by
    have hnat : (770021211 : ℕ)^5551*50000000000000^4527 ≤ 5043405754551^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770021211 5000000000 5043405754551 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673932299/5000000000 : ℝ), (5071433537/10000000000 : ℝ), (-770021211/5000000000 : ℝ)] ![(9283788757427/20000000000000 : ℝ), (43494244677313/100000000000000 : ℝ), (5043405754551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673932299/5000000000 : ℝ)|^5551 ≤ (9283788757427/20000000000000 : ℝ)^4527
        have hw : |(2673932299/5000000000 : ℝ)|=(2673932299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5071433537/10000000000 : ℝ)|^5551 ≤ (43494244677313/100000000000000 : ℝ)^4527
        have hw : |(5071433537/10000000000 : ℝ)|=(5071433537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-770021211/5000000000 : ℝ)|^5551 ≤ (5043405754551/50000000000000 : ℝ)^4527
        have hw : |(-770021211/5000000000 : ℝ)|=(770021211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s1_3 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4049725027/10000000000 : ℝ)*x 0 + (3385515651/10000000000 : ℝ)*x 1 + (2392071419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4049725027/10000000000 : ℝ)^5551 ≤ (33008503399569/100000000000000 : ℝ)^4527 := by
    have hnat : (4049725027 : ℕ)^5551*100000000000000^4527 ≤ 33008503399569^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4049725027 10000000000 33008503399569 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3385515651/10000000000 : ℝ)^5551 ≤ (13249415956373/50000000000000 : ℝ)^4527 := by
    have hnat : (3385515651 : ℕ)^5551*50000000000000^4527 ≤ 13249415956373^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3385515651 10000000000 13249415956373 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2392071419/5000000000 : ℝ)^5551 ≤ (10123166169059/25000000000000 : ℝ)^4527 := by
    have hnat : (2392071419 : ℕ)^5551*25000000000000^4527 ≤ 10123166169059^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392071419 5000000000 10123166169059 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4049725027/10000000000 : ℝ), (3385515651/10000000000 : ℝ), (2392071419/5000000000 : ℝ)] ![(33008503399569/100000000000000 : ℝ), (13249415956373/50000000000000 : ℝ), (10123166169059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4049725027/10000000000 : ℝ)|^5551 ≤ (33008503399569/100000000000000 : ℝ)^4527
        have hw : |(4049725027/10000000000 : ℝ)|=(4049725027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3385515651/10000000000 : ℝ)|^5551 ≤ (13249415956373/50000000000000 : ℝ)^4527
        have hw : |(3385515651/10000000000 : ℝ)|=(3385515651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2392071419/5000000000 : ℝ)|^5551 ≤ (10123166169059/25000000000000 : ℝ)^4527
        have hw : |(2392071419/5000000000 : ℝ)|=(2392071419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s1_4 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-325856451/2500000000 : ℝ)*x 0 + (1269696089/2500000000 : ℝ)*x 1 + (5515323881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325856451/2500000000 : ℝ)^5551 ≤ (411045870677/5000000000000 : ℝ)^4527 := by
    have hnat : (325856451 : ℕ)^5551*5000000000000^4527 ≤ 411045870677^4527*2500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325856451 2500000000 411045870677 5000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269696089/2500000000 : ℝ)^5551 ≤ (43571560553067/100000000000000 : ℝ)^4527 := by
    have hnat : (1269696089 : ℕ)^5551*100000000000000^4527 ≤ 43571560553067^4527*2500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269696089 2500000000 43571560553067 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5515323881/10000000000 : ℝ)^5551 ≤ (48207522025069/100000000000000 : ℝ)^4527 := by
    have hnat : (5515323881 : ℕ)^5551*100000000000000^4527 ≤ 48207522025069^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515323881 10000000000 48207522025069 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-325856451/2500000000 : ℝ), (1269696089/2500000000 : ℝ), (5515323881/10000000000 : ℝ)] ![(411045870677/5000000000000 : ℝ), (43571560553067/100000000000000 : ℝ), (48207522025069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-325856451/2500000000 : ℝ)|^5551 ≤ (411045870677/5000000000000 : ℝ)^4527
        have hw : |(-325856451/2500000000 : ℝ)|=(325856451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269696089/2500000000 : ℝ)|^5551 ≤ (43571560553067/100000000000000 : ℝ)^4527
        have hw : |(1269696089/2500000000 : ℝ)|=(1269696089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5515323881/10000000000 : ℝ)|^5551 ≤ (48207522025069/100000000000000 : ℝ)^4527
        have hw : |(5515323881/10000000000 : ℝ)|=(5515323881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s1_5 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227813663/10000000000 : ℝ)*x 0 + (-548076599/5000000000 : ℝ)*x 1 + (5515323561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227813663/10000000000 : ℝ)^5551 ≤ (352691178099/781250000000 : ℝ)^4527 := by
    have hnat : (5227813663 : ℕ)^5551*781250000000^4527 ≤ 352691178099^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227813663 10000000000 352691178099 781250000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548076599/5000000000 : ℝ)^5551 ≤ (6648010590729/100000000000000 : ℝ)^4527 := by
    have hnat : (548076599 : ℕ)^5551*100000000000000^4527 ≤ 6648010590729^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548076599 5000000000 6648010590729 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5515323561/10000000000 : ℝ)^5551 ≤ (24103759297691/50000000000000 : ℝ)^4527 := by
    have hnat : (5515323561 : ℕ)^5551*50000000000000^4527 ≤ 24103759297691^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515323561 10000000000 24103759297691 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227813663/10000000000 : ℝ), (-548076599/5000000000 : ℝ), (5515323561/10000000000 : ℝ)] ![(352691178099/781250000000 : ℝ), (6648010590729/100000000000000 : ℝ), (24103759297691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227813663/10000000000 : ℝ)|^5551 ≤ (352691178099/781250000000 : ℝ)^4527
        have hw : |(5227813663/10000000000 : ℝ)|=(5227813663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-548076599/5000000000 : ℝ)|^5551 ≤ (6648010590729/100000000000000 : ℝ)^4527
        have hw : |(-548076599/5000000000 : ℝ)|=(548076599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5515323561/10000000000 : ℝ)|^5551 ≤ (24103759297691/50000000000000 : ℝ)^4527
        have hw : |(5515323561/10000000000 : ℝ)|=(5515323561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s1_6 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227812999/10000000000 : ℝ)*x 0 + (2757662089/5000000000 : ℝ)*x 1 + (-137019157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227812999/10000000000 : ℝ)^5551 ≤ (22572231882867/50000000000000 : ℝ)^4527 := by
    have hnat : (5227812999 : ℕ)^5551*50000000000000^4527 ≤ 22572231882867^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227812999 10000000000 22572231882867 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757662089/5000000000 : ℝ)^5551 ≤ (6025940651031/12500000000000 : ℝ)^4527 := by
    have hnat : (2757662089 : ℕ)^5551*12500000000000^4527 ≤ 6025940651031^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757662089 5000000000 6025940651031 12500000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137019157/1250000000 : ℝ)^5551 ≤ (6648011022059/100000000000000 : ℝ)^4527 := by
    have hnat : (137019157 : ℕ)^5551*100000000000000^4527 ≤ 6648011022059^4527*1250000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137019157 1250000000 6648011022059 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227812999/10000000000 : ℝ), (2757662089/5000000000 : ℝ), (-137019157/1250000000 : ℝ)] ![(22572231882867/50000000000000 : ℝ), (6025940651031/12500000000000 : ℝ), (6648011022059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227812999/10000000000 : ℝ)|^5551 ≤ (22572231882867/50000000000000 : ℝ)^4527
        have hw : |(5227812999/10000000000 : ℝ)|=(5227812999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757662089/5000000000 : ℝ)|^5551 ≤ (6025940651031/12500000000000 : ℝ)^4527
        have hw : |(2757662089/5000000000 : ℝ)|=(2757662089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137019157/1250000000 : ℝ)|^5551 ≤ (6648011022059/100000000000000 : ℝ)^4527
        have hw : |(-137019157/1250000000 : ℝ)|=(137019157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s1_7 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2025499529/5000000000 : ℝ)*x 0 + (2380680519/5000000000 : ℝ)*x 1 + (3408792861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025499529/5000000000 : ℝ)^5551 ≤ (8255309288551/25000000000000 : ℝ)^4527 := by
    have hnat : (2025499529 : ℕ)^5551*25000000000000^4527 ≤ 8255309288551^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025499529 5000000000 8255309288551 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2380680519/5000000000 : ℝ)^5551 ≤ (40256352153007/100000000000000 : ℝ)^4527 := by
    have hnat : (2380680519 : ℕ)^5551*100000000000000^4527 ≤ 40256352153007^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2380680519 5000000000 40256352153007 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3408792861/10000000000 : ℝ)^5551 ≤ (26722410675637/100000000000000 : ℝ)^4527 := by
    have hnat : (3408792861 : ℕ)^5551*100000000000000^4527 ≤ 26722410675637^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3408792861 10000000000 26722410675637 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2025499529/5000000000 : ℝ), (2380680519/5000000000 : ℝ), (3408792861/10000000000 : ℝ)] ![(8255309288551/25000000000000 : ℝ), (40256352153007/100000000000000 : ℝ), (26722410675637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2025499529/5000000000 : ℝ)|^5551 ≤ (8255309288551/25000000000000 : ℝ)^4527
        have hw : |(2025499529/5000000000 : ℝ)|=(2025499529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2380680519/5000000000 : ℝ)|^5551 ≤ (40256352153007/100000000000000 : ℝ)^4527
        have hw : |(2380680519/5000000000 : ℝ)|=(2380680519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3408792861/10000000000 : ℝ)|^5551 ≤ (26722410675637/100000000000000 : ℝ)^4527
        have hw : |(3408792861/10000000000 : ℝ)|=(3408792861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1736_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21649/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1091/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18381/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21649/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21649/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21649/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21649/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21649/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21649/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6107/100000 : ℝ) ^ (5535/1024 : ℝ) ≤ (1094278581353/4000000000000000000 : ℝ) := by
    have hpowers : (6107/100000 : ℝ)^5535 ≤ (1094278581353/4000000000000000000 : ℝ)^1024 := by
      have hnat : (6107 : ℕ)^5535*4000000000000000000^1024 ≤ 1094278581353^1024*100000^5535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6107 100000 1094278581353 4000000000000000000 5535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6107/100000 : ℝ)) (X := (1094278581353/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21649/100000 : ℝ) ^ (5535/1024 : ℝ) ≤ (6394400295131381/25000000000000000000 : ℝ) := by
    have hpowers : (21649/100000 : ℝ)^5535 ≤ (6394400295131381/25000000000000000000 : ℝ)^1024 := by
      have hnat : (21649 : ℕ)^5535*25000000000000000000^1024 ≤ 6394400295131381^1024*100000^5535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21649 100000 6394400295131381 25000000000000000000 5535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21649/100000 : ℝ)) (X := (6394400295131381/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000001094278581353/2000000000000000000 : ℝ) ≤ (400000040489287/400000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (2000001094278581353/2000000000000000000 : ℝ)^1024 ≤ (400000040489287/400000000000000 : ℝ)^5535 := by
      have hnat : (2000001094278581353 : ℕ)^1024*400000000000000^5535 ≤ 400000040489287^5535*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000001094278581353 2000000000000000000 400000040489287 400000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000040489287/400000000000000 : ℝ)) (X := (2000001094278581353/2000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025604958145059349/100000000000000000000 : ℝ) ≤ (10000473653872337/10000000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (100025604958145059349/100000000000000000000 : ℝ)^1024 ≤ (10000473653872337/10000000000000000 : ℝ)^5535 := by
      have hnat : (100025604958145059349 : ℕ)^1024*10000000000000000^5535 ≤ 10000473653872337^5535*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025604958145059349 100000000000000000000 10000473653872337 10000000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000473653872337/10000000000000000 : ℝ)) (X := (100025604958145059349/100000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506394400295131381/12500000000000000000 : ℝ) ≤ (10000946295512499/10000000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (12506394400295131381/12500000000000000000 : ℝ)^1024 ≤ (10000946295512499/10000000000000000 : ℝ)^5535 := by
      have hnat : (12506394400295131381 : ℕ)^1024*10000000000000000^5535 ≤ 10000946295512499^5535*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506394400295131381 12500000000000000000 10000946295512499 10000000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000946295512499/10000000000000000 : ℝ)) (X := (12506394400295131381/12500000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1094278581353/4000000000000000000 : ℝ) ≤ ((4089848497029461189/4090000000000000000 : ℝ)+2*(12437937899/40900000000000 : ℝ)*(6107/100000 : ℝ))^(5535/1024 : ℝ) := by
    rw [show (4089848497029461189/4090000000000000000 : ℝ)+2*(12437937899/40900000000000 : ℝ)*(6107/100000 : ℝ)=(400000040489287/400000000000000 : ℝ) by norm_num, show 1+2*(1094278581353/4000000000000000000 : ℝ)=(2000001094278581353/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6394400295131381/25000000000000000000 : ℝ)+(1094278581353/4000000000000000000 : ℝ) ≤ ((4089848497029461189/4090000000000000000 : ℝ)+(12437937899/40900000000000 : ℝ)*((21649/100000 : ℝ)+(6107/100000 : ℝ)))^(5535/1024 : ℝ) := by
    rw [show (4089848497029461189/4090000000000000000 : ℝ)+(12437937899/40900000000000 : ℝ)*((21649/100000 : ℝ)+(6107/100000 : ℝ))=(10000473653872337/10000000000000000 : ℝ) by norm_num, show 1+(6394400295131381/25000000000000000000 : ℝ)+(1094278581353/4000000000000000000 : ℝ)=(100025604958145059349/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6394400295131381/25000000000000000000 : ℝ) ≤ ((4089848497029461189/4090000000000000000 : ℝ)+2*(12437937899/40900000000000 : ℝ)*(21649/100000 : ℝ))^(5535/1024 : ℝ) := by
    rw [show (4089848497029461189/4090000000000000000 : ℝ)+2*(12437937899/40900000000000 : ℝ)*(21649/100000 : ℝ)=(10000946295512499/10000000000000000 : ℝ) by norm_num, show 1+2*(6394400295131381/25000000000000000000 : ℝ)=(12506394400295131381/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4089848497029461189/4090000000000000000 : ℝ)*(X 1 0+X 2 0)+(12437937899/40900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (6107/100000 : ℝ)) (hi := (21649/100000 : ℝ)) (c := (4089848497029461189/4090000000000000000 : ℝ)) (alpha := (12437937899/40900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4089848497029461189/4090000000000000000 : ℝ)*(X 0 1+X 2 1)+(12437937899/40900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (6107/100000 : ℝ)) (hi := (21649/100000 : ℝ)) (c := (4089848497029461189/4090000000000000000 : ℝ)) (alpha := (12437937899/40900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4089848497029461189/4090000000000000000 : ℝ)*(X 0 2+X 1 2)+(12437937899/40900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (6107/100000 : ℝ)) (hi := (21649/100000 : ℝ)) (c := (4089848497029461189/4090000000000000000 : ℝ)) (alpha := (12437937899/40900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1303011619/10000000000 : ℝ)*X 0 0+(86294307/156250000 : ℝ)*X 0 1+(5071433269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347865211/10000000000 : ℝ)*X 1 0+(-1540042431/10000000000 : ℝ)*X 1 1+(5071432911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673932299/5000000000 : ℝ)*X 2 0+(5071433537/10000000000 : ℝ)*X 2 1+(-770021211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4049725027/10000000000 : ℝ)*X 0 0+(3385515651/10000000000 : ℝ)*X 0 1+(2392071419/5000000000 : ℝ)*X 0 2+(4049725027/10000000000 : ℝ)*X 1 0+(3385515651/10000000000 : ℝ)*X 1 1+(2392071419/5000000000 : ℝ)*X 1 2+(4049725027/10000000000 : ℝ)*X 2 0+(3385515651/10000000000 : ℝ)*X 2 1+(2392071419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-325856451/2500000000 : ℝ)*X 0 0+(1269696089/2500000000 : ℝ)*X 0 1+(5515323881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5227813663/10000000000 : ℝ)*X 1 0+(-548076599/5000000000 : ℝ)*X 1 1+(5515323561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5227812999/10000000000 : ℝ)*X 2 0+(2757662089/5000000000 : ℝ)*X 2 1+(-137019157/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2025499529/5000000000 : ℝ)*X 0 0+(2380680519/5000000000 : ℝ)*X 0 1+(3408792861/10000000000 : ℝ)*X 0 2+(2025499529/5000000000 : ℝ)*X 1 0+(2380680519/5000000000 : ℝ)*X 1 1+(3408792861/10000000000 : ℝ)*X 1 2+(2025499529/5000000000 : ℝ)*X 2 0+(2380680519/5000000000 : ℝ)*X 2 1+(3408792861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (970908330123416125448679297/204500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104433073/10000000000000 : ℝ)*(base19) + (66098809/10000000000000 : ℝ)*(base23) + (34603313/50000000000000 : ℝ)*(lower2) + (19331811/12500000000000 : ℝ)*(upper3) + (4621251/20000000000000 : ℝ)*(upper5) + (1465161808245809/100000000000000 : ℝ)*(major0) + (1465161808245809/100000000000000 : ℝ)*(major1) + (1465161808245809/100000000000000 : ℝ)*(major2) + (1107663163066553/50000000000000 : ℝ)*(sp0) + (2215331606378813/100000000000000 : ℝ)*(sp1) + (2215331989721453/100000000000000 : ℝ)*(sp2) + (178747126956957/25000000000000 : ℝ)*(sp3) + (6324576437/100000000000000 : ℝ)*(sp4) + (574924243/25000000000000 : ℝ)*(sp7) + (446869254703/62500000000 : ℝ)*(f.failure) + (2215332650709543/100000000000000 : ℝ)*(f.sum) + (6120178060641/2045000000000000000000000000 : ℝ)*base65 + (3039936539450506901/409000000000000000000000000000000 : ℝ)*base67 + (2818625695136493099/409000000000000000000000000000000 : ℝ)*base70 + (1300466471591506901/409000000000000000000000000000000 : ℝ)*base71 + (5908841729023/1022500000000000000000000000 : ℝ)*base73 + (578275079875506901/409000000000000000000000000000000 : ℝ)*base75 + (1852761114032506901/409000000000000000000000000000000 : ℝ)*base77 + (93407143958493099/409000000000000000000000000000000 : ℝ)*base80 + (4913351176259/2045000000000000000000000000 : ℝ)*base82 + (6239/625000000000000000 : ℝ)*base90 + (6239/625000000000000000 : ℝ)*base92 + (6239/625000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22238981040452166361083897/5112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (303771073/100000000000000 : ℝ)*(base19) + (1207875829/100000000000000 : ℝ)*(base23) + (308575491/50000000000000 : ℝ)*(upper2) + (565126577/100000000000000 : ℝ)*(upper5) + (37875970629509/2500000000000 : ℝ)*(major0) + (37875970629509/2500000000000 : ℝ)*(major1) + (37875970629509/2500000000000 : ℝ)*(major2) + (1282767991/100000000000000 : ℝ)*(sp0) + (54008103/2000000000000 : ℝ)*(sp1) + (1666884879/50000000000000 : ℝ)*(sp2) + (229074570841539/10000000000000 : ℝ)*(sp4) + (1145371993503579/50000000000000 : ℝ)*(sp5) + (1145371224768897/50000000000000 : ℝ)*(sp6) + (739330514179903/100000000000000 : ℝ)*(sp7) + (739330514179903/100000000000000 : ℝ)*(f.failure) + (2290746991183381/100000000000000 : ℝ)*(f.sum) + (1701242055263/409000000000000000000000000 : ℝ)*base65 + (22631540055276201/10225000000000000000000000000000 : ℝ)*base67 + (19108083481026201/10225000000000000000000000000000 : ℝ)*base69 + (20257638042676201/10225000000000000000000000000000 : ℝ)*base71 + (280034941327/102250000000000000000000000 : ℝ)*base73 + (63063289735748799/10225000000000000000000000000000 : ℝ)*base76 + (67857312788326201/10225000000000000000000000000000 : ℝ)*base77 + (43225388102973799/10225000000000000000000000000000 : ℝ)*base80 + (287610816559/409000000000000000000000000 : ℝ)*base82 + (3067589/1000000000000000000000 : ℝ)*base90 + (3067589/1000000000000000000000 : ℝ)*base92 + (3067589/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1736_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21649/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1091/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18381/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1736_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1736_s2_0 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1304899621/10000000000 : ℝ)*x 0 + (2758411787/5000000000 : ℝ)*x 1 + (2538086289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1304899621/10000000000 : ℝ)^5551 ≤ (4116158561529/50000000000000 : ℝ)^4527 := by
    have hnat : (1304899621 : ℕ)^5551*50000000000000^4527 ≤ 4116158561529^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304899621 10000000000 4116158561529 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758411787/5000000000 : ℝ)^5551 ≤ (3013974742951/6250000000000 : ℝ)^4527 := by
    have hnat : (2758411787 : ℕ)^5551*6250000000000^4527 ≤ 3013974742951^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758411787 5000000000 3013974742951 6250000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538086289/5000000000 : ℝ)^5551 ≤ (43544086984721/100000000000000 : ℝ)^4527 := by
    have hnat : (2538086289 : ℕ)^5551*100000000000000^4527 ≤ 43544086984721^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538086289 5000000000 43544086984721 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1304899621/10000000000 : ℝ), (2758411787/5000000000 : ℝ), (2538086289/5000000000 : ℝ)] ![(4116158561529/50000000000000 : ℝ), (3013974742951/6250000000000 : ℝ), (43544086984721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1304899621/10000000000 : ℝ)|^5551 ≤ (4116158561529/50000000000000 : ℝ)^4527
        have hw : |(-1304899621/10000000000 : ℝ)|=(1304899621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758411787/5000000000 : ℝ)|^5551 ≤ (3013974742951/6250000000000 : ℝ)^4527
        have hw : |(2758411787/5000000000 : ℝ)|=(2758411787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538086289/5000000000 : ℝ)|^5551 ≤ (43544086984721/100000000000000 : ℝ)^4527
        have hw : |(2538086289/5000000000 : ℝ)|=(2538086289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s2_1 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346217173/10000000000 : ℝ)*x 0 + (-1536020013/10000000000 : ℝ)*x 1 + (5076171289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346217173/10000000000 : ℝ)^5551 ≤ (46401410388619/100000000000000 : ℝ)^4527 := by
    have hnat : (5346217173 : ℕ)^5551*100000000000000^4527 ≤ 46401410388619^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346217173 10000000000 46401410388619 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1536020013/10000000000 : ℝ)^5551 ≤ (2513629043691/25000000000000 : ℝ)^4527 := by
    have hnat : (1536020013 : ℕ)^5551*25000000000000^4527 ≤ 2513629043691^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536020013 10000000000 2513629043691 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5076171289/10000000000 : ℝ)^5551 ≤ (43544073426383/100000000000000 : ℝ)^4527 := by
    have hnat : (5076171289 : ℕ)^5551*100000000000000^4527 ≤ 43544073426383^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076171289 10000000000 43544073426383 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346217173/10000000000 : ℝ), (-1536020013/10000000000 : ℝ), (5076171289/10000000000 : ℝ)] ![(46401410388619/100000000000000 : ℝ), (2513629043691/25000000000000 : ℝ), (43544073426383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346217173/10000000000 : ℝ)|^5551 ≤ (46401410388619/100000000000000 : ℝ)^4527
        have hw : |(5346217173/10000000000 : ℝ)|=(5346217173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1536020013/10000000000 : ℝ)|^5551 ≤ (2513629043691/25000000000000 : ℝ)^4527
        have hw : |(-1536020013/10000000000 : ℝ)|=(1536020013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5076171289/10000000000 : ℝ)|^5551 ≤ (43544073426383/100000000000000 : ℝ)^4527
        have hw : |(5076171289/10000000000 : ℝ)|=(5076171289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s2_2 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346214647/10000000000 : ℝ)*x 0 + (2538087181/5000000000 : ℝ)*x 1 + (-307203867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346214647/10000000000 : ℝ)^5551 ≤ (46401383505563/100000000000000 : ℝ)^4527 := by
    have hnat : (5346214647 : ℕ)^5551*100000000000000^4527 ≤ 46401383505563^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346214647 10000000000 46401383505563 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2538087181/5000000000 : ℝ)^5551 ≤ (21772052874857/50000000000000 : ℝ)^4527 := by
    have hnat : (2538087181 : ℕ)^5551*50000000000000^4527 ≤ 21772052874857^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538087181 5000000000 21772052874857 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307203867/2000000000 : ℝ)^5551 ≤ (2513627683203/25000000000000 : ℝ)^4527 := by
    have hnat : (307203867 : ℕ)^5551*25000000000000^4527 ≤ 2513627683203^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307203867 2000000000 2513627683203 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346214647/10000000000 : ℝ), (2538087181/5000000000 : ℝ), (-307203867/2000000000 : ℝ)] ![(46401383505563/100000000000000 : ℝ), (21772052874857/50000000000000 : ℝ), (2513627683203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346214647/10000000000 : ℝ)|^5551 ≤ (46401383505563/100000000000000 : ℝ)^4527
        have hw : |(5346214647/10000000000 : ℝ)|=(5346214647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2538087181/5000000000 : ℝ)|^5551 ≤ (21772052874857/50000000000000 : ℝ)^4527
        have hw : |(2538087181/5000000000 : ℝ)|=(2538087181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-307203867/2000000000 : ℝ)|^5551 ≤ (2513627683203/25000000000000 : ℝ)^4527
        have hw : |(-307203867/2000000000 : ℝ)|=(307203867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s2_3 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4051257977/10000000000 : ℝ)*x 0 + (340204823/1000000000 : ℝ)*x 1 + (4767362751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4051257977/10000000000 : ℝ)^5551 ≤ (6604765024547/20000000000000 : ℝ)^4527 := by
    have hnat : (4051257977 : ℕ)^5551*20000000000000^4527 ≤ 6604765024547^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051257977 10000000000 6604765024547 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340204823/1000000000 : ℝ)^5551 ≤ (5331518502977/20000000000000 : ℝ)^4527 := by
    have hnat : (340204823 : ℕ)^5551*20000000000000^4527 ≤ 5331518502977^4527*1000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340204823 1000000000 5331518502977 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4767362751/10000000000 : ℝ)^5551 ≤ (40318582346403/100000000000000 : ℝ)^4527 := by
    have hnat : (4767362751 : ℕ)^5551*100000000000000^4527 ≤ 40318582346403^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4767362751 10000000000 40318582346403 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4051257977/10000000000 : ℝ), (340204823/1000000000 : ℝ), (4767362751/10000000000 : ℝ)] ![(6604765024547/20000000000000 : ℝ), (5331518502977/20000000000000 : ℝ), (40318582346403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4051257977/10000000000 : ℝ)|^5551 ≤ (6604765024547/20000000000000 : ℝ)^4527
        have hw : |(4051257977/10000000000 : ℝ)|=(4051257977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340204823/1000000000 : ℝ)|^5551 ≤ (5331518502977/20000000000000 : ℝ)^4527
        have hw : |(340204823/1000000000 : ℝ)|=(340204823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4767362751/10000000000 : ℝ)|^5551 ≤ (40318582346403/100000000000000 : ℝ)^4527
        have hw : |(4767362751/10000000000 : ℝ)|=(4767362751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s2_4 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1305282997/10000000000 : ℝ)*x 0 + (5083180099/10000000000 : ℝ)*x 1 + (2754833971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305282997/10000000000 : ℝ)^5551 ≤ (8235282944981/100000000000000 : ℝ)^4527 := by
    have hnat : (1305282997 : ℕ)^5551*100000000000000^4527 ≤ 8235282944981^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305282997 10000000000 8235282944981 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083180099/10000000000 : ℝ)^5551 ≤ (8723561410577/20000000000000 : ℝ)^4527 := by
    have hnat : (5083180099 : ℕ)^5551*20000000000000^4527 ≤ 8723561410577^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083180099 10000000000 8723561410577 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754833971/5000000000 : ℝ)^5551 ≤ (2407345499609/5000000000000 : ℝ)^4527 := by
    have hnat : (2754833971 : ℕ)^5551*5000000000000^4527 ≤ 2407345499609^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754833971 5000000000 2407345499609 5000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1305282997/10000000000 : ℝ), (5083180099/10000000000 : ℝ), (2754833971/5000000000 : ℝ)] ![(8235282944981/100000000000000 : ℝ), (8723561410577/20000000000000 : ℝ), (2407345499609/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1305282997/10000000000 : ℝ)|^5551 ≤ (8235282944981/100000000000000 : ℝ)^4527
        have hw : |(-1305282997/10000000000 : ℝ)|=(1305282997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083180099/10000000000 : ℝ)|^5551 ≤ (8723561410577/20000000000000 : ℝ)^4527
        have hw : |(5083180099/10000000000 : ℝ)|=(5083180099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754833971/5000000000 : ℝ)|^5551 ≤ (2407345499609/5000000000000 : ℝ)^4527
        have hw : |(2754833971/5000000000 : ℝ)|=(2754833971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s2_5 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5229059757/10000000000 : ℝ)*x 0 + (-1102524819/10000000000 : ℝ)*x 1 + (2754833907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5229059757/10000000000 : ℝ)^5551 ≤ (22578832872769/50000000000000 : ℝ)^4527 := by
    have hnat : (5229059757 : ℕ)^5551*50000000000000^4527 ≤ 22578832872769^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229059757 10000000000 22578832872769 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102524819/10000000000 : ℝ)^5551 ≤ (3347712814501/50000000000000 : ℝ)^4527 := by
    have hnat : (1102524819 : ℕ)^5551*50000000000000^4527 ≤ 3347712814501^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102524819 10000000000 3347712814501 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754833907/5000000000 : ℝ)^5551 ≤ (48146908620623/100000000000000 : ℝ)^4527 := by
    have hnat : (2754833907 : ℕ)^5551*100000000000000^4527 ≤ 48146908620623^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754833907 5000000000 48146908620623 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5229059757/10000000000 : ℝ), (-1102524819/10000000000 : ℝ), (2754833907/5000000000 : ℝ)] ![(22578832872769/50000000000000 : ℝ), (3347712814501/50000000000000 : ℝ), (48146908620623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5229059757/10000000000 : ℝ)|^5551 ≤ (22578832872769/50000000000000 : ℝ)^4527
        have hw : |(5229059757/10000000000 : ℝ)|=(5229059757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1102524819/10000000000 : ℝ)|^5551 ≤ (3347712814501/50000000000000 : ℝ)^4527
        have hw : |(-1102524819/10000000000 : ℝ)|=(1102524819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754833907/5000000000 : ℝ)|^5551 ≤ (48146908620623/100000000000000 : ℝ)^4527
        have hw : |(2754833907/5000000000 : ℝ)|=(2754833907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s2_6 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5229059791/10000000000 : ℝ)*x 0 + (5509667743/10000000000 : ℝ)*x 1 + (-137815609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5229059791/10000000000 : ℝ)^5551 ≤ (5644708263197/12500000000000 : ℝ)^4527 := by
    have hnat : (5229059791 : ℕ)^5551*12500000000000^4527 ≤ 5644708263197^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229059791 10000000000 5644708263197 12500000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509667743/10000000000 : ℝ)^5551 ≤ (24073453929919/50000000000000 : ℝ)^4527 := by
    have hnat : (5509667743 : ℕ)^5551*50000000000000^4527 ≤ 24073453929919^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509667743 10000000000 24073453929919 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137815609/1250000000 : ℝ)^5551 ≤ (3347713011833/50000000000000 : ℝ)^4527 := by
    have hnat : (137815609 : ℕ)^5551*50000000000000^4527 ≤ 3347713011833^4527*1250000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137815609 1250000000 3347713011833 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5229059791/10000000000 : ℝ), (5509667743/10000000000 : ℝ), (-137815609/1250000000 : ℝ)] ![(5644708263197/12500000000000 : ℝ), (24073453929919/50000000000000 : ℝ), (3347713011833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5229059791/10000000000 : ℝ)|^5551 ≤ (5644708263197/12500000000000 : ℝ)^4527
        have hw : |(5229059791/10000000000 : ℝ)|=(5229059791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509667743/10000000000 : ℝ)|^5551 ≤ (24073453929919/50000000000000 : ℝ)^4527
        have hw : |(5509667743/10000000000 : ℝ)|=(5509667743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137815609/1250000000 : ℝ)|^5551 ≤ (3347713011833/50000000000000 : ℝ)^4527
        have hw : |(-137815609/1250000000 : ℝ)|=(137815609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s2_7 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2026222811/5000000000 : ℝ)*x 0 + (4745650927/10000000000 : ℝ)*x 1 + (34242181/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026222811/5000000000 : ℝ)^5551 ≤ (33035696449303/100000000000000 : ℝ)^4527 := by
    have hnat : (2026222811 : ℕ)^5551*100000000000000^4527 ≤ 33035696449303^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026222811 5000000000 33035696449303 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4745650927/10000000000 : ℝ)^5551 ≤ (40093542160351/100000000000000 : ℝ)^4527 := by
    have hnat : (4745650927 : ℕ)^5551*100000000000000^4527 ≤ 40093542160351^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4745650927 10000000000 40093542160351 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34242181/100000000 : ℝ)^5551 ≤ (5374152275707/20000000000000 : ℝ)^4527 := by
    have hnat : (34242181 : ℕ)^5551*20000000000000^4527 ≤ 5374152275707^4527*100000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34242181 100000000 5374152275707 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2026222811/5000000000 : ℝ), (4745650927/10000000000 : ℝ), (34242181/100000000 : ℝ)] ![(33035696449303/100000000000000 : ℝ), (40093542160351/100000000000000 : ℝ), (5374152275707/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2026222811/5000000000 : ℝ)|^5551 ≤ (33035696449303/100000000000000 : ℝ)^4527
        have hw : |(2026222811/5000000000 : ℝ)|=(2026222811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4745650927/10000000000 : ℝ)|^5551 ≤ (40093542160351/100000000000000 : ℝ)^4527
        have hw : |(4745650927/10000000000 : ℝ)|=(4745650927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34242181/100000000 : ℝ)|^5551 ≤ (5374152275707/20000000000000 : ℝ)^4527
        have hw : |(34242181/100000000 : ℝ)|=(34242181/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1736_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18381/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1091/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (276/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9127/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18381/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1091/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18381/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1091/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18381/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1091/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18381/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1091/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18381/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1091/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18381/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1091/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1091/12500 : ℝ) ^ (5535/1024 : ℝ) ≤ (47129688753223/25000000000000000000 : ℝ) := by
    have hpowers : (1091/12500 : ℝ)^5535 ≤ (47129688753223/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1091 : ℕ)^5535*25000000000000000000^1024 ≤ 47129688753223^1024*12500^5535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1091 12500 47129688753223 25000000000000000000 5535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1091/12500 : ℝ)) (X := (47129688753223/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18381/100000 : ℝ) ^ (5535/1024 : ℝ) ≤ (5280609226885531/50000000000000000000 : ℝ) := by
    have hpowers : (18381/100000 : ℝ)^5535 ≤ (5280609226885531/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18381 : ℕ)^5535*50000000000000000000^1024 ≤ 5280609226885531^1024*100000^5535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18381 100000 5280609226885531 50000000000000000000 5535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18381/100000 : ℝ)) (X := (5280609226885531/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500047129688753223/12500000000000000000 : ℝ) ≤ (2500001743838379/2500000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (12500047129688753223/12500000000000000000 : ℝ)^1024 ≤ (2500001743838379/2500000000000000 : ℝ)^5535 := by
      have hnat : (12500047129688753223 : ℕ)^1024*2500000000000000^5535 ≤ 2500001743838379^5535*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500047129688753223 12500000000000000000 2500001743838379 2500000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500001743838379/2500000000000000 : ℝ)) (X := (12500047129688753223/12500000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50005374868604391977/50000000000000000000 : ℝ) ≤ (1000019886628257/1000000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (50005374868604391977/50000000000000000000 : ℝ)^1024 ≤ (1000019886628257/1000000000000000 : ℝ)^5535 := by
      have hnat : (50005374868604391977 : ℕ)^1024*1000000000000000^5535 ≤ 1000019886628257^5535*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005374868604391977 50000000000000000000 1000019886628257 1000000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000019886628257/1000000000000000 : ℝ)) (X := (50005374868604391977/50000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005280609226885531/25000000000000000000 : ℝ) ≤ (1250048844651453/1250000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (25005280609226885531/25000000000000000000 : ℝ)^1024 ≤ (1250048844651453/1250000000000000 : ℝ)^5535 := by
      have hnat : (25005280609226885531 : ℕ)^1024*1250000000000000^5535 ≤ 1250048844651453^5535*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005280609226885531 25000000000000000000 1250048844651453 1250000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250048844651453/1250000000000000 : ℝ)) (X := (25005280609226885531/25000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(47129688753223/25000000000000000000 : ℝ) ≤ ((24131679421257480831/24132500000000000000 : ℝ)+2*(95945464527/482650000000000 : ℝ)*(1091/12500 : ℝ))^(5535/1024 : ℝ) := by
    rw [show (24131679421257480831/24132500000000000000 : ℝ)+2*(95945464527/482650000000000 : ℝ)*(1091/12500 : ℝ)=(2500001743838379/2500000000000000 : ℝ) by norm_num, show 1+2*(47129688753223/25000000000000000000 : ℝ)=(12500047129688753223/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5280609226885531/50000000000000000000 : ℝ)+(47129688753223/25000000000000000000 : ℝ) ≤ ((24131679421257480831/24132500000000000000 : ℝ)+(95945464527/482650000000000 : ℝ)*((18381/100000 : ℝ)+(1091/12500 : ℝ)))^(5535/1024 : ℝ) := by
    rw [show (24131679421257480831/24132500000000000000 : ℝ)+(95945464527/482650000000000 : ℝ)*((18381/100000 : ℝ)+(1091/12500 : ℝ))=(1000019886628257/1000000000000000 : ℝ) by norm_num, show 1+(5280609226885531/50000000000000000000 : ℝ)+(47129688753223/25000000000000000000 : ℝ)=(50005374868604391977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5280609226885531/50000000000000000000 : ℝ) ≤ ((24131679421257480831/24132500000000000000 : ℝ)+2*(95945464527/482650000000000 : ℝ)*(18381/100000 : ℝ))^(5535/1024 : ℝ) := by
    rw [show (24131679421257480831/24132500000000000000 : ℝ)+2*(95945464527/482650000000000 : ℝ)*(18381/100000 : ℝ)=(1250048844651453/1250000000000000 : ℝ) by norm_num, show 1+2*(5280609226885531/50000000000000000000 : ℝ)=(25005280609226885531/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24131679421257480831/24132500000000000000 : ℝ)*(X 1 0+X 2 0)+(95945464527/482650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (1091/12500 : ℝ)) (hi := (18381/100000 : ℝ)) (c := (24131679421257480831/24132500000000000000 : ℝ)) (alpha := (95945464527/482650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24131679421257480831/24132500000000000000 : ℝ)*(X 0 1+X 2 1)+(95945464527/482650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (1091/12500 : ℝ)) (hi := (18381/100000 : ℝ)) (c := (24131679421257480831/24132500000000000000 : ℝ)) (alpha := (95945464527/482650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24131679421257480831/24132500000000000000 : ℝ)*(X 0 2+X 1 2)+(95945464527/482650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (1091/12500 : ℝ)) (hi := (18381/100000 : ℝ)) (c := (24131679421257480831/24132500000000000000 : ℝ)) (alpha := (95945464527/482650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1304899621/10000000000 : ℝ)*X 0 0+(2758411787/5000000000 : ℝ)*X 0 1+(2538086289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346217173/10000000000 : ℝ)*X 1 0+(-1536020013/10000000000 : ℝ)*X 1 1+(5076171289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346214647/10000000000 : ℝ)*X 2 0+(2538087181/5000000000 : ℝ)*X 2 1+(-307203867/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4051257977/10000000000 : ℝ)*X 0 0+(340204823/1000000000 : ℝ)*X 0 1+(4767362751/10000000000 : ℝ)*X 0 2+(4051257977/10000000000 : ℝ)*X 1 0+(340204823/1000000000 : ℝ)*X 1 1+(4767362751/10000000000 : ℝ)*X 1 2+(4051257977/10000000000 : ℝ)*X 2 0+(340204823/1000000000 : ℝ)*X 2 1+(4767362751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1305282997/10000000000 : ℝ)*X 0 0+(5083180099/10000000000 : ℝ)*X 0 1+(2754833971/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5229059757/10000000000 : ℝ)*X 1 0+(-1102524819/10000000000 : ℝ)*X 1 1+(2754833907/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5229059791/10000000000 : ℝ)*X 2 0+(5509667743/10000000000 : ℝ)*X 2 1+(-137815609/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2026222811/5000000000 : ℝ)*X 0 0+(4745650927/10000000000 : ℝ)*X 0 1+(34242181/100000000 : ℝ)*X 0 2+(2026222811/5000000000 : ℝ)*X 1 0+(4745650927/10000000000 : ℝ)*X 1 1+(34242181/100000000 : ℝ)*X 1 2+(2026222811/5000000000 : ℝ)*X 2 0+(4745650927/10000000000 : ℝ)*X 2 1+(34242181/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3853535145039473733757803633/301656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (576587663/25000000000000 : ℝ)*(base19) + (1109004761/100000000000000 : ℝ)*(base23) + (33438461/50000000000000 : ℝ)*(lower2) + (21798283/12500000000000 : ℝ)*(upper3) + (138419721/50000000000000 : ℝ)*(upper5) + (750460386020731/50000000000000 : ℝ)*(major0) + (750460386020731/50000000000000 : ℝ)*(major1) + (750460386020731/50000000000000 : ℝ)*(major2) + (2269384709766523/100000000000000 : ℝ)*(sp0) + (70918682158913/3125000000000 : ℝ)*(sp1) + (2269399026431107/100000000000000 : ℝ)*(sp2) + (183109223597037/25000000000000 : ℝ)*(sp3) + (3085133869/20000000000000 : ℝ)*(sp4) + (1022109803/25000000000000 : ℝ)*(sp7) + (4577756142671/625000000000 : ℝ)*(f.failure) + (567350033858967/25000000000000 : ℝ)*(f.sum) + (50962191560683/12066250000000000000000000000 : ℝ)*base66 + (670006756876618923/172375000000000000000000000000000 : ℝ)*base67 + (783692071932006077/172375000000000000000000000000000 : ℝ)*base70 + (876213352717506077/172375000000000000000000000000000 : ℝ)*base72 + (6971517714201/6033125000000000000000000000 : ℝ)*base73 + (45913133689506077/172375000000000000000000000000000 : ℝ)*base76 + (1517484527507381077/172375000000000000000000000000000 : ℝ)*base78 + (249079570608756077/172375000000000000000000000000000 : ℝ)*base80 + (176134365710347/48265000000000000000000000000 : ℝ)*base82 + (35827/6250000000000000000 : ℝ)*base89 + (35827/6250000000000000000 : ℝ)*base91 + (35827/6250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2081439732546710407020974997/603312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112532633/25000000000000 : ℝ)*(base19) + (479973341/100000000000000 : ℝ)*(base23) + (14646953/25000000000000 : ℝ)*(upper3) + (5456437/50000000000000 : ℝ)*(lower4) + (71982471/100000000000000 : ℝ)*(upper5) + (775371795322857/50000000000000 : ℝ)*(major0) + (775371795322857/50000000000000 : ℝ)*(major1) + (775371795322857/50000000000000 : ℝ)*(major2) + (327347403/12500000000000 : ℝ)*(sp1) + (116943337/5000000000000 : ℝ)*(sp2) + (2344732825291841/100000000000000 : ℝ)*(sp4) + (586182439095521/25000000000000 : ℝ)*(sp5) + (29309125080647/1250000000000 : ℝ)*(sp6) + (756754240998937/100000000000000 : ℝ)*(sp7) + (756754240998937/100000000000000 : ℝ)*(f.failure) + (2344732825291841/100000000000000 : ℝ)*(f.sum) + (60357267730749/48265000000000000000000000000 : ℝ)*base66 + (177888645218764881/172375000000000000000000000000000 : ℝ)*base67 + (1520865017186764881/172375000000000000000000000000000 : ℝ)*base69 + (1112889550945764881/172375000000000000000000000000000 : ℝ)*base71 + (267816433244559/48265000000000000000000000000 : ℝ)*base74 + (2340045679023014881/172375000000000000000000000000000 : ℝ)*base75 + (671313824395764881/172375000000000000000000000000000 : ℝ)*base77 + (929129008958889881/172375000000000000000000000000000 : ℝ)*base79 + (7506054514589/12066250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6035331/1000000000000000000000 : ℝ)*base90 + (6035331/1000000000000000000000 : ℝ)*base92 + (6035331/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1736_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18381/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1091/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (276/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9127/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1736_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1736_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (276/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9127/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1736_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1736_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1736_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (276/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9127/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1736_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
