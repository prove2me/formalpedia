-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1728_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:05:48.869812+00:00
-- url     : https://prove2.me/submissions/33faad78-f55a-4284-9921-02dce2cb0d84

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
theorem support_rectangle_w1728_s0_0 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-321309559/2500000000 : ℝ)*x 0 + (5663269281/10000000000 : ℝ)*x 1 + (4978319359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (321309559/2500000000 : ℝ)^5447 ≤ (12488726821/156250000000 : ℝ)^4423 := by
    have hnat : (321309559 : ℕ)^5447*156250000000^4423 ≤ 12488726821^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321309559 2500000000 12488726821 156250000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5663269281/10000000000 : ℝ)^5447 ≤ (49647576855001/100000000000000 : ℝ)^4423 := by
    have hnat : (5663269281 : ℕ)^5447*100000000000000^4423 ≤ 49647576855001^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663269281 10000000000 49647576855001 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4978319359/10000000000 : ℝ)^5447 ≤ (8471927594357/20000000000000 : ℝ)^4423 := by
    have hnat : (4978319359 : ℕ)^5447*20000000000000^4423 ≤ 8471927594357^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4978319359 10000000000 8471927594357 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-321309559/2500000000 : ℝ), (5663269281/10000000000 : ℝ), (4978319359/10000000000 : ℝ)] ![(12488726821/156250000000 : ℝ), (49647576855001/100000000000000 : ℝ), (8471927594357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-321309559/2500000000 : ℝ)|^5447 ≤ (12488726821/156250000000 : ℝ)^4423
        have hw : |(-321309559/2500000000 : ℝ)|=(321309559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5663269281/10000000000 : ℝ)|^5447 ≤ (49647576855001/100000000000000 : ℝ)^4423
        have hw : |(5663269281/10000000000 : ℝ)|=(5663269281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4978319359/10000000000 : ℝ)|^5447 ≤ (8471927594357/20000000000000 : ℝ)^4423
        have hw : |(4978319359/10000000000 : ℝ)|=(4978319359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s0_1 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539198743/1000000000 : ℝ)*x 0 + (-1654058921/10000000000 : ℝ)*x 1 + (4978318687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539198743/1000000000 : ℝ)^5447 ≤ (23367602699397/50000000000000 : ℝ)^4423 := by
    have hnat : (539198743 : ℕ)^5447*50000000000000^4423 ≤ 23367602699397^4423*1000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539198743 1000000000 23367602699397 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1654058921/10000000000 : ℝ)^5447 ≤ (5452581829991/50000000000000 : ℝ)^4423 := by
    have hnat : (1654058921 : ℕ)^5447*50000000000000^4423 ≤ 5452581829991^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1654058921 10000000000 5452581829991 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4978318687/10000000000 : ℝ)^5447 ≤ (21179815465029/50000000000000 : ℝ)^4423 := by
    have hnat : (4978318687 : ℕ)^5447*50000000000000^4423 ≤ 21179815465029^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4978318687 10000000000 21179815465029 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539198743/1000000000 : ℝ), (-1654058921/10000000000 : ℝ), (4978318687/10000000000 : ℝ)] ![(23367602699397/50000000000000 : ℝ), (5452581829991/50000000000000 : ℝ), (21179815465029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539198743/1000000000 : ℝ)|^5447 ≤ (23367602699397/50000000000000 : ℝ)^4423
        have hw : |(539198743/1000000000 : ℝ)|=(539198743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1654058921/10000000000 : ℝ)|^5447 ≤ (5452581829991/50000000000000 : ℝ)^4423
        have hw : |(-1654058921/10000000000 : ℝ)|=(1654058921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4978318687/10000000000 : ℝ)|^5447 ≤ (21179815465029/50000000000000 : ℝ)^4423
        have hw : |(4978318687/10000000000 : ℝ)|=(4978318687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s0_2 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391986021/10000000000 : ℝ)*x 0 + (2489159789/5000000000 : ℝ)*x 1 + (-1654059623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391986021/10000000000 : ℝ)^5447 ≤ (46735190358833/100000000000000 : ℝ)^4423 := by
    have hnat : (5391986021 : ℕ)^5447*100000000000000^4423 ≤ 46735190358833^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391986021 10000000000 46735190358833 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2489159789/5000000000 : ℝ)^5447 ≤ (21179820133317/50000000000000 : ℝ)^4423 := by
    have hnat : (2489159789 : ℕ)^5447*50000000000000^4423 ≤ 21179820133317^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2489159789 5000000000 21179820133317 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1654059623/10000000000 : ℝ)^5447 ≤ (10905169359771/100000000000000 : ℝ)^4423 := by
    have hnat : (1654059623 : ℕ)^5447*100000000000000^4423 ≤ 10905169359771^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1654059623 10000000000 10905169359771 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391986021/10000000000 : ℝ), (2489159789/5000000000 : ℝ), (-1654059623/10000000000 : ℝ)] ![(46735190358833/100000000000000 : ℝ), (21179820133317/50000000000000 : ℝ), (10905169359771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391986021/10000000000 : ℝ)|^5447 ≤ (46735190358833/100000000000000 : ℝ)^4423
        have hw : |(5391986021/10000000000 : ℝ)|=(5391986021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2489159789/5000000000 : ℝ)|^5447 ≤ (21179820133317/50000000000000 : ℝ)^4423
        have hw : |(2489159789/5000000000 : ℝ)|=(2489159789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1654059623/10000000000 : ℝ)|^5447 ≤ (10905169359771/100000000000000 : ℝ)^4423
        have hw : |(-1654059623/10000000000 : ℝ)|=(1654059623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s0_3 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4024705487/10000000000 : ℝ)*x 0 + (153522473/500000000 : ℝ)*x 1 + (642251263/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4024705487/10000000000 : ℝ)^5447 ≤ (32600428177087/100000000000000 : ℝ)^4423 := by
    have hnat : (4024705487 : ℕ)^5447*100000000000000^4423 ≤ 32600428177087^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024705487 10000000000 32600428177087 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153522473/500000000 : ℝ)^5447 ≤ (23360409525469/100000000000000 : ℝ)^4423 := by
    have hnat : (153522473 : ℕ)^5447*100000000000000^4423 ≤ 23360409525469^4423*500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153522473 500000000 23360409525469 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642251263/1250000000 : ℝ)^5447 ≤ (4403916227767/10000000000000 : ℝ)^4423 := by
    have hnat : (642251263 : ℕ)^5447*10000000000000^4423 ≤ 4403916227767^4423*1250000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642251263 1250000000 4403916227767 10000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4024705487/10000000000 : ℝ), (153522473/500000000 : ℝ), (642251263/1250000000 : ℝ)] ![(32600428177087/100000000000000 : ℝ), (23360409525469/100000000000000 : ℝ), (4403916227767/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4024705487/10000000000 : ℝ)|^5447 ≤ (32600428177087/100000000000000 : ℝ)^4423
        have hw : |(4024705487/10000000000 : ℝ)|=(4024705487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(153522473/500000000 : ℝ)|^5447 ≤ (23360409525469/100000000000000 : ℝ)^4423
        have hw : |(153522473/500000000 : ℝ)|=(153522473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642251263/1250000000 : ℝ)|^5447 ≤ (4403916227767/10000000000000 : ℝ)^4423
        have hw : |(642251263/1250000000 : ℝ)|=(642251263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s0_4 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-128665197/1000000000 : ℝ)*x 0 + (4994817129/10000000000 : ℝ)*x 1 + (5646241523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128665197/1000000000 : ℝ)^5447 ≤ (8003613905323/100000000000000 : ℝ)^4423 := by
    have hnat : (128665197 : ℕ)^5447*100000000000000^4423 ≤ 8003613905323^4423*1000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128665197 1000000000 8003613905323 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4994817129/10000000000 : ℝ)^5447 ≤ (42532580417319/100000000000000 : ℝ)^4423 := by
    have hnat : (4994817129 : ℕ)^5447*100000000000000^4423 ≤ 42532580417319^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994817129 10000000000 42532580417319 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5646241523/10000000000 : ℝ)^5447 ≤ (9892761131099/20000000000000 : ℝ)^4423 := by
    have hnat : (5646241523 : ℕ)^5447*20000000000000^4423 ≤ 9892761131099^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5646241523 10000000000 9892761131099 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128665197/1000000000 : ℝ), (4994817129/10000000000 : ℝ), (5646241523/10000000000 : ℝ)] ![(8003613905323/100000000000000 : ℝ), (42532580417319/100000000000000 : ℝ), (9892761131099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128665197/1000000000 : ℝ)|^5447 ≤ (8003613905323/100000000000000 : ℝ)^4423
        have hw : |(-128665197/1000000000 : ℝ)|=(128665197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4994817129/10000000000 : ℝ)|^5447 ≤ (42532580417319/100000000000000 : ℝ)^4423
        have hw : |(4994817129/10000000000 : ℝ)|=(4994817129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5646241523/10000000000 : ℝ)|^5447 ≤ (9892761131099/20000000000000 : ℝ)^4423
        have hw : |(5646241523/10000000000 : ℝ)|=(5646241523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s0_5 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130174503/250000000 : ℝ)*x 0 + (-49306821/500000000 : ℝ)*x 1 + (1129248337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130174503/250000000 : ℝ)^5447 ≤ (5596039033361/12500000000000 : ℝ)^4423 := by
    have hnat : (130174503 : ℕ)^5447*12500000000000^4423 ≤ 5596039033361^4423*250000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130174503 250000000 5596039033361 12500000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49306821/500000000 : ℝ)^5447 ≤ (5767880317271/100000000000000 : ℝ)^4423 := by
    have hnat : (49306821 : ℕ)^5447*100000000000000^4423 ≤ 5767880317271^4423*500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49306821 500000000 5767880317271 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129248337/2000000000 : ℝ)^5447 ≤ (24731903701631/50000000000000 : ℝ)^4423 := by
    have hnat : (1129248337 : ℕ)^5447*50000000000000^4423 ≤ 24731903701631^4423*2000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129248337 2000000000 24731903701631 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130174503/250000000 : ℝ), (-49306821/500000000 : ℝ), (1129248337/2000000000 : ℝ)] ![(5596039033361/12500000000000 : ℝ), (5767880317271/100000000000000 : ℝ), (24731903701631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130174503/250000000 : ℝ)|^5447 ≤ (5596039033361/12500000000000 : ℝ)^4423
        have hw : |(130174503/250000000 : ℝ)|=(130174503/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49306821/500000000 : ℝ)|^5447 ≤ (5767880317271/100000000000000 : ℝ)^4423
        have hw : |(-49306821/500000000 : ℝ)|=(49306821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129248337/2000000000 : ℝ)|^5447 ≤ (24731903701631/50000000000000 : ℝ)^4423
        have hw : |(1129248337/2000000000 : ℝ)|=(1129248337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s0_6 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5206979713/10000000000 : ℝ)*x 0 + (5646241591/10000000000 : ℝ)*x 1 + (-986137159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5206979713/10000000000 : ℝ)^5447 ≤ (2238415397873/5000000000000 : ℝ)^4423 := by
    have hnat : (5206979713 : ℕ)^5447*5000000000000^4423 ≤ 2238415397873^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206979713 10000000000 2238415397873 5000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5646241591/10000000000 : ℝ)^5447 ≤ (395710451113/800000000000 : ℝ)^4423 := by
    have hnat : (5646241591 : ℕ)^5447*800000000000^4423 ≤ 395710451113^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5646241591 10000000000 395710451113 800000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986137159/10000000000 : ℝ)^5447 ≤ (2883942820183/50000000000000 : ℝ)^4423 := by
    have hnat : (986137159 : ℕ)^5447*50000000000000^4423 ≤ 2883942820183^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986137159 10000000000 2883942820183 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5206979713/10000000000 : ℝ), (5646241591/10000000000 : ℝ), (-986137159/10000000000 : ℝ)] ![(2238415397873/5000000000000 : ℝ), (395710451113/800000000000 : ℝ), (2883942820183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5206979713/10000000000 : ℝ)|^5447 ≤ (2238415397873/5000000000000 : ℝ)^4423
        have hw : |(5206979713/10000000000 : ℝ)|=(5206979713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5646241591/10000000000 : ℝ)|^5447 ≤ (395710451113/800000000000 : ℝ)^4423
        have hw : |(5646241591/10000000000 : ℝ)|=(5646241591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-986137159/10000000000 : ℝ)|^5447 ≤ (2883942820183/50000000000000 : ℝ)^4423
        have hw : |(-986137159/10000000000 : ℝ)|=(986137159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s0_7 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4028970217/10000000000 : ℝ)*x 0 + (2544106327/5000000000 : ℝ)*x 1 + (3121847419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4028970217/10000000000 : ℝ)^5447 ≤ (16321487857269/50000000000000 : ℝ)^4423 := by
    have hnat : (4028970217 : ℕ)^5447*50000000000000^4423 ≤ 16321487857269^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028970217 10000000000 16321487857269 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544106327/5000000000 : ℝ)^5447 ≤ (4351410957523/10000000000000 : ℝ)^4423 := by
    have hnat : (2544106327 : ℕ)^5447*10000000000000^4423 ≤ 4351410957523^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544106327 5000000000 4351410957523 10000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3121847419/10000000000 : ℝ)^5447 ≤ (23842914695709/100000000000000 : ℝ)^4423 := by
    have hnat : (3121847419 : ℕ)^5447*100000000000000^4423 ≤ 23842914695709^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121847419 10000000000 23842914695709 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4028970217/10000000000 : ℝ), (2544106327/5000000000 : ℝ), (3121847419/10000000000 : ℝ)] ![(16321487857269/50000000000000 : ℝ), (4351410957523/10000000000000 : ℝ), (23842914695709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4028970217/10000000000 : ℝ)|^5447 ≤ (16321487857269/50000000000000 : ℝ)^4423
        have hw : |(4028970217/10000000000 : ℝ)|=(4028970217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544106327/5000000000 : ℝ)|^5447 ≤ (4351410957523/10000000000000 : ℝ)^4423
        have hw : |(2544106327/5000000000 : ℝ)|=(2544106327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3121847419/10000000000 : ℝ)|^5447 ≤ (23842914695709/100000000000000 : ℝ)^4423
        have hw : |(3121847419/10000000000 : ℝ)|=(3121847419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1728_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6547/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (213/1000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (5439/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5439 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5439*1^1024 ≤ 0^1024*1^5439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5439/1024 : ℝ) ≤ (769719195415389081/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5439 ≤ (769719195415389081/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5439*100000000000000000000^1024 ≤ 769719195415389081^1024*5^5439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 769719195415389081 100000000000000000000 5439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (769719195415389081/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5439 := by
      have hnat : (1 : ℕ)^1024*1^5439 ≤ 1^5439*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100769719195415389081/100000000000000000000 : ℝ) ≤ (1001444643336141/1000000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (100769719195415389081/100000000000000000000 : ℝ)^1024 ≤ (1001444643336141/1000000000000000 : ℝ)^5439 := by
      have hnat : (100769719195415389081 : ℕ)^1024*1000000000000000^5439 ≤ 1001444643336141^5439*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100769719195415389081 100000000000000000000 1001444643336141 1000000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001444643336141/1000000000000000 : ℝ)) (X := (100769719195415389081/100000000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50769719195415389081/50000000000000000000 : ℝ) ≤ (501444643336141/500000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (50769719195415389081/50000000000000000000 : ℝ)^1024 ≤ (501444643336141/500000000000000 : ℝ)^5439 := by
      have hnat : (50769719195415389081 : ℕ)^1024*500000000000000^5439 ≤ 501444643336141^5439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50769719195415389081 50000000000000000000 501444643336141 500000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501444643336141/500000000000000 : ℝ)) (X := (50769719195415389081/50000000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1444643336141/400000000000000 : ℝ)*(0 : ℝ))^(5439/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1444643336141/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(769719195415389081/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1444643336141/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5439/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1444643336141/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1001444643336141/1000000000000000 : ℝ) by norm_num, show 1+(769719195415389081/100000000000000000000 : ℝ)+(0 : ℝ)=(100769719195415389081/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(769719195415389081/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1444643336141/400000000000000 : ℝ)*(2/5 : ℝ))^(5439/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1444643336141/400000000000000 : ℝ)*(2/5 : ℝ)=(501444643336141/500000000000000 : ℝ) by norm_num, show 1+2*(769719195415389081/100000000000000000000 : ℝ)=(50769719195415389081/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1444643336141/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1444643336141/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1444643336141/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1444643336141/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1444643336141/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1444643336141/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-321309559/2500000000 : ℝ)*X 0 0+(5663269281/10000000000 : ℝ)*X 0 1+(4978319359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((539198743/1000000000 : ℝ)*X 1 0+(-1654058921/10000000000 : ℝ)*X 1 1+(4978318687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5391986021/10000000000 : ℝ)*X 2 0+(2489159789/5000000000 : ℝ)*X 2 1+(-1654059623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4024705487/10000000000 : ℝ)*X 0 0+(153522473/500000000 : ℝ)*X 0 1+(642251263/1250000000 : ℝ)*X 0 2+(4024705487/10000000000 : ℝ)*X 1 0+(153522473/500000000 : ℝ)*X 1 1+(642251263/1250000000 : ℝ)*X 1 2+(4024705487/10000000000 : ℝ)*X 2 0+(153522473/500000000 : ℝ)*X 2 1+(642251263/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-128665197/1000000000 : ℝ)*X 0 0+(4994817129/10000000000 : ℝ)*X 0 1+(5646241523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((130174503/250000000 : ℝ)*X 1 0+(-49306821/500000000 : ℝ)*X 1 1+(1129248337/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5206979713/10000000000 : ℝ)*X 2 0+(5646241591/10000000000 : ℝ)*X 2 1+(-986137159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4028970217/10000000000 : ℝ)*X 0 0+(2544106327/5000000000 : ℝ)*X 0 1+(3121847419/10000000000 : ℝ)*X 0 2+(4028970217/10000000000 : ℝ)*X 1 0+(2544106327/5000000000 : ℝ)*X 1 1+(3121847419/10000000000 : ℝ)*X 1 2+(4028970217/10000000000 : ℝ)*X 2 0+(2544106327/5000000000 : ℝ)*X 2 1+(3121847419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16846866154576256939757/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195550013/100000000000000 : ℝ)*(base1) + (36438203/100000000000000 : ℝ)*(base16) + (424886851/50000000000000 : ℝ)*(base19) + (99307721/20000000000000 : ℝ)*(base23) + (213128587/100000000000000 : ℝ)*(upper3) + (971812910018659/100000000000000 : ℝ)*(major0) + (971812910018659/100000000000000 : ℝ)*(major1) + (971812910018659/100000000000000 : ℝ)*(major2) + (182495458154147/12500000000000 : ℝ)*(sp0) + (1459962583471259/100000000000000 : ℝ)*(sp1) + (729981367587937/50000000000000 : ℝ)*(sp2) + (483661648526001/100000000000000 : ℝ)*(sp3) + (118984343/50000000000000 : ℝ)*(sp6) + (393965691/100000000000000 : ℝ)*(sp7) + (60457779755213/12500000000000 : ℝ)*(f.failure) + (364990867420791/25000000000000 : ℝ)*(f.sum) + (62915178905081/20000000000000000000000000000 : ℝ)*base66 + (114912874145081/40000000000000000000000000000 : ℝ)*base68 + (182918473625081/40000000000000000000000000000 : ℝ)*base70 + (212618353105081/40000000000000000000000000000 : ℝ)*base72 + (35812082354919/20000000000000000000000000000 : ℝ)*base73 + (210008983585081/40000000000000000000000000000 : ℝ)*base76 + (357476357185081/40000000000000000000000000000 : ℝ)*base78 + (583449439825081/40000000000000000000000000000 : ℝ)*base80 + (81769222085081/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (228387/125000000000000000000 : ℝ)*base90 + (228387/125000000000000000000 : ℝ)*base92 + (228387/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (95318160489750957802527/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1980683051/100000000000000 : ℝ)*(base19) + (1820516109/100000000000000 : ℝ)*(base23) + (1586187/50000000000000 : ℝ)*(upper2) + (8394577/2500000000000 : ℝ)*(upper3) + (267927657/100000000000000 : ℝ)*(upper5) + (1021824724377351/100000000000000 : ℝ)*(major0) + (1021824724377351/100000000000000 : ℝ)*(major1) + (1021824724377351/100000000000000 : ℝ)*(major2) + (4127923541/50000000000000 : ℝ)*(sp1) + (3476815941/50000000000000 : ℝ)*(sp2) + (767548239286919/50000000000000 : ℝ)*(sp4) + (307017248408741/20000000000000 : ℝ)*(sp5) + (767543852212923/50000000000000 : ℝ)*(sp6) + (254276326226829/50000000000000 : ℝ)*(sp7) + (254276326226829/50000000000000 : ℝ)*(f.failure) + (767548239286919/50000000000000 : ℝ)*(f.sum) + (82126761622491/20000000000000000000000000000 : ℝ)*base65 + (78556757217509/40000000000000000000000000000 : ℝ)*base68 + (233101738897509/40000000000000000000000000000 : ℝ)*base70 + (158123485697509/40000000000000000000000000000 : ℝ)*base72 + (100996945942491/20000000000000000000000000000 : ℝ)*base73 + (159533298297509/40000000000000000000000000000 : ℝ)*base76 + (117618119902491/40000000000000000000000000000 : ℝ)*base77 + (109744215582491/40000000000000000000000000000 : ℝ)*base79 + (23715686102491/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (958029/500000000000000000000 : ℝ)*base89 + (958029/500000000000000000000 : ℝ)*base91 + (958029/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1728_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6547/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (213/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1728_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1728_s1_0 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1347164281/10000000000 : ℝ)*x 0 + (5468921231/10000000000 : ℝ)*x 1 + (205267999/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347164281/10000000000 : ℝ)^5447 ≤ (529354458749/6250000000000 : ℝ)^4423 := by
    have hnat : (1347164281 : ℕ)^5447*6250000000000^4423 ≤ 529354458749^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347164281 10000000000 529354458749 6250000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468921231/10000000000 : ℝ)^5447 ≤ (11889441084067/25000000000000 : ℝ)^4423 := by
    have hnat : (5468921231 : ℕ)^5447*25000000000000^4423 ≤ 11889441084067^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468921231 10000000000 11889441084067 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205267999/400000000 : ℝ)^5447 ≤ (43972564305901/100000000000000 : ℝ)^4423 := by
    have hnat : (205267999 : ℕ)^5447*100000000000000^4423 ≤ 43972564305901^4423*400000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205267999 400000000 43972564305901 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1347164281/10000000000 : ℝ), (5468921231/10000000000 : ℝ), (205267999/400000000 : ℝ)] ![(529354458749/6250000000000 : ℝ), (11889441084067/25000000000000 : ℝ), (43972564305901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1347164281/10000000000 : ℝ)|^5447 ≤ (529354458749/6250000000000 : ℝ)^4423
        have hw : |(-1347164281/10000000000 : ℝ)|=(1347164281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468921231/10000000000 : ℝ)|^5447 ≤ (11889441084067/25000000000000 : ℝ)^4423
        have hw : |(5468921231/10000000000 : ℝ)|=(5468921231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205267999/400000000 : ℝ)|^5447 ≤ (43972564305901/100000000000000 : ℝ)^4423
        have hw : |(205267999/400000000 : ℝ)|=(205267999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s1_1 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670117823/5000000000 : ℝ)*x 0 + (-1522123571/10000000000 : ℝ)*x 1 + (2565849527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670117823/5000000000 : ℝ)^5447 ≤ (4618341128067/10000000000000 : ℝ)^4423 := by
    have hnat : (2670117823 : ℕ)^5447*10000000000000^4423 ≤ 4618341128067^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670117823 5000000000 4618341128067 10000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1522123571/10000000000 : ℝ)^5447 ≤ (492201706001/5000000000000 : ℝ)^4423 := by
    have hnat : (1522123571 : ℕ)^5447*5000000000000^4423 ≤ 492201706001^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522123571 10000000000 492201706001 5000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565849527/5000000000 : ℝ)^5447 ≤ (43972554586923/100000000000000 : ℝ)^4423 := by
    have hnat : (2565849527 : ℕ)^5447*100000000000000^4423 ≤ 43972554586923^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565849527 5000000000 43972554586923 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670117823/5000000000 : ℝ), (-1522123571/10000000000 : ℝ), (2565849527/5000000000 : ℝ)] ![(4618341128067/10000000000000 : ℝ), (492201706001/5000000000000 : ℝ), (43972554586923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670117823/5000000000 : ℝ)|^5447 ≤ (4618341128067/10000000000000 : ℝ)^4423
        have hw : |(2670117823/5000000000 : ℝ)|=(2670117823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1522123571/10000000000 : ℝ)|^5447 ≤ (492201706001/5000000000000 : ℝ)^4423
        have hw : |(-1522123571/10000000000 : ℝ)|=(1522123571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565849527/5000000000 : ℝ)|^5447 ≤ (43972554586923/100000000000000 : ℝ)^4423
        have hw : |(2565849527/5000000000 : ℝ)|=(2565849527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s1_2 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (333764643/625000000 : ℝ)*x 0 + (2565849981/5000000000 : ℝ)*x 1 + (-190265523/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333764643/625000000 : ℝ)^5447 ≤ (2886462301089/6250000000000 : ℝ)^4423 := by
    have hnat : (333764643 : ℕ)^5447*6250000000000^4423 ≤ 2886462301089^4423*625000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333764643 625000000 2886462301089 6250000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2565849981/5000000000 : ℝ)^5447 ≤ (43972564168717/100000000000000 : ℝ)^4423 := by
    have hnat : (2565849981 : ℕ)^5447*100000000000000^4423 ≤ 43972564168717^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565849981 5000000000 43972564168717 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190265523/1250000000 : ℝ)^5447 ≤ (2461009750579/25000000000000 : ℝ)^4423 := by
    have hnat : (190265523 : ℕ)^5447*25000000000000^4423 ≤ 2461009750579^4423*1250000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190265523 1250000000 2461009750579 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(333764643/625000000 : ℝ), (2565849981/5000000000 : ℝ), (-190265523/1250000000 : ℝ)] ![(2886462301089/6250000000000 : ℝ), (43972564168717/100000000000000 : ℝ), (2461009750579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(333764643/625000000 : ℝ)|^5447 ≤ (2886462301089/6250000000000 : ℝ)^4423
        have hw : |(333764643/625000000 : ℝ)|=(333764643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2565849981/5000000000 : ℝ)|^5447 ≤ (43972564168717/100000000000000 : ℝ)^4423
        have hw : |(2565849981/5000000000 : ℝ)|=(2565849981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-190265523/1250000000 : ℝ)|^5447 ≤ (2461009750579/25000000000000 : ℝ)^4423
        have hw : |(-190265523/1250000000 : ℝ)|=(190265523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s1_3 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2040179627/5000000000 : ℝ)*x 0 + (3590563651/10000000000 : ℝ)*x 1 + (4608481113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040179627/5000000000 : ℝ)^5447 ≤ (663129628483/2000000000000 : ℝ)^4423 := by
    have hnat : (2040179627 : ℕ)^5447*2000000000000^4423 ≤ 663129628483^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040179627 5000000000 663129628483 2000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3590563651/10000000000 : ℝ)^5447 ≤ (5665068703889/20000000000000 : ℝ)^4423 := by
    have hnat : (3590563651 : ℕ)^5447*20000000000000^4423 ≤ 5665068703889^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3590563651 10000000000 5665068703889 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4608481113/10000000000 : ℝ)^5447 ≤ (7703635007681/20000000000000 : ℝ)^4423 := by
    have hnat : (4608481113 : ℕ)^5447*20000000000000^4423 ≤ 7703635007681^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4608481113 10000000000 7703635007681 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2040179627/5000000000 : ℝ), (3590563651/10000000000 : ℝ), (4608481113/10000000000 : ℝ)] ![(663129628483/2000000000000 : ℝ), (5665068703889/20000000000000 : ℝ), (7703635007681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2040179627/5000000000 : ℝ)|^5447 ≤ (663129628483/2000000000000 : ℝ)^4423
        have hw : |(2040179627/5000000000 : ℝ)|=(2040179627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3590563651/10000000000 : ℝ)|^5447 ≤ (5665068703889/20000000000000 : ℝ)^4423
        have hw : |(3590563651/10000000000 : ℝ)|=(3590563651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4608481113/10000000000 : ℝ)|^5447 ≤ (7703635007681/20000000000000 : ℝ)^4423
        have hw : |(4608481113/10000000000 : ℝ)|=(4608481113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s1_4 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1347333007/10000000000 : ℝ)*x 0 + (5135712953/10000000000 : ℝ)*x 1 + (5464844253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347333007/10000000000 : ℝ)^5447 ≤ (8470977735683/100000000000000 : ℝ)^4423 := by
    have hnat : (1347333007 : ℕ)^5447*100000000000000^4423 ≤ 8470977735683^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347333007 10000000000 8470977735683 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135712953/10000000000 : ℝ)^5447 ≤ (22007457817977/50000000000000 : ℝ)^4423 := by
    have hnat : (5135712953 : ℕ)^5447*50000000000000^4423 ≤ 22007457817977^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135712953 10000000000 22007457817977 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5464844253/10000000000 : ℝ)^5447 ≤ (23757053306711/50000000000000 : ℝ)^4423 := by
    have hnat : (5464844253 : ℕ)^5447*50000000000000^4423 ≤ 23757053306711^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464844253 10000000000 23757053306711 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1347333007/10000000000 : ℝ), (5135712953/10000000000 : ℝ), (5464844253/10000000000 : ℝ)] ![(8470977735683/100000000000000 : ℝ), (22007457817977/50000000000000 : ℝ), (23757053306711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1347333007/10000000000 : ℝ)|^5447 ≤ (8470977735683/100000000000000 : ℝ)^4423
        have hw : |(-1347333007/10000000000 : ℝ)|=(1347333007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135712953/10000000000 : ℝ)|^5447 ≤ (22007457817977/50000000000000 : ℝ)^4423
        have hw : |(5135712953/10000000000 : ℝ)|=(5135712953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5464844253/10000000000 : ℝ)|^5447 ≤ (23757053306711/50000000000000 : ℝ)^4423
        have hw : |(5464844253/10000000000 : ℝ)|=(5464844253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s1_5 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5249958119/10000000000 : ℝ)*x 0 + (-1188979531/10000000000 : ℝ)*x 1 + (341552749/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5249958119/10000000000 : ℝ)^5447 ≤ (11305952261459/25000000000000 : ℝ)^4423 := by
    have hnat : (5249958119 : ℕ)^5447*25000000000000^4423 ≤ 11305952261459^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249958119 10000000000 11305952261459 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1188979531/10000000000 : ℝ)^5447 ≤ (7262087208093/100000000000000 : ℝ)^4423 := by
    have hnat : (1188979531 : ℕ)^5447*100000000000000^4423 ≤ 7262087208093^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188979531 10000000000 7262087208093 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341552749/625000000 : ℝ)^5447 ≤ (11878525933281/25000000000000 : ℝ)^4423 := by
    have hnat : (341552749 : ℕ)^5447*25000000000000^4423 ≤ 11878525933281^4423*625000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341552749 625000000 11878525933281 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5249958119/10000000000 : ℝ), (-1188979531/10000000000 : ℝ), (341552749/625000000 : ℝ)] ![(11305952261459/25000000000000 : ℝ), (7262087208093/100000000000000 : ℝ), (11878525933281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5249958119/10000000000 : ℝ)|^5447 ≤ (11305952261459/25000000000000 : ℝ)^4423
        have hw : |(5249958119/10000000000 : ℝ)|=(5249958119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1188979531/10000000000 : ℝ)|^5447 ≤ (7262087208093/100000000000000 : ℝ)^4423
        have hw : |(-1188979531/10000000000 : ℝ)|=(1188979531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(341552749/625000000 : ℝ)|^5447 ≤ (11878525933281/25000000000000 : ℝ)^4423
        have hw : |(341552749/625000000 : ℝ)|=(341552749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s1_6 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5249958019/10000000000 : ℝ)*x 0 + (1092968779/2000000000 : ℝ)*x 1 + (-594489899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5249958019/10000000000 : ℝ)^5447 ≤ (1413243999531/3125000000000 : ℝ)^4423 := by
    have hnat : (5249958019 : ℕ)^5447*3125000000000^4423 ≤ 1413243999531^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249958019 10000000000 1413243999531 3125000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092968779/2000000000 : ℝ)^5447 ≤ (47514102780163/100000000000000 : ℝ)^4423 := by
    have hnat : (1092968779 : ℕ)^5447*100000000000000^4423 ≤ 47514102780163^4423*2000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092968779 2000000000 47514102780163 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (594489899/5000000000 : ℝ)^5447 ≤ (181552230411/2500000000000 : ℝ)^4423 := by
    have hnat : (594489899 : ℕ)^5447*2500000000000^4423 ≤ 181552230411^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594489899 5000000000 181552230411 2500000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5249958019/10000000000 : ℝ), (1092968779/2000000000 : ℝ), (-594489899/5000000000 : ℝ)] ![(1413243999531/3125000000000 : ℝ), (47514102780163/100000000000000 : ℝ), (181552230411/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5249958019/10000000000 : ℝ)|^5447 ≤ (1413243999531/3125000000000 : ℝ)^4423
        have hw : |(5249958019/10000000000 : ℝ)|=(5249958019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092968779/2000000000 : ℝ)|^5447 ≤ (47514102780163/100000000000000 : ℝ)^4423
        have hw : |(1092968779/2000000000 : ℝ)|=(1092968779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-594489899/5000000000 : ℝ)|^5447 ≤ (181552230411/2500000000000 : ℝ)^4423
        have hw : |(-594489899/5000000000 : ℝ)|=(594489899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s1_7 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (510108153/1250000000 : ℝ)*x 0 + (4596368219/10000000000 : ℝ)*x 1 + (900716783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510108153/1250000000 : ℝ)^5447 ≤ (1326461792609/4000000000000 : ℝ)^4423 := by
    have hnat : (510108153 : ℕ)^5447*4000000000000^4423 ≤ 1326461792609^4423*1250000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510108153 1250000000 1326461792609 4000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4596368219/10000000000 : ℝ)^5447 ≤ (38393533156963/100000000000000 : ℝ)^4423 := by
    have hnat : (4596368219 : ℕ)^5447*100000000000000^4423 ≤ 38393533156963^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4596368219 10000000000 38393533156963 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900716783/2500000000 : ℝ)^5447 ≤ (14222461006311/50000000000000 : ℝ)^4423 := by
    have hnat : (900716783 : ℕ)^5447*50000000000000^4423 ≤ 14222461006311^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900716783 2500000000 14222461006311 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(510108153/1250000000 : ℝ), (4596368219/10000000000 : ℝ), (900716783/2500000000 : ℝ)] ![(1326461792609/4000000000000 : ℝ), (38393533156963/100000000000000 : ℝ), (14222461006311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(510108153/1250000000 : ℝ)|^5447 ≤ (1326461792609/4000000000000 : ℝ)^4423
        have hw : |(510108153/1250000000 : ℝ)|=(510108153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4596368219/10000000000 : ℝ)|^5447 ≤ (38393533156963/100000000000000 : ℝ)^4423
        have hw : |(4596368219/10000000000 : ℝ)|=(4596368219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900716783/2500000000 : ℝ)|^5447 ≤ (14222461006311/50000000000000 : ℝ)^4423
        have hw : |(900716783/2500000000 : ℝ)|=(900716783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1728_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (213/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6547/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2489/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17177/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (213/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6547/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (213/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6547/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (213/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6547/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (213/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6547/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (213/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6547/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (213/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6547/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6547/100000 : ℝ) ^ (5439/1024 : ℝ) ≤ (51449498373511/100000000000000000000 : ℝ) := by
    have hpowers : (6547/100000 : ℝ)^5439 ≤ (51449498373511/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6547 : ℕ)^5439*100000000000000000000^1024 ≤ 51449498373511^1024*100000^5439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6547 100000 51449498373511 100000000000000000000 5439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6547/100000 : ℝ)) (X := (51449498373511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (213/1000 : ℝ) ^ (5439/1024 : ℝ) ≤ (27081487966343143/100000000000000000000 : ℝ) := by
    have hpowers : (213/1000 : ℝ)^5439 ≤ (27081487966343143/100000000000000000000 : ℝ)^1024 := by
      have hnat : (213 : ℕ)^5439*100000000000000000000^1024 ≤ 27081487966343143^1024*1000^5439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        213 1000 27081487966343143 100000000000000000000 5439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (213/1000 : ℝ)) (X := (27081487966343143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000051449498373511/50000000000000000000 : ℝ) ≤ (12500002421597/12500000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (50000051449498373511/50000000000000000000 : ℝ)^1024 ≤ (12500002421597/12500000000000 : ℝ)^5439 := by
      have hnat : (50000051449498373511 : ℕ)^1024*12500000000000^5439 ≤ 12500002421597^5439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000051449498373511 50000000000000000000 12500002421597 12500000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12500002421597/12500000000000 : ℝ)) (X := (50000051449498373511/50000000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013566468732358327/50000000000000000000 : ℝ) ≤ (10000510775304111/10000000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (50013566468732358327/50000000000000000000 : ℝ)^1024 ≤ (10000510775304111/10000000000000000 : ℝ)^5439 := by
      have hnat : (50013566468732358327 : ℕ)^1024*10000000000000000^5439 ≤ 10000510775304111^5439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013566468732358327 50000000000000000000 10000510775304111 10000000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000510775304111/10000000000000000 : ℝ)) (X := (50013566468732358327/50000000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027081487966343143/50000000000000000000 : ℝ) ≤ (5000509806665311/5000000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (50027081487966343143/50000000000000000000 : ℝ)^1024 ≤ (5000509806665311/5000000000000000 : ℝ)^5439 := by
      have hnat : (50027081487966343143 : ℕ)^1024*5000000000000000^5439 ≤ 5000509806665311^5439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027081487966343143 50000000000000000000 5000509806665311 5000000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000509806665311/5000000000000000 : ℝ)) (X := (50027081487966343143/50000000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51449498373511/100000000000000000000 : ℝ) ≤ ((73761682927768648883/73765000000000000000 : ℝ)+2*(508838026511/1475300000000000 : ℝ)*(6547/100000 : ℝ))^(5439/1024 : ℝ) := by
    rw [show (73761682927768648883/73765000000000000000 : ℝ)+2*(508838026511/1475300000000000 : ℝ)*(6547/100000 : ℝ)=(12500002421597/12500000000000 : ℝ) by norm_num, show 1+2*(51449498373511/100000000000000000000 : ℝ)=(50000051449498373511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27081487966343143/100000000000000000000 : ℝ)+(51449498373511/100000000000000000000 : ℝ) ≤ ((73761682927768648883/73765000000000000000 : ℝ)+(508838026511/1475300000000000 : ℝ)*((213/1000 : ℝ)+(6547/100000 : ℝ)))^(5439/1024 : ℝ) := by
    rw [show (73761682927768648883/73765000000000000000 : ℝ)+(508838026511/1475300000000000 : ℝ)*((213/1000 : ℝ)+(6547/100000 : ℝ))=(10000510775304111/10000000000000000 : ℝ) by norm_num, show 1+(27081487966343143/100000000000000000000 : ℝ)+(51449498373511/100000000000000000000 : ℝ)=(50013566468732358327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27081487966343143/100000000000000000000 : ℝ) ≤ ((73761682927768648883/73765000000000000000 : ℝ)+2*(508838026511/1475300000000000 : ℝ)*(213/1000 : ℝ))^(5439/1024 : ℝ) := by
    rw [show (73761682927768648883/73765000000000000000 : ℝ)+2*(508838026511/1475300000000000 : ℝ)*(213/1000 : ℝ)=(5000509806665311/5000000000000000 : ℝ) by norm_num, show 1+2*(27081487966343143/100000000000000000000 : ℝ)=(50027081487966343143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (73761682927768648883/73765000000000000000 : ℝ)*(X 1 0+X 2 0)+(508838026511/1475300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (6547/100000 : ℝ)) (hi := (213/1000 : ℝ)) (c := (73761682927768648883/73765000000000000000 : ℝ)) (alpha := (508838026511/1475300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (73761682927768648883/73765000000000000000 : ℝ)*(X 0 1+X 2 1)+(508838026511/1475300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (6547/100000 : ℝ)) (hi := (213/1000 : ℝ)) (c := (73761682927768648883/73765000000000000000 : ℝ)) (alpha := (508838026511/1475300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (73761682927768648883/73765000000000000000 : ℝ)*(X 0 2+X 1 2)+(508838026511/1475300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (6547/100000 : ℝ)) (hi := (213/1000 : ℝ)) (c := (73761682927768648883/73765000000000000000 : ℝ)) (alpha := (508838026511/1475300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1347164281/10000000000 : ℝ)*X 0 0+(5468921231/10000000000 : ℝ)*X 0 1+(205267999/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2670117823/5000000000 : ℝ)*X 1 0+(-1522123571/10000000000 : ℝ)*X 1 1+(2565849527/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((333764643/625000000 : ℝ)*X 2 0+(2565849981/5000000000 : ℝ)*X 2 1+(-190265523/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2040179627/5000000000 : ℝ)*X 0 0+(3590563651/10000000000 : ℝ)*X 0 1+(4608481113/10000000000 : ℝ)*X 0 2+(2040179627/5000000000 : ℝ)*X 1 0+(3590563651/10000000000 : ℝ)*X 1 1+(4608481113/10000000000 : ℝ)*X 1 2+(2040179627/5000000000 : ℝ)*X 2 0+(3590563651/10000000000 : ℝ)*X 2 1+(4608481113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1347333007/10000000000 : ℝ)*X 0 0+(5135712953/10000000000 : ℝ)*X 0 1+(5464844253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5249958119/10000000000 : ℝ)*X 1 0+(-1188979531/10000000000 : ℝ)*X 1 1+(341552749/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5249958019/10000000000 : ℝ)*X 2 0+(1092968779/2000000000 : ℝ)*X 2 1+(-594489899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((510108153/1250000000 : ℝ)*X 0 0+(4596368219/10000000000 : ℝ)*X 0 1+(900716783/2500000000 : ℝ)*X 0 2+(510108153/1250000000 : ℝ)*X 1 0+(4596368219/10000000000 : ℝ)*X 1 1+(900716783/2500000000 : ℝ)*X 1 2+(510108153/1250000000 : ℝ)*X 2 0+(4596368219/10000000000 : ℝ)*X 2 1+(900716783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3629491583105668413069262857/368825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1099770623/100000000000000 : ℝ)*(base19) + (35389193/4000000000000 : ℝ)*(base23) + (1228721/50000000000000 : ℝ)*(lower2) + (55778829/100000000000000 : ℝ)*(upper3) + (58745687/20000000000000 : ℝ)*(lower4) + (394783096299407/20000000000000 : ℝ)*(major0) + (394783096299407/20000000000000 : ℝ)*(major1) + (394783096299407/20000000000000 : ℝ)*(major2) + (741356269414811/25000000000000 : ℝ)*(sp0) + (29654301765959/1000000000000 : ℝ)*(sp1) + (2965430014749189/100000000000000 : ℝ)*(sp2) + (61399959912789/6250000000000 : ℝ)*(sp3) + (6198707279/100000000000000 : ℝ)*(sp4) + (376887509/100000000000000 : ℝ)*(sp6) + (61399959912789/6250000000000 : ℝ)*(f.failure) + (2965431276366523/100000000000000 : ℝ)*(f.sum) + (7172330226821/1475300000000000000000000000 : ℝ)*base66 + (9449745883005462381/1475300000000000000000000000000000 : ℝ)*base67 + (11123198554148262381/1475300000000000000000000000000000 : ℝ)*base69 + (966733379404162381/1475300000000000000000000000000000 : ℝ)*base71 + (628779667999/2950600000000000000000000000 : ℝ)*base74 + (390842425160637619/1475300000000000000000000000000000 : ℝ)*base76 + (8585144659768262381/1475300000000000000000000000000000 : ℝ)*base77 + (13314229139818862381/1475300000000000000000000000000000 : ℝ)*base79 + (8032195499563/2950600000000000000000000000 : ℝ)*base81 + (143011/62500000000000000000 : ℝ)*base90 + (143011/62500000000000000000 : ℝ)*base92 + (143011/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13151557429655510331378945693/1844125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (556998499/50000000000000 : ℝ)*(base19) + (1081637983/100000000000000 : ℝ)*(base23) + (22909439/50000000000000 : ℝ)*(upper2) + (82098203/100000000000000 : ℝ)*(upper3) + (106394639/50000000000000 : ℝ)*(upper5) + (1011210856808357/50000000000000 : ℝ)*(major0) + (1011210856808357/50000000000000 : ℝ)*(major1) + (1011210856808357/50000000000000 : ℝ)*(major2) + (1280923261/12500000000000 : ℝ)*(sp1) + (1331172839/20000000000000 : ℝ)*(sp2) + (1519151365380389/50000000000000 : ℝ)*(sp4) + (3038291369377693/100000000000000 : ℝ)*(sp5) + (3038294993258601/100000000000000 : ℝ)*(sp6) + (503270229376361/50000000000000 : ℝ)*(sp7) + (503270229376361/50000000000000 : ℝ)*(f.failure) + (1519151365380389/50000000000000 : ℝ)*(f.sum) + (133967410549219/18441250000000000000000000000 : ℝ)*base66 + (37943778050510465231/3688250000000000000000000000000000 : ℝ)*base67 + (11126724057695965231/3688250000000000000000000000000000 : ℝ)*base69 + (13915128439420284769/3688250000000000000000000000000000 : ℝ)*base72 + (223281409140299/73765000000000000000000000000 : ℝ)*base73 + (15451177328551534769/3688250000000000000000000000000000 : ℝ)*base76 + (17110101793368284769/3688250000000000000000000000000000 : ℝ)*base78 + (33131728108090284769/3688250000000000000000000000000000 : ℝ)*base80 + (45387789923759/18441250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5677161/500000000000000000000 : ℝ)*base89 + (5677161/500000000000000000000 : ℝ)*base91 + (5677161/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1728_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (213/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6547/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2489/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17177/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1728_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1728_s2_0 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1349536293/10000000000 : ℝ)*x 0 + (54590669/100000000 : ℝ)*x 1 + (5139956231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349536293/10000000000 : ℝ)^5447 ≤ (4244020302631/50000000000000 : ℝ)^4423 := by
    have hnat : (1349536293 : ℕ)^5447*50000000000000^4423 ≤ 4244020302631^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349536293 10000000000 4244020302631 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54590669/100000000 : ℝ)^5447 ≤ (47452253587203/100000000000000 : ℝ)^4423 := by
    have hnat : (54590669 : ℕ)^5447*100000000000000^4423 ≤ 47452253587203^4423*100000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54590669 100000000 47452253587203 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139956231/10000000000 : ℝ)^5447 ≤ (688432903007/1562500000000 : ℝ)^4423 := by
    have hnat : (5139956231 : ℕ)^5447*1562500000000^4423 ≤ 688432903007^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139956231 10000000000 688432903007 1562500000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1349536293/10000000000 : ℝ), (54590669/100000000 : ℝ), (5139956231/10000000000 : ℝ)] ![(4244020302631/50000000000000 : ℝ), (47452253587203/100000000000000 : ℝ), (688432903007/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1349536293/10000000000 : ℝ)|^5447 ≤ (4244020302631/50000000000000 : ℝ)^4423
        have hw : |(-1349536293/10000000000 : ℝ)|=(1349536293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54590669/100000000 : ℝ)|^5447 ≤ (47452253587203/100000000000000 : ℝ)^4423
        have hw : |(54590669/100000000 : ℝ)|=(54590669/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139956231/10000000000 : ℝ)|^5447 ≤ (688432903007/1562500000000 : ℝ)^4423
        have hw : |(5139956231/10000000000 : ℝ)|=(5139956231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s2_1 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1334386003/2500000000 : ℝ)*x 0 + (-1514776299/10000000000 : ℝ)*x 1 + (2569978087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334386003/2500000000 : ℝ)^5447 ≤ (23077372983933/50000000000000 : ℝ)^4423 := by
    have hnat : (1334386003 : ℕ)^5447*50000000000000^4423 ≤ 23077372983933^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334386003 2500000000 23077372983933 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1514776299/10000000000 : ℝ)^5447 ≤ (2446387205219/25000000000000 : ℝ)^4423 := by
    have hnat : (1514776299 : ℕ)^5447*25000000000000^4423 ≤ 2446387205219^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514776299 10000000000 2446387205219 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569978087/5000000000 : ℝ)^5447 ≤ (11014926297681/25000000000000 : ℝ)^4423 := by
    have hnat : (2569978087 : ℕ)^5447*25000000000000^4423 ≤ 11014926297681^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569978087 5000000000 11014926297681 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334386003/2500000000 : ℝ), (-1514776299/10000000000 : ℝ), (2569978087/5000000000 : ℝ)] ![(23077372983933/50000000000000 : ℝ), (2446387205219/25000000000000 : ℝ), (11014926297681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334386003/2500000000 : ℝ)|^5447 ≤ (23077372983933/50000000000000 : ℝ)^4423
        have hw : |(1334386003/2500000000 : ℝ)|=(1334386003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1514776299/10000000000 : ℝ)|^5447 ≤ (2446387205219/25000000000000 : ℝ)^4423
        have hw : |(-1514776299/10000000000 : ℝ)|=(1514776299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569978087/5000000000 : ℝ)|^5447 ≤ (11014926297681/25000000000000 : ℝ)^4423
        have hw : |(2569978087/5000000000 : ℝ)|=(2569978087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s2_2 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533754397/1000000000 : ℝ)*x 0 + (160623631/312500000 : ℝ)*x 1 + (-378694083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533754397/1000000000 : ℝ)^5447 ≤ (46154745520601/100000000000000 : ℝ)^4423 := by
    have hnat : (533754397 : ℕ)^5447*100000000000000^4423 ≤ 46154745520601^4423*1000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533754397 1000000000 46154745520601 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160623631/312500000 : ℝ)^5447 ≤ (22029852690371/50000000000000 : ℝ)^4423 := by
    have hnat : (160623631 : ℕ)^5447*50000000000000^4423 ≤ 22029852690371^4423*312500000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160623631 312500000 22029852690371 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378694083/2500000000 : ℝ)^5447 ≤ (9785549083413/100000000000000 : ℝ)^4423 := by
    have hnat : (378694083 : ℕ)^5447*100000000000000^4423 ≤ 9785549083413^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378694083 2500000000 9785549083413 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533754397/1000000000 : ℝ), (160623631/312500000 : ℝ), (-378694083/2500000000 : ℝ)] ![(46154745520601/100000000000000 : ℝ), (22029852690371/50000000000000 : ℝ), (9785549083413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533754397/1000000000 : ℝ)|^5447 ≤ (46154745520601/100000000000000 : ℝ)^4423
        have hw : |(533754397/1000000000 : ℝ)|=(533754397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160623631/312500000 : ℝ)|^5447 ≤ (22029852690371/50000000000000 : ℝ)^4423
        have hw : |(160623631/312500000 : ℝ)|=(160623631/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-378694083/2500000000 : ℝ)|^5447 ≤ (9785549083413/100000000000000 : ℝ)^4423
        have hw : |(-378694083/2500000000 : ℝ)|=(378694083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s2_3 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4082206943/10000000000 : ℝ)*x 0 + (1808869331/5000000000 : ℝ)*x 1 + (2290497/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4082206943/10000000000 : ℝ)^5447 ≤ (6634994499367/20000000000000 : ℝ)^4423 := by
    have hnat : (4082206943 : ℕ)^5447*20000000000000^4423 ≤ 6634994499367^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4082206943 10000000000 6634994499367 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1808869331/5000000000 : ℝ)^5447 ≤ (14294792900297/50000000000000 : ℝ)^4423 := by
    have hnat : (1808869331 : ℕ)^5447*50000000000000^4423 ≤ 14294792900297^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808869331 5000000000 14294792900297 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2290497/5000000 : ℝ)^5447 ≤ (38235441689197/100000000000000 : ℝ)^4423 := by
    have hnat : (2290497 : ℕ)^5447*100000000000000^4423 ≤ 38235441689197^4423*5000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290497 5000000 38235441689197 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4082206943/10000000000 : ℝ), (1808869331/5000000000 : ℝ), (2290497/5000000 : ℝ)] ![(6634994499367/20000000000000 : ℝ), (14294792900297/50000000000000 : ℝ), (38235441689197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4082206943/10000000000 : ℝ)|^5447 ≤ (6634994499367/20000000000000 : ℝ)^4423
        have hw : |(4082206943/10000000000 : ℝ)|=(4082206943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1808869331/5000000000 : ℝ)|^5447 ≤ (14294792900297/50000000000000 : ℝ)^4423
        have hw : |(1808869331/5000000000 : ℝ)|=(1808869331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2290497/5000000 : ℝ)|^5447 ≤ (38235441689197/100000000000000 : ℝ)^4423
        have hw : |(2290497/5000000 : ℝ)|=(2290497/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s2_4 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-168709797/1250000000 : ℝ)*x 0 + (1028710303/2000000000 : ℝ)*x 1 + (2727709013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168709797/1250000000 : ℝ)^5447 ≤ (8489141157667/100000000000000 : ℝ)^4423 := by
    have hnat : (168709797 : ℕ)^5447*100000000000000^4423 ≤ 8489141157667^4423*1250000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168709797 1250000000 8489141157667 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028710303/2000000000 : ℝ)^5447 ≤ (44097662712689/100000000000000 : ℝ)^4423 := by
    have hnat : (1028710303 : ℕ)^5447*100000000000000^4423 ≤ 44097662712689^4423*2000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028710303 2000000000 44097662712689 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727709013/5000000000 : ℝ)^5447 ≤ (47413196116213/100000000000000 : ℝ)^4423 := by
    have hnat : (2727709013 : ℕ)^5447*100000000000000^4423 ≤ 47413196116213^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727709013 5000000000 47413196116213 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168709797/1250000000 : ℝ), (1028710303/2000000000 : ℝ), (2727709013/5000000000 : ℝ)] ![(8489141157667/100000000000000 : ℝ), (44097662712689/100000000000000 : ℝ), (47413196116213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168709797/1250000000 : ℝ)|^5447 ≤ (8489141157667/100000000000000 : ℝ)^4423
        have hw : |(-168709797/1250000000 : ℝ)|=(168709797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028710303/2000000000 : ℝ)|^5447 ≤ (44097662712689/100000000000000 : ℝ)^4423
        have hw : |(1028710303/2000000000 : ℝ)|=(1028710303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727709013/5000000000 : ℝ)|^5447 ≤ (47413196116213/100000000000000 : ℝ)^4423
        have hw : |(2727709013/5000000000 : ℝ)|=(2727709013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s2_5 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626067453/5000000000 : ℝ)*x 0 + (-149914327/1250000000 : ℝ)*x 1 + (1091083543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626067453/5000000000 : ℝ)^5447 ≤ (11311725619899/25000000000000 : ℝ)^4423 := by
    have hnat : (2626067453 : ℕ)^5447*25000000000000^4423 ≤ 11311725619899^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626067453 5000000000 11311725619899 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149914327/1250000000 : ℝ)^5447 ≤ (293596189067/4000000000000 : ℝ)^4423 := by
    have hnat : (149914327 : ℕ)^5447*4000000000000^4423 ≤ 293596189067^4423*1250000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149914327 1250000000 293596189067 4000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091083543/2000000000 : ℝ)^5447 ≤ (47413192787533/100000000000000 : ℝ)^4423 := by
    have hnat : (1091083543 : ℕ)^5447*100000000000000^4423 ≤ 47413192787533^4423*2000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091083543 2000000000 47413192787533 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626067453/5000000000 : ℝ), (-149914327/1250000000 : ℝ), (1091083543/2000000000 : ℝ)] ![(11311725619899/25000000000000 : ℝ), (293596189067/4000000000000 : ℝ), (47413192787533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626067453/5000000000 : ℝ)|^5447 ≤ (11311725619899/25000000000000 : ℝ)^4423
        have hw : |(2626067453/5000000000 : ℝ)|=(2626067453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149914327/1250000000 : ℝ)|^5447 ≤ (293596189067/4000000000000 : ℝ)^4423
        have hw : |(-149914327/1250000000 : ℝ)|=(149914327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091083543/2000000000 : ℝ)|^5447 ≤ (47413192787533/100000000000000 : ℝ)^4423
        have hw : |(1091083543/2000000000 : ℝ)|=(1091083543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s2_6 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313033699/2500000000 : ℝ)*x 0 + (5455417913/10000000000 : ℝ)*x 1 + (-1199314489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313033699/2500000000 : ℝ)^5447 ≤ (9049380262511/20000000000000 : ℝ)^4423 := by
    have hnat : (1313033699 : ℕ)^5447*20000000000000^4423 ≤ 9049380262511^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313033699 2500000000 9049380262511 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455417913/10000000000 : ℝ)^5447 ≤ (47413194906757/100000000000000 : ℝ)^4423 := by
    have hnat : (5455417913 : ℕ)^5447*100000000000000^4423 ≤ 47413194906757^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455417913 10000000000 47413194906757 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199314489/10000000000 : ℝ)^5447 ≤ (3669951884739/50000000000000 : ℝ)^4423 := by
    have hnat : (1199314489 : ℕ)^5447*50000000000000^4423 ≤ 3669951884739^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199314489 10000000000 3669951884739 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313033699/2500000000 : ℝ), (5455417913/10000000000 : ℝ), (-1199314489/10000000000 : ℝ)] ![(9049380262511/20000000000000 : ℝ), (47413194906757/100000000000000 : ℝ), (3669951884739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313033699/2500000000 : ℝ)|^5447 ≤ (9049380262511/20000000000000 : ℝ)^4423
        have hw : |(1313033699/2500000000 : ℝ)|=(1313033699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455417913/10000000000 : ℝ)|^5447 ≤ (47413194906757/100000000000000 : ℝ)^4423
        have hw : |(5455417913/10000000000 : ℝ)|=(5455417913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1199314489/10000000000 : ℝ)|^5447 ≤ (3669951884739/50000000000000 : ℝ)^4423
        have hw : |(-1199314489/10000000000 : ℝ)|=(1199314489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s2_7 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (255164751/625000000 : ℝ)*x 0 + (4570140783/10000000000 : ℝ)*x 1 + (1814376641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (255164751/625000000 : ℝ)^5447 ≤ (8294816699407/25000000000000 : ℝ)^4423 := by
    have hnat : (255164751 : ℕ)^5447*25000000000000^4423 ≤ 8294816699407^4423*625000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255164751 625000000 8294816699407 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4570140783/10000000000 : ℝ)^5447 ≤ (19061956561957/50000000000000 : ℝ)^4423 := by
    have hnat : (4570140783 : ℕ)^5447*50000000000000^4423 ≤ 19061956561957^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570140783 10000000000 19061956561957 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1814376641/5000000000 : ℝ)^5447 ≤ (5739364011353/20000000000000 : ℝ)^4423 := by
    have hnat : (1814376641 : ℕ)^5447*20000000000000^4423 ≤ 5739364011353^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814376641 5000000000 5739364011353 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(255164751/625000000 : ℝ), (4570140783/10000000000 : ℝ), (1814376641/5000000000 : ℝ)] ![(8294816699407/25000000000000 : ℝ), (19061956561957/50000000000000 : ℝ), (5739364011353/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(255164751/625000000 : ℝ)|^5447 ≤ (8294816699407/25000000000000 : ℝ)^4423
        have hw : |(255164751/625000000 : ℝ)|=(255164751/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4570140783/10000000000 : ℝ)|^5447 ≤ (19061956561957/50000000000000 : ℝ)^4423
        have hw : |(4570140783/10000000000 : ℝ)|=(4570140783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1814376641/5000000000 : ℝ)|^5447 ≤ (5739364011353/20000000000000 : ℝ)^4423
        have hw : |(1814376641/5000000000 : ℝ)|=(1814376641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1728_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17177/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2489/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1267/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16969/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17177/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2489/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17177/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2489/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17177/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2489/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17177/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2489/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17177/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2489/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17177/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2489/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2489/25000 : ℝ) ^ (5439/1024 : ℝ) ≤ (476765037506907/100000000000000000000 : ℝ) := by
    have hpowers : (2489/25000 : ℝ)^5439 ≤ (476765037506907/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2489 : ℕ)^5439*100000000000000000000^1024 ≤ 476765037506907^1024*25000^5439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2489 25000 476765037506907 100000000000000000000 5439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2489/25000 : ℝ)) (X := (476765037506907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17177/100000 : ℝ) ^ (5439/1024 : ℝ) ≤ (8637831664024557/100000000000000000000 : ℝ) := by
    have hpowers : (17177/100000 : ℝ)^5439 ≤ (8637831664024557/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17177 : ℕ)^5439*100000000000000000000^1024 ≤ 8637831664024557^1024*100000^5439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17177 100000 8637831664024557 100000000000000000000 5439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17177/100000 : ℝ)) (X := (8637831664024557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000476765037506907/50000000000000000000 : ℝ) ≤ (2500004488007989/2500000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (50000476765037506907/50000000000000000000 : ℝ)^1024 ≤ (2500004488007989/2500000000000000 : ℝ)^5439 := by
      have hnat : (50000476765037506907 : ℕ)^1024*2500000000000000^5439 ≤ 2500004488007989^5439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000476765037506907 50000000000000000000 2500004488007989 2500000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500004488007989/2500000000000000 : ℝ)) (X := (50000476765037506907/50000000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12501139324587691433/12500000000000000000 : ℝ) ≤ (16000274550521/16000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (12501139324587691433/12500000000000000000 : ℝ)^1024 ≤ (16000274550521/16000000000000 : ℝ)^5439 := by
      have hnat : (12501139324587691433 : ℕ)^1024*16000000000000^5439 ≤ 16000274550521^5439*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501139324587691433 12500000000000000000 16000274550521 16000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16000274550521/16000000000000 : ℝ)) (X := (12501139324587691433/12500000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008637831664024557/50000000000000000000 : ℝ) ≤ (5000162618059647/5000000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (50008637831664024557/50000000000000000000 : ℝ)^1024 ≤ (5000162618059647/5000000000000000 : ℝ)^5439 := by
      have hnat : (50008637831664024557 : ℕ)^1024*5000000000000000^5439 ≤ 5000162618059647^5439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008637831664024557 50000000000000000000 5000162618059647 5000000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000162618059647/5000000000000000 : ℝ)) (X := (50008637831664024557/50000000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(476765037506907/100000000000000000000 : ℝ) ≤ ((18051767577812304287/18052500000000000000 : ℝ)+2*(153642043669/722100000000000 : ℝ)*(2489/25000 : ℝ))^(5439/1024 : ℝ) := by
    rw [show (18051767577812304287/18052500000000000000 : ℝ)+2*(153642043669/722100000000000 : ℝ)*(2489/25000 : ℝ)=(2500004488007989/2500000000000000 : ℝ) by norm_num, show 1+2*(476765037506907/100000000000000000000 : ℝ)=(50000476765037506907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8637831664024557/100000000000000000000 : ℝ)+(476765037506907/100000000000000000000 : ℝ) ≤ ((18051767577812304287/18052500000000000000 : ℝ)+(153642043669/722100000000000 : ℝ)*((17177/100000 : ℝ)+(2489/25000 : ℝ)))^(5439/1024 : ℝ) := by
    rw [show (18051767577812304287/18052500000000000000 : ℝ)+(153642043669/722100000000000 : ℝ)*((17177/100000 : ℝ)+(2489/25000 : ℝ))=(16000274550521/16000000000000 : ℝ) by norm_num, show 1+(8637831664024557/100000000000000000000 : ℝ)+(476765037506907/100000000000000000000 : ℝ)=(12501139324587691433/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8637831664024557/100000000000000000000 : ℝ) ≤ ((18051767577812304287/18052500000000000000 : ℝ)+2*(153642043669/722100000000000 : ℝ)*(17177/100000 : ℝ))^(5439/1024 : ℝ) := by
    rw [show (18051767577812304287/18052500000000000000 : ℝ)+2*(153642043669/722100000000000 : ℝ)*(17177/100000 : ℝ)=(5000162618059647/5000000000000000 : ℝ) by norm_num, show 1+2*(8637831664024557/100000000000000000000 : ℝ)=(50008637831664024557/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18051767577812304287/18052500000000000000 : ℝ)*(X 1 0+X 2 0)+(153642043669/722100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (2489/25000 : ℝ)) (hi := (17177/100000 : ℝ)) (c := (18051767577812304287/18052500000000000000 : ℝ)) (alpha := (153642043669/722100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18051767577812304287/18052500000000000000 : ℝ)*(X 0 1+X 2 1)+(153642043669/722100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (2489/25000 : ℝ)) (hi := (17177/100000 : ℝ)) (c := (18051767577812304287/18052500000000000000 : ℝ)) (alpha := (153642043669/722100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18051767577812304287/18052500000000000000 : ℝ)*(X 0 2+X 1 2)+(153642043669/722100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (2489/25000 : ℝ)) (hi := (17177/100000 : ℝ)) (c := (18051767577812304287/18052500000000000000 : ℝ)) (alpha := (153642043669/722100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1349536293/10000000000 : ℝ)*X 0 0+(54590669/100000000 : ℝ)*X 0 1+(5139956231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1334386003/2500000000 : ℝ)*X 1 0+(-1514776299/10000000000 : ℝ)*X 1 1+(2569978087/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((533754397/1000000000 : ℝ)*X 2 0+(160623631/312500000 : ℝ)*X 2 1+(-378694083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4082206943/10000000000 : ℝ)*X 0 0+(1808869331/5000000000 : ℝ)*X 0 1+(2290497/5000000 : ℝ)*X 0 2+(4082206943/10000000000 : ℝ)*X 1 0+(1808869331/5000000000 : ℝ)*X 1 1+(2290497/5000000 : ℝ)*X 1 2+(4082206943/10000000000 : ℝ)*X 2 0+(1808869331/5000000000 : ℝ)*X 2 1+(2290497/5000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-168709797/1250000000 : ℝ)*X 0 0+(1028710303/2000000000 : ℝ)*X 0 1+(2727709013/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2626067453/5000000000 : ℝ)*X 1 0+(-149914327/1250000000 : ℝ)*X 1 1+(1091083543/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313033699/2500000000 : ℝ)*X 2 0+(5455417913/10000000000 : ℝ)*X 2 1+(-1199314489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((255164751/625000000 : ℝ)*X 0 0+(4570140783/10000000000 : ℝ)*X 0 1+(1814376641/5000000000 : ℝ)*X 0 2+(255164751/625000000 : ℝ)*X 1 0+(4570140783/10000000000 : ℝ)*X 1 1+(1814376641/5000000000 : ℝ)*X 1 2+(255164751/625000000 : ℝ)*X 2 0+(4570140783/10000000000 : ℝ)*X 2 1+(1814376641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (388045095695855733699241419/37609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2343097/160000000000 : ℝ)*(base19) + (670152961/50000000000000 : ℝ)*(base23) + (13273271/25000000000000 : ℝ)*(lower2) + (257433817/100000000000000 : ℝ)*(upper3) + (32519783/20000000000000 : ℝ)*(upper5) + (130371705653719/6250000000000 : ℝ)*(major0) + (130371705653719/6250000000000 : ℝ)*(major1) + (130371705653719/6250000000000 : ℝ)*(major2) + (78343096388417/2500000000000 : ℝ)*(sp0) + (1566868112806707/50000000000000 : ℝ)*(sp1) + (1566868174871559/50000000000000 : ℝ)*(sp2) + (64884439879607/6250000000000 : ℝ)*(sp3) + (13834512359/100000000000000 : ℝ)*(sp4) + (688608799/12500000000000 : ℝ)*(sp7) + (129769568368013/12500000000000 : ℝ)*(f.failure) + (39171721125613/1250000000000 : ℝ)*(f.sum) + (1031340161777/282070312500000000000000000 : ℝ)*base65 + (21468581826090161/2350585937500000000000000000000 : ℝ)*base67 + (310492269736958201/37609375000000000000000000000000 : ℝ)*base69 + (133663418108135549/37609375000000000000000000000000 : ℝ)*base72 + (63165551934653/18052500000000000000000000000 : ℝ)*base73 + (393116996859551951/37609375000000000000000000000000 : ℝ)*base75 + (181979975153676951/37609375000000000000000000000000 : ℝ)*base77 + (108902882904385549/37609375000000000000000000000000 : ℝ)*base80 + (18043004667317/4513125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (25587/125000000000000000000 : ℝ)*base90 + (25587/125000000000000000000 : ℝ)*base92 + (25587/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41834223033734422153180797/9402343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (760162087/100000000000000 : ℝ)*(base19) + (808092701/100000000000000 : ℝ)*(base23) + (18600377/20000000000000 : ℝ)*(upper3) + (46665497/100000000000000 : ℝ)*(lower4) + (123553531/100000000000000 : ℝ)*(upper5) + (266797598635337/12500000000000 : ℝ)*(major0) + (266797598635337/12500000000000 : ℝ)*(major1) + (266797598635337/12500000000000 : ℝ)*(major2) + (605215933/12500000000000 : ℝ)*(sp1) + (6455109957/100000000000000 : ℝ)*(sp2) + (320649998154593/10000000000000 : ℝ)*(sp4) + (160324718982819/5000000000000 : ℝ)*(sp5) + (400811589792909/12500000000000 : ℝ)*(sp6) + (531130724154063/50000000000000 : ℝ)*(sp7) + (531130724154063/50000000000000 : ℝ)*(f.failure) + (320649998154593/10000000000000 : ℝ)*(f.sum) + (25563553030043/4513125000000000000000000000 : ℝ)*base65 + (169627216289871573/75218750000000000000000000000000 : ℝ)*base67 + (781229332751628427/75218750000000000000000000000000 : ℝ)*base70 + (202993327184878427/75218750000000000000000000000000 : ℝ)*base72 + (138261358435607/18052500000000000000000000000 : ℝ)*base73 + (1428712352007628427/75218750000000000000000000000000 : ℝ)*base76 + (212264485974815927/75218750000000000000000000000000 : ℝ)*base78 + (54618767144815927/75218750000000000000000000000000 : ℝ)*base80 + (5194970890789/2256562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1200463/500000000000000000000 : ℝ)*base89 + (1200463/500000000000000000000 : ℝ)*base91 + (1200463/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1728_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17177/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2489/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16969/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1728_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1728_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16969/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1728_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1728_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1728_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16969/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1728_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
