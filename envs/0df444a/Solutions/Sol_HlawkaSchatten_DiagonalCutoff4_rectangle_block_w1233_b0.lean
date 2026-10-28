-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1233_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:15:44.848564+00:00
-- url     : https://prove2.me/submissions/216c964a-6cc8-4da3-ba3c-842065148b4f

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
theorem support_rectangle_w1233_s0_0 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-465835073/2500000000 : ℝ)*x 0 + (754192003/1250000000 : ℝ)*x 1 + (4791872299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (465835073/2500000000 : ℝ)^4213 ≤ (2715940381689/25000000000000 : ℝ)^3189 := by
    have hnat : (465835073 : ℕ)^4213*25000000000000^3189 ≤ 2715940381689^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465835073 2500000000 2715940381689 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (754192003/1250000000 : ℝ)^4213 ≤ (512994510553/1000000000000 : ℝ)^3189 := by
    have hnat : (754192003 : ℕ)^4213*1000000000000^3189 ≤ 512994510553^3189*1250000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754192003 1250000000 512994510553 1000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4791872299/10000000000 : ℝ)^4213 ≤ (18918393700799/50000000000000 : ℝ)^3189 := by
    have hnat : (4791872299 : ℕ)^4213*50000000000000^3189 ≤ 18918393700799^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791872299 10000000000 18918393700799 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-465835073/2500000000 : ℝ), (754192003/1250000000 : ℝ), (4791872299/10000000000 : ℝ)] ![(2715940381689/25000000000000 : ℝ), (512994510553/1000000000000 : ℝ), (18918393700799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-465835073/2500000000 : ℝ)|^4213 ≤ (2715940381689/25000000000000 : ℝ)^3189
        have hw : |(-465835073/2500000000 : ℝ)|=(465835073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(754192003/1250000000 : ℝ)|^4213 ≤ (512994510553/1000000000000 : ℝ)^3189
        have hw : |(754192003/1250000000 : ℝ)|=(754192003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4791872299/10000000000 : ℝ)|^4213 ≤ (18918393700799/50000000000000 : ℝ)^3189
        have hw : |(4791872299/10000000000 : ℝ)|=(4791872299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s0_1 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (551166653/1000000000 : ℝ)*x 0 + (-102936497/400000000 : ℝ)*x 1 + (4791872253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551166653/1000000000 : ℝ)^4213 ≤ (22760296035399/50000000000000 : ℝ)^3189 := by
    have hnat : (551166653 : ℕ)^4213*50000000000000^3189 ≤ 22760296035399^3189*1000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551166653 1000000000 22760296035399 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102936497/400000000 : ℝ)^4213 ≤ (4160655248851/25000000000000 : ℝ)^3189 := by
    have hnat : (102936497 : ℕ)^4213*25000000000000^3189 ≤ 4160655248851^3189*400000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102936497 400000000 4160655248851 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4791872253/10000000000 : ℝ)^4213 ≤ (151347147687/400000000000 : ℝ)^3189 := by
    have hnat : (4791872253 : ℕ)^4213*400000000000^3189 ≤ 151347147687^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791872253 10000000000 151347147687 400000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551166653/1000000000 : ℝ), (-102936497/400000000 : ℝ), (4791872253/10000000000 : ℝ)] ![(22760296035399/50000000000000 : ℝ), (4160655248851/25000000000000 : ℝ), (151347147687/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551166653/1000000000 : ℝ)|^4213 ≤ (22760296035399/50000000000000 : ℝ)^3189
        have hw : |(551166653/1000000000 : ℝ)|=(551166653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102936497/400000000 : ℝ)|^4213 ≤ (4160655248851/25000000000000 : ℝ)^3189
        have hw : |(-102936497/400000000 : ℝ)|=(102936497/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4791872253/10000000000 : ℝ)|^4213 ≤ (151347147687/400000000000 : ℝ)^3189
        have hw : |(4791872253/10000000000 : ℝ)|=(4791872253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s0_2 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5511666471/10000000000 : ℝ)*x 0 + (1197968079/2500000000 : ℝ)*x 1 + (-321676553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5511666471/10000000000 : ℝ)^4213 ≤ (45520591427053/100000000000000 : ℝ)^3189 := by
    have hnat : (5511666471 : ℕ)^4213*100000000000000^3189 ≤ 45520591427053^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511666471 10000000000 45520591427053 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1197968079/2500000000 : ℝ)^4213 ≤ (18918393789467/50000000000000 : ℝ)^3189 := by
    have hnat : (1197968079 : ℕ)^4213*50000000000000^3189 ≤ 18918393789467^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197968079 2500000000 18918393789467 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321676553/1250000000 : ℝ)^4213 ≤ (832131049343/5000000000000 : ℝ)^3189 := by
    have hnat : (321676553 : ℕ)^4213*5000000000000^3189 ≤ 832131049343^3189*1250000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321676553 1250000000 832131049343 5000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5511666471/10000000000 : ℝ), (1197968079/2500000000 : ℝ), (-321676553/1250000000 : ℝ)] ![(45520591427053/100000000000000 : ℝ), (18918393789467/50000000000000 : ℝ), (832131049343/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5511666471/10000000000 : ℝ)|^4213 ≤ (45520591427053/100000000000000 : ℝ)^3189
        have hw : |(5511666471/10000000000 : ℝ)|=(5511666471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1197968079/2500000000 : ℝ)|^4213 ≤ (18918393789467/50000000000000 : ℝ)^3189
        have hw : |(1197968079/2500000000 : ℝ)|=(1197968079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321676553/1250000000 : ℝ)|^4213 ≤ (832131049343/5000000000000 : ℝ)^3189
        have hw : |(-321676553/1250000000 : ℝ)|=(321676553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s0_3 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193729319/10000000000 : ℝ)*x 0 + (779308007/2500000000 : ℝ)*x 1 + (1407914479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193729319/10000000000 : ℝ)^4213 ≤ (7931511525309/25000000000000 : ℝ)^3189 := by
    have hnat : (4193729319 : ℕ)^4213*25000000000000^3189 ≤ 7931511525309^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193729319 10000000000 7931511525309 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779308007/2500000000 : ℝ)^4213 ≤ (4287918006449/20000000000000 : ℝ)^3189 := by
    have hnat : (779308007 : ℕ)^4213*20000000000000^3189 ≤ 4287918006449^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779308007 2500000000 4287918006449 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1407914479/2500000000 : ℝ)^4213 ≤ (4683436385123/10000000000000 : ℝ)^3189 := by
    have hnat : (1407914479 : ℕ)^4213*10000000000000^3189 ≤ 4683436385123^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407914479 2500000000 4683436385123 10000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193729319/10000000000 : ℝ), (779308007/2500000000 : ℝ), (1407914479/2500000000 : ℝ)] ![(7931511525309/25000000000000 : ℝ), (4287918006449/20000000000000 : ℝ), (4683436385123/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193729319/10000000000 : ℝ)|^4213 ≤ (7931511525309/25000000000000 : ℝ)^3189
        have hw : |(4193729319/10000000000 : ℝ)|=(4193729319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779308007/2500000000 : ℝ)|^4213 ≤ (4287918006449/20000000000000 : ℝ)^3189
        have hw : |(779308007/2500000000 : ℝ)|=(779308007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1407914479/2500000000 : ℝ)|^4213 ≤ (4683436385123/10000000000000 : ℝ)^3189
        have hw : |(1407914479/2500000000 : ℝ)|=(1407914479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s0_4 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1868223419/10000000000 : ℝ)*x 0 + (4823853657/10000000000 : ℝ)*x 1 + (240016983/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868223419/10000000000 : ℝ)^4213 ≤ (10901389046273/100000000000000 : ℝ)^3189 := by
    have hnat : (1868223419 : ℕ)^4213*100000000000000^3189 ≤ 10901389046273^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868223419 10000000000 10901389046273 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4823853657/10000000000 : ℝ)^4213 ≤ (38170757260437/100000000000000 : ℝ)^3189 := by
    have hnat : (4823853657 : ℕ)^4213*100000000000000^3189 ≤ 38170757260437^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4823853657 10000000000 38170757260437 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240016983/400000000 : ℝ)^4213 ≤ (50927853682481/100000000000000 : ℝ)^3189 := by
    have hnat : (240016983 : ℕ)^4213*100000000000000^3189 ≤ 50927853682481^3189*400000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240016983 400000000 50927853682481 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1868223419/10000000000 : ℝ), (4823853657/10000000000 : ℝ), (240016983/400000000 : ℝ)] ![(10901389046273/100000000000000 : ℝ), (38170757260437/100000000000000 : ℝ), (50927853682481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1868223419/10000000000 : ℝ)|^4213 ≤ (10901389046273/100000000000000 : ℝ)^3189
        have hw : |(-1868223419/10000000000 : ℝ)|=(1868223419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4823853657/10000000000 : ℝ)|^4213 ≤ (38170757260437/100000000000000 : ℝ)^3189
        have hw : |(4823853657/10000000000 : ℝ)|=(4823853657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(240016983/400000000 : ℝ)|^4213 ≤ (50927853682481/100000000000000 : ℝ)^3189
        have hw : |(240016983/400000000 : ℝ)|=(240016983/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s0_5 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173865659/10000000000 : ℝ)*x 0 + (-272971603/2000000000 : ℝ)*x 1 + (24001707/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173865659/10000000000 : ℝ)^4213 ≤ (10467913246611/25000000000000 : ℝ)^3189 := by
    have hnat : (5173865659 : ℕ)^4213*25000000000000^3189 ≤ 10467913246611^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173865659 10000000000 10467913246611 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272971603/2000000000 : ℝ)^4213 ≤ (7200468930207/100000000000000 : ℝ)^3189 := by
    have hnat : (272971603 : ℕ)^4213*100000000000000^3189 ≤ 7200468930207^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272971603 2000000000 7200468930207 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24001707/40000000 : ℝ)^4213 ≤ (50927878070113/100000000000000 : ℝ)^3189 := by
    have hnat : (24001707 : ℕ)^4213*100000000000000^3189 ≤ 50927878070113^3189*40000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24001707 40000000 50927878070113 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173865659/10000000000 : ℝ), (-272971603/2000000000 : ℝ), (24001707/40000000 : ℝ)] ![(10467913246611/25000000000000 : ℝ), (7200468930207/100000000000000 : ℝ), (50927878070113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173865659/10000000000 : ℝ)|^4213 ≤ (10467913246611/25000000000000 : ℝ)^3189
        have hw : |(5173865659/10000000000 : ℝ)|=(5173865659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-272971603/2000000000 : ℝ)|^4213 ≤ (7200468930207/100000000000000 : ℝ)^3189
        have hw : |(-272971603/2000000000 : ℝ)|=(272971603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(24001707/40000000 : ℝ)|^4213 ≤ (50927878070113/100000000000000 : ℝ)^3189
        have hw : |(24001707/40000000 : ℝ)|=(24001707/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s0_6 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173866477/10000000000 : ℝ)*x 0 + (1500106267/2500000000 : ℝ)*x 1 + (-682429733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173866477/10000000000 : ℝ)^4213 ≤ (41871661732157/100000000000000 : ℝ)^3189 := by
    have hnat : (5173866477 : ℕ)^4213*100000000000000^3189 ≤ 41871661732157^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173866477 10000000000 41871661732157 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1500106267/2500000000 : ℝ)^4213 ≤ (6365982401293/12500000000000 : ℝ)^3189 := by
    have hnat : (1500106267 : ℕ)^4213*12500000000000^3189 ≤ 6365982401293^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500106267 2500000000 6365982401293 12500000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682429733/5000000000 : ℝ)^4213 ≤ (3600239521577/50000000000000 : ℝ)^3189 := by
    have hnat : (682429733 : ℕ)^4213*50000000000000^3189 ≤ 3600239521577^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682429733 5000000000 3600239521577 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173866477/10000000000 : ℝ), (1500106267/2500000000 : ℝ), (-682429733/5000000000 : ℝ)] ![(41871661732157/100000000000000 : ℝ), (6365982401293/12500000000000 : ℝ), (3600239521577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173866477/10000000000 : ℝ)|^4213 ≤ (41871661732157/100000000000000 : ℝ)^3189
        have hw : |(5173866477/10000000000 : ℝ)|=(5173866477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1500106267/2500000000 : ℝ)|^4213 ≤ (6365982401293/12500000000000 : ℝ)^3189
        have hw : |(1500106267/2500000000 : ℝ)|=(1500106267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-682429733/5000000000 : ℝ)|^4213 ≤ (3600239521577/50000000000000 : ℝ)^3189
        have hw : |(-682429733/5000000000 : ℝ)|=(682429733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s0_7 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4203618227/10000000000 : ℝ)*x 0 + (2783449559/5000000000 : ℝ)*x 1 + (3184278627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203618227/10000000000 : ℝ)^4213 ≤ (31824916236923/100000000000000 : ℝ)^3189 := by
    have hnat : (4203618227 : ℕ)^4213*100000000000000^3189 ≤ 31824916236923^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203618227 10000000000 31824916236923 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2783449559/5000000000 : ℝ)^4213 ≤ (23062099279299/50000000000000 : ℝ)^3189 := by
    have hnat : (2783449559 : ℕ)^4213*50000000000000^3189 ≤ 23062099279299^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783449559 5000000000 23062099279299 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3184278627/10000000000 : ℝ)^4213 ≤ (5512721297869/25000000000000 : ℝ)^3189 := by
    have hnat : (3184278627 : ℕ)^4213*25000000000000^3189 ≤ 5512721297869^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184278627 10000000000 5512721297869 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203618227/10000000000 : ℝ), (2783449559/5000000000 : ℝ), (3184278627/10000000000 : ℝ)] ![(31824916236923/100000000000000 : ℝ), (23062099279299/50000000000000 : ℝ), (5512721297869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203618227/10000000000 : ℝ)|^4213 ≤ (31824916236923/100000000000000 : ℝ)^3189
        have hw : |(4203618227/10000000000 : ℝ)|=(4203618227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2783449559/5000000000 : ℝ)|^4213 ≤ (23062099279299/50000000000000 : ℝ)^3189
        have hw : |(2783449559/5000000000 : ℝ)|=(2783449559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3184278627/10000000000 : ℝ)|^4213 ≤ (5512721297869/25000000000000 : ℝ)^3189
        have hw : |(3184278627/10000000000 : ℝ)|=(3184278627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1233_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (391/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2747/10000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8425/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8425 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8425*1^2048 ≤ 0^2048*1^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8425/2048 : ℝ) ≤ (2306569351550735971/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8425 ≤ (2306569351550735971/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8425*100000000000000000000^2048 ≤ 2306569351550735971^2048*5^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2306569351550735971 100000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2306569351550735971/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8425 := by
      have hnat : (1 : ℕ)^2048*1^8425 ≤ 1^8425*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102306569351550735971/100000000000000000000 : ℝ) ≤ (1256948317613269/1250000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (102306569351550735971/100000000000000000000 : ℝ)^2048 ≤ (1256948317613269/1250000000000000 : ℝ)^8425 := by
      have hnat : (102306569351550735971 : ℕ)^2048*1250000000000000^8425 ≤ 1256948317613269^8425*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102306569351550735971 100000000000000000000 1256948317613269 1250000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256948317613269/1250000000000000 : ℝ)) (X := (102306569351550735971/100000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52306569351550735971/50000000000000000000 : ℝ) ≤ (631948317613269/625000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (52306569351550735971/50000000000000000000 : ℝ)^2048 ≤ (631948317613269/625000000000000 : ℝ)^8425 := by
      have hnat : (52306569351550735971 : ℕ)^2048*625000000000000^8425 ≤ 631948317613269^8425*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52306569351550735971 50000000000000000000 631948317613269 625000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631948317613269/625000000000000 : ℝ)) (X := (52306569351550735971/50000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6948317613269/500000000000000 : ℝ)*(0 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(6948317613269/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2306569351550735971/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6948317613269/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8425/2048 : ℝ) := by
    rw [show (1 : ℝ)+(6948317613269/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1256948317613269/1250000000000000 : ℝ) by norm_num, show 1+(2306569351550735971/100000000000000000000 : ℝ)+(0 : ℝ)=(102306569351550735971/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2306569351550735971/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6948317613269/500000000000000 : ℝ)*(2/5 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(6948317613269/500000000000000 : ℝ)*(2/5 : ℝ)=(631948317613269/625000000000000 : ℝ) by norm_num, show 1+2*(2306569351550735971/100000000000000000000 : ℝ)=(52306569351550735971/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6948317613269/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6948317613269/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6948317613269/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6948317613269/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6948317613269/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6948317613269/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-465835073/2500000000 : ℝ)*X 0 0+(754192003/1250000000 : ℝ)*X 0 1+(4791872299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((551166653/1000000000 : ℝ)*X 1 0+(-102936497/400000000 : ℝ)*X 1 1+(4791872253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5511666471/10000000000 : ℝ)*X 2 0+(1197968079/2500000000 : ℝ)*X 2 1+(-321676553/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4193729319/10000000000 : ℝ)*X 0 0+(779308007/2500000000 : ℝ)*X 0 1+(1407914479/2500000000 : ℝ)*X 0 2+(4193729319/10000000000 : ℝ)*X 1 0+(779308007/2500000000 : ℝ)*X 1 1+(1407914479/2500000000 : ℝ)*X 1 2+(4193729319/10000000000 : ℝ)*X 2 0+(779308007/2500000000 : ℝ)*X 2 1+(1407914479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1868223419/10000000000 : ℝ)*X 0 0+(4823853657/10000000000 : ℝ)*X 0 1+(240016983/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173865659/10000000000 : ℝ)*X 1 0+(-272971603/2000000000 : ℝ)*X 1 1+(24001707/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173866477/10000000000 : ℝ)*X 2 0+(1500106267/2500000000 : ℝ)*X 2 1+(-682429733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4203618227/10000000000 : ℝ)*X 0 0+(2783449559/5000000000 : ℝ)*X 0 1+(3184278627/10000000000 : ℝ)*X 0 2+(4203618227/10000000000 : ℝ)*X 1 0+(2783449559/5000000000 : ℝ)*X 1 1+(3184278627/10000000000 : ℝ)*X 1 2+(4203618227/10000000000 : ℝ)*X 2 0+(2783449559/5000000000 : ℝ)*X 2 1+(3184278627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39677544489082962212463/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19078023/25000000000000 : ℝ)*(base1) + (1548165821/100000000000000 : ℝ)*(base19) + (1435337243/100000000000000 : ℝ)*(base23) + (20841471/20000000000000 : ℝ)*(base24) + (349948217/100000000000000 : ℝ)*(upper3) + (601544649164391/100000000000000 : ℝ)*(major0) + (601544649164391/100000000000000 : ℝ)*(major1) + (601544649164391/100000000000000 : ℝ)*(major2) + (402688140856583/50000000000000 : ℝ)*(sp0) + (5033613125397/625000000000 : ℝ)*(sp1) + (805378108684743/100000000000000 : ℝ)*(sp2) + (2485666727731/625000000000 : ℝ)*(sp3) + (3442828267/100000000000000 : ℝ)*(sp4) + (2685736813/100000000000000 : ℝ)*(sp7) + (198854719242933/50000000000000 : ℝ)*(f.failure) + (805379648229341/100000000000000 : ℝ)*(f.sum) + (42737057754179/25000000000000000000000000000 : ℝ)*base65 + (269638333054179/50000000000000000000000000000 : ℝ)*base67 + (205607280404179/50000000000000000000000000000 : ℝ)*base69 + (173383024354179/50000000000000000000000000000 : ℝ)*base71 + (48039598554179/25000000000000000000000000000 : ℝ)*base73 + (315854260354179/50000000000000000000000000000 : ℝ)*base75 + (281164706704179/50000000000000000000000000000 : ℝ)*base77 + (96325313804179/50000000000000000000000000000 : ℝ)*base79 + (38434758070821/25000000000000000000000000000 : ℝ)*base82 + (4769151/2500000000000000000000 : ℝ)*base89 + (4769151/2500000000000000000000 : ℝ)*base91 + (4769151/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28722263714004068471847/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93343683/100000000000000 : ℝ)*(base1) + (729071053/50000000000000 : ℝ)*(base19) + (317764627/20000000000000 : ℝ)*(base23) + (2639769/800000000000 : ℝ)*(upper3) + (644947/2500000000000 : ℝ)*(upper5) + (126963265083721/20000000000000 : ℝ)*(major0) + (126963265083721/20000000000000 : ℝ)*(major1) + (126963265083721/20000000000000 : ℝ)*(major2) + (158069879/5000000000000 : ℝ)*(sp1) + (1552414383/50000000000000 : ℝ)*(sp2) + (424962822682737/50000000000000 : ℝ)*(sp4) + (169984186496421/20000000000000 : ℝ)*(sp5) + (84992085836989/10000000000000 : ℝ)*(sp6) + (419706813989971/100000000000000 : ℝ)*(sp7) + (209853453666827/50000000000000 : ℝ)*(f.failure) + (26560173500681/3125000000000 : ℝ)*(f.sum) + (7087643561051/5000000000000000000000000000 : ℝ)*base66 + (5109654466051/10000000000000000000000000000 : ℝ)*base68 + (16724451823949/10000000000000000000000000000 : ℝ)*base69 + (51251124626051/10000000000000000000000000000 : ℝ)*base72 + (490277021051/5000000000000000000000000000 : ℝ)*base74 + (56769122423949/10000000000000000000000000000 : ℝ)*base75 + (12202651836051/10000000000000000000000000000 : ℝ)*base78 + (10572283953949/10000000000000000000000000000 : ℝ)*base79 + (15988274028949/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (22725569/2500000000000000000000 : ℝ)*base89 + (22725569/2500000000000000000000 : ℝ)*base91 + (22725569/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1233_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (391/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2747/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1233_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1233_s1_0 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-412280979/2000000000 : ℝ)*x 0 + (709734247/1250000000 : ℝ)*x 1 + (5020750669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412280979/2000000000 : ℝ)^4213 ≤ (496590639027/4000000000000 : ℝ)^3189 := by
    have hnat : (412280979 : ℕ)^4213*4000000000000^3189 ≤ 496590639027^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412280979 2000000000 496590639027 4000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (709734247/1250000000 : ℝ)^4213 ≤ (47342791306159/100000000000000 : ℝ)^3189 := by
    have hnat : (709734247 : ℕ)^4213*100000000000000^3189 ≤ 47342791306159^3189*1250000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709734247 1250000000 47342791306159 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5020750669/10000000000 : ℝ)^4213 ≤ (157197041847/390625000000 : ℝ)^3189 := by
    have hnat : (5020750669 : ℕ)^4213*390625000000^3189 ≤ 157197041847^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020750669 10000000000 157197041847 390625000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412280979/2000000000 : ℝ), (709734247/1250000000 : ℝ), (5020750669/10000000000 : ℝ)] ![(496590639027/4000000000000 : ℝ), (47342791306159/100000000000000 : ℝ), (157197041847/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412280979/2000000000 : ℝ)|^4213 ≤ (496590639027/4000000000000 : ℝ)^3189
        have hw : |(-412280979/2000000000 : ℝ)|=(412280979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(709734247/1250000000 : ℝ)|^4213 ≤ (47342791306159/100000000000000 : ℝ)^3189
        have hw : |(709734247/1250000000 : ℝ)|=(709734247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5020750669/10000000000 : ℝ)|^4213 ≤ (157197041847/390625000000 : ℝ)^3189
        have hw : |(5020750669/10000000000 : ℝ)|=(5020750669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s1_1 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5414148199/10000000000 : ℝ)*x 0 + (-2414426189/10000000000 : ℝ)*x 1 + (5020750647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414148199/10000000000 : ℝ)^4213 ≤ (22229805372299/50000000000000 : ℝ)^3189 := by
    have hnat : (5414148199 : ℕ)^4213*50000000000000^3189 ≤ 22229805372299^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414148199 10000000000 22229805372299 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2414426189/10000000000 : ℝ)^4213 ≤ (15297946767377/100000000000000 : ℝ)^3189 := by
    have hnat : (2414426189 : ℕ)^4213*100000000000000^3189 ≤ 15297946767377^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2414426189 10000000000 15297946767377 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5020750647/10000000000 : ℝ)^4213 ≤ (321939539839/800000000000 : ℝ)^3189 := by
    have hnat : (5020750647 : ℕ)^4213*800000000000^3189 ≤ 321939539839^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020750647 10000000000 321939539839 800000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414148199/10000000000 : ℝ), (-2414426189/10000000000 : ℝ), (5020750647/10000000000 : ℝ)] ![(22229805372299/50000000000000 : ℝ), (15297946767377/100000000000000 : ℝ), (321939539839/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414148199/10000000000 : ℝ)|^4213 ≤ (22229805372299/50000000000000 : ℝ)^3189
        have hw : |(5414148199/10000000000 : ℝ)|=(5414148199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2414426189/10000000000 : ℝ)|^4213 ≤ (15297946767377/100000000000000 : ℝ)^3189
        have hw : |(-2414426189/10000000000 : ℝ)|=(2414426189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5020750647/10000000000 : ℝ)|^4213 ≤ (321939539839/800000000000 : ℝ)^3189
        have hw : |(5020750647/10000000000 : ℝ)|=(5020750647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s1_2 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707074081/5000000000 : ℝ)*x 0 + (2510375339/5000000000 : ℝ)*x 1 + (-2414426197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707074081/5000000000 : ℝ)^4213 ≤ (44459610343201/100000000000000 : ℝ)^3189 := by
    have hnat : (2707074081 : ℕ)^4213*100000000000000^3189 ≤ 44459610343201^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707074081 5000000000 44459610343201 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2510375339/5000000000 : ℝ)^4213 ≤ (10060610702033/25000000000000 : ℝ)^3189 := by
    have hnat : (2510375339 : ℕ)^4213*25000000000000^3189 ≤ 10060610702033^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510375339 5000000000 10060610702033 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2414426197/10000000000 : ℝ)^4213 ≤ (15297946834341/100000000000000 : ℝ)^3189 := by
    have hnat : (2414426197 : ℕ)^4213*100000000000000^3189 ≤ 15297946834341^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2414426197 10000000000 15297946834341 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707074081/5000000000 : ℝ), (2510375339/5000000000 : ℝ), (-2414426197/10000000000 : ℝ)] ![(44459610343201/100000000000000 : ℝ), (10060610702033/25000000000000 : ℝ), (15297946834341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707074081/5000000000 : ℝ)|^4213 ≤ (44459610343201/100000000000000 : ℝ)^3189
        have hw : |(2707074081/5000000000 : ℝ)|=(2707074081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2510375339/5000000000 : ℝ)|^4213 ≤ (10060610702033/25000000000000 : ℝ)^3189
        have hw : |(2510375339/5000000000 : ℝ)|=(2510375339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2414426197/10000000000 : ℝ)|^4213 ≤ (15297946834341/100000000000000 : ℝ)^3189
        have hw : |(-2414426197/10000000000 : ℝ)|=(2414426197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s1_3 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2154817647/5000000000 : ℝ)*x 0 + (1846907423/5000000000 : ℝ)*x 1 + (2512259813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154817647/5000000000 : ℝ)^4213 ≤ (16444776949283/50000000000000 : ℝ)^3189 := by
    have hnat : (2154817647 : ℕ)^4213*50000000000000^3189 ≤ 16444776949283^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154817647 5000000000 16444776949283 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1846907423/5000000000 : ℝ)^4213 ≤ (26828089293231/100000000000000 : ℝ)^3189 := by
    have hnat : (1846907423 : ℕ)^4213*100000000000000^3189 ≤ 26828089293231^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846907423 5000000000 26828089293231 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512259813/5000000000 : ℝ)^4213 ≤ (40282356793653/100000000000000 : ℝ)^3189 := by
    have hnat : (2512259813 : ℕ)^4213*100000000000000^3189 ≤ 40282356793653^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512259813 5000000000 40282356793653 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154817647/5000000000 : ℝ), (1846907423/5000000000 : ℝ), (2512259813/5000000000 : ℝ)] ![(16444776949283/50000000000000 : ℝ), (26828089293231/100000000000000 : ℝ), (40282356793653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154817647/5000000000 : ℝ)|^4213 ≤ (16444776949283/50000000000000 : ℝ)^3189
        have hw : |(2154817647/5000000000 : ℝ)|=(2154817647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1846907423/5000000000 : ℝ)|^4213 ≤ (26828089293231/100000000000000 : ℝ)^3189
        have hw : |(1846907423/5000000000 : ℝ)|=(1846907423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2512259813/5000000000 : ℝ)|^4213 ≤ (40282356793653/100000000000000 : ℝ)^3189
        have hw : |(2512259813/5000000000 : ℝ)|=(2512259813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s1_4 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1031046383/5000000000 : ℝ)*x 0 + (5029413399/10000000000 : ℝ)*x 1 + (5669045337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031046383/5000000000 : ℝ)^4213 ≤ (12420239189803/100000000000000 : ℝ)^3189 := by
    have hnat : (1031046383 : ℕ)^4213*100000000000000^3189 ≤ 12420239189803^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031046383 5000000000 12420239189803 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5029413399/10000000000 : ℝ)^4213 ≤ (10083549317319/25000000000000 : ℝ)^3189 := by
    have hnat : (5029413399 : ℕ)^4213*25000000000000^3189 ≤ 10083549317319^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5029413399 10000000000 10083549317319 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5669045337/10000000000 : ℝ)^4213 ≤ (9449112706609/20000000000000 : ℝ)^3189 := by
    have hnat : (5669045337 : ℕ)^4213*20000000000000^3189 ≤ 9449112706609^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669045337 10000000000 9449112706609 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1031046383/5000000000 : ℝ), (5029413399/10000000000 : ℝ), (5669045337/10000000000 : ℝ)] ![(12420239189803/100000000000000 : ℝ), (10083549317319/25000000000000 : ℝ), (9449112706609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1031046383/5000000000 : ℝ)|^4213 ≤ (12420239189803/100000000000000 : ℝ)^3189
        have hw : |(-1031046383/5000000000 : ℝ)|=(1031046383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5029413399/10000000000 : ℝ)|^4213 ≤ (10083549317319/25000000000000 : ℝ)^3189
        have hw : |(5029413399/10000000000 : ℝ)|=(5029413399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5669045337/10000000000 : ℝ)|^4213 ≤ (9449112706609/20000000000000 : ℝ)^3189
        have hw : |(5669045337/10000000000 : ℝ)|=(5669045337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s1_5 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2622462893/5000000000 : ℝ)*x 0 + (-1766130977/10000000000 : ℝ)*x 1 + (2834522797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622462893/5000000000 : ℝ)^4213 ≤ (42633068162067/100000000000000 : ℝ)^3189 := by
    have hnat : (2622462893 : ℕ)^4213*100000000000000^3189 ≤ 42633068162067^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622462893 5000000000 42633068162067 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1766130977/10000000000 : ℝ)^4213 ≤ (2530341365309/25000000000000 : ℝ)^3189 := by
    have hnat : (1766130977 : ℕ)^4213*25000000000000^3189 ≤ 2530341365309^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766130977 10000000000 2530341365309 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2834522797/5000000000 : ℝ)^4213 ≤ (2362278318131/5000000000000 : ℝ)^3189 := by
    have hnat : (2834522797 : ℕ)^4213*5000000000000^3189 ≤ 2362278318131^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2834522797 5000000000 2362278318131 5000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622462893/5000000000 : ℝ), (-1766130977/10000000000 : ℝ), (2834522797/5000000000 : ℝ)] ![(42633068162067/100000000000000 : ℝ), (2530341365309/25000000000000 : ℝ), (2362278318131/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622462893/5000000000 : ℝ)|^4213 ≤ (42633068162067/100000000000000 : ℝ)^3189
        have hw : |(2622462893/5000000000 : ℝ)|=(2622462893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1766130977/10000000000 : ℝ)|^4213 ≤ (2530341365309/25000000000000 : ℝ)^3189
        have hw : |(-1766130977/10000000000 : ℝ)|=(1766130977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2834522797/5000000000 : ℝ)|^4213 ≤ (2362278318131/5000000000000 : ℝ)^3189
        have hw : |(2834522797/5000000000 : ℝ)|=(2834522797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s1_6 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1311231527/2500000000 : ℝ)*x 0 + (5669046349/10000000000 : ℝ)*x 1 + (-883064711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311231527/2500000000 : ℝ)^4213 ≤ (10658267904967/25000000000000 : ℝ)^3189 := by
    have hnat : (1311231527 : ℕ)^4213*25000000000000^3189 ≤ 10658267904967^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311231527 2500000000 10658267904967 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5669046349/10000000000 : ℝ)^4213 ≤ (2952848417199/6250000000000 : ℝ)^3189 := by
    have hnat : (5669046349 : ℕ)^4213*6250000000000^3189 ≤ 2952848417199^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669046349 10000000000 2952848417199 6250000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883064711/5000000000 : ℝ)^4213 ≤ (632584605521/6250000000000 : ℝ)^3189 := by
    have hnat : (883064711 : ℕ)^4213*6250000000000^3189 ≤ 632584605521^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883064711 5000000000 632584605521 6250000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311231527/2500000000 : ℝ), (5669046349/10000000000 : ℝ), (-883064711/5000000000 : ℝ)] ![(10658267904967/25000000000000 : ℝ), (2952848417199/6250000000000 : ℝ), (632584605521/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311231527/2500000000 : ℝ)|^4213 ≤ (10658267904967/25000000000000 : ℝ)^3189
        have hw : |(1311231527/2500000000 : ℝ)|=(1311231527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5669046349/10000000000 : ℝ)|^4213 ≤ (2952848417199/6250000000000 : ℝ)^3189
        have hw : |(5669046349/10000000000 : ℝ)|=(5669046349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-883064711/5000000000 : ℝ)|^4213 ≤ (632584605521/6250000000000 : ℝ)^3189
        have hw : |(-883064711/5000000000 : ℝ)|=(883064711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s1_7 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2155513289/5000000000 : ℝ)*x 0 + (1001395611/2000000000 : ℝ)*x 1 + (3711691199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155513289/5000000000 : ℝ)^4213 ≤ (16451790899941/50000000000000 : ℝ)^3189 := by
    have hnat : (2155513289 : ℕ)^4213*50000000000000^3189 ≤ 16451790899941^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155513289 5000000000 16451790899941 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001395611/2000000000 : ℝ)^4213 ≤ (160386678217/400000000000 : ℝ)^3189 := by
    have hnat : (1001395611 : ℕ)^4213*400000000000^3189 ≤ 160386678217^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001395611 2000000000 160386678217 400000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3711691199/10000000000 : ℝ)^4213 ≤ (26999748629289/100000000000000 : ℝ)^3189 := by
    have hnat : (3711691199 : ℕ)^4213*100000000000000^3189 ≤ 26999748629289^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3711691199 10000000000 26999748629289 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155513289/5000000000 : ℝ), (1001395611/2000000000 : ℝ), (3711691199/10000000000 : ℝ)] ![(16451790899941/50000000000000 : ℝ), (160386678217/400000000000 : ℝ), (26999748629289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155513289/5000000000 : ℝ)|^4213 ≤ (16451790899941/50000000000000 : ℝ)^3189
        have hw : |(2155513289/5000000000 : ℝ)|=(2155513289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001395611/2000000000 : ℝ)|^4213 ≤ (160386678217/400000000000 : ℝ)^3189
        have hw : |(1001395611/2000000000 : ℝ)|=(1001395611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3711691199/10000000000 : ℝ)|^4213 ≤ (26999748629289/100000000000000 : ℝ)^3189
        have hw : |(3711691199/10000000000 : ℝ)|=(3711691199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1233_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2747/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (391/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (192/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20037/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2747/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (391/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2747/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (391/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2747/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (391/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2747/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (391/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2747/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (391/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2747/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (391/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (391/50000 : ℝ) ^ (8425/2048 : ℝ) ≤ (215346655933/100000000000000000000 : ℝ) := by
    have hpowers : (391/50000 : ℝ)^8425 ≤ (215346655933/100000000000000000000 : ℝ)^2048 := by
      have hnat : (391 : ℕ)^8425*100000000000000000000^2048 ≤ 215346655933^2048*50000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        391 50000 215346655933 100000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (391/50000 : ℝ)) (X := (215346655933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2747/10000 : ℝ) ^ (8425/2048 : ℝ) ≤ (49157959835109789/10000000000000000000 : ℝ) := by
    have hpowers : (2747/10000 : ℝ)^8425 ≤ (49157959835109789/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2747 : ℕ)^8425*10000000000000000000^2048 ≤ 49157959835109789^2048*10000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2747 10000 49157959835109789 10000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2747/10000 : ℝ)) (X := (49157959835109789/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000215346655933/50000000000000000000 : ℝ) ≤ (5000000005234777/5000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (50000000215346655933/50000000000000000000 : ℝ)^2048 ≤ (5000000005234777/5000000000000000 : ℝ)^8425 := by
      have hnat : (50000000215346655933 : ℕ)^2048*5000000000000000^8425 ≤ 5000000005234777^8425*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000215346655933 50000000000000000000 5000000005234777 5000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000005234777/5000000000000000 : ℝ)) (X := (50000000215346655933/50000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100491579813697753823/100000000000000000000 : ℝ) ≤ (5005963726090733/5000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (100491579813697753823/100000000000000000000 : ℝ)^2048 ≤ (5005963726090733/5000000000000000 : ℝ)^8425 := by
      have hnat : (100491579813697753823 : ℕ)^2048*5000000000000000^8425 ≤ 5005963726090733^8425*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100491579813697753823 100000000000000000000 5005963726090733 5000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005963726090733/5000000000000000 : ℝ)) (X := (100491579813697753823/100000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5049157959835109789/5000000000000000000 : ℝ) ≤ (5011927446946689/5000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (5049157959835109789/5000000000000000000 : ℝ)^2048 ≤ (5011927446946689/5000000000000000 : ℝ)^8425 := by
      have hnat : (5049157959835109789 : ℕ)^2048*5000000000000000^8425 ≤ 5011927446946689^8425*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5049157959835109789 5000000000000000000 5011927446946689 5000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011927446946689/5000000000000000 : ℝ)) (X := (5049157959835109789/5000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(215346655933/100000000000000000000 : ℝ) ≤ ((8339417055017938337/8340000000000000000 : ℝ)+2*(1490930213989/333600000000000 : ℝ)*(391/50000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (8339417055017938337/8340000000000000000 : ℝ)+2*(1490930213989/333600000000000 : ℝ)*(391/50000 : ℝ)=(5000000005234777/5000000000000000 : ℝ) by norm_num, show 1+2*(215346655933/100000000000000000000 : ℝ)=(50000000215346655933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(49157959835109789/10000000000000000000 : ℝ)+(215346655933/100000000000000000000 : ℝ) ≤ ((8339417055017938337/8340000000000000000 : ℝ)+(1490930213989/333600000000000 : ℝ)*((2747/10000 : ℝ)+(391/50000 : ℝ)))^(8425/2048 : ℝ) := by
    rw [show (8339417055017938337/8340000000000000000 : ℝ)+(1490930213989/333600000000000 : ℝ)*((2747/10000 : ℝ)+(391/50000 : ℝ))=(5005963726090733/5000000000000000 : ℝ) by norm_num, show 1+(49157959835109789/10000000000000000000 : ℝ)+(215346655933/100000000000000000000 : ℝ)=(100491579813697753823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(49157959835109789/10000000000000000000 : ℝ) ≤ ((8339417055017938337/8340000000000000000 : ℝ)+2*(1490930213989/333600000000000 : ℝ)*(2747/10000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (8339417055017938337/8340000000000000000 : ℝ)+2*(1490930213989/333600000000000 : ℝ)*(2747/10000 : ℝ)=(5011927446946689/5000000000000000 : ℝ) by norm_num, show 1+2*(49157959835109789/10000000000000000000 : ℝ)=(5049157959835109789/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8339417055017938337/8340000000000000000 : ℝ)*(X 1 0+X 2 0)+(1490930213989/333600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (391/50000 : ℝ)) (hi := (2747/10000 : ℝ)) (c := (8339417055017938337/8340000000000000000 : ℝ)) (alpha := (1490930213989/333600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8339417055017938337/8340000000000000000 : ℝ)*(X 0 1+X 2 1)+(1490930213989/333600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (391/50000 : ℝ)) (hi := (2747/10000 : ℝ)) (c := (8339417055017938337/8340000000000000000 : ℝ)) (alpha := (1490930213989/333600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8339417055017938337/8340000000000000000 : ℝ)*(X 0 2+X 1 2)+(1490930213989/333600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (391/50000 : ℝ)) (hi := (2747/10000 : ℝ)) (c := (8339417055017938337/8340000000000000000 : ℝ)) (alpha := (1490930213989/333600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-412280979/2000000000 : ℝ)*X 0 0+(709734247/1250000000 : ℝ)*X 0 1+(5020750669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5414148199/10000000000 : ℝ)*X 1 0+(-2414426189/10000000000 : ℝ)*X 1 1+(5020750647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2707074081/5000000000 : ℝ)*X 2 0+(2510375339/5000000000 : ℝ)*X 2 1+(-2414426197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154817647/5000000000 : ℝ)*X 0 0+(1846907423/5000000000 : ℝ)*X 0 1+(2512259813/5000000000 : ℝ)*X 0 2+(2154817647/5000000000 : ℝ)*X 1 0+(1846907423/5000000000 : ℝ)*X 1 1+(2512259813/5000000000 : ℝ)*X 1 2+(2154817647/5000000000 : ℝ)*X 2 0+(1846907423/5000000000 : ℝ)*X 2 1+(2512259813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1031046383/5000000000 : ℝ)*X 0 0+(5029413399/10000000000 : ℝ)*X 0 1+(5669045337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622462893/5000000000 : ℝ)*X 1 0+(-1766130977/10000000000 : ℝ)*X 1 1+(2834522797/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1311231527/2500000000 : ℝ)*X 2 0+(5669046349/10000000000 : ℝ)*X 2 1+(-883064711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155513289/5000000000 : ℝ)*X 0 0+(1001395611/2000000000 : ℝ)*X 0 1+(3711691199/10000000000 : ℝ)*X 0 2+(2155513289/5000000000 : ℝ)*X 1 0+(1001395611/2000000000 : ℝ)*X 1 1+(3711691199/10000000000 : ℝ)*X 1 2+(2155513289/5000000000 : ℝ)*X 2 0+(1001395611/2000000000 : ℝ)*X 2 1+(3711691199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10668066547494083998303779/3475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3216641/10000000000000 : ℝ)*(base1) + (5186139/800000000000 : ℝ)*(base19) + (318933769/50000000000000 : ℝ)*(base23) + (571251/800000000000 : ℝ)*(upper3) + (65630581/100000000000000 : ℝ)*(upper5) + (28415957730111/2500000000000 : ℝ)*(major0) + (28415957730111/2500000000000 : ℝ)*(major1) + (28415957730111/2500000000000 : ℝ)*(major2) + (304357593271959/20000000000000 : ℝ)*(sp0) + (38044771568993/2500000000000 : ℝ)*(sp1) + (760895436579779/50000000000000 : ℝ)*(sp2) + (150296639207111/20000000000000 : ℝ)*(sp3) + (357683371/10000000000000 : ℝ)*(sp4) + (888424117/50000000000000 : ℝ)*(sp7) + (751485005050197/100000000000000 : ℝ)*(f.failure) + (190223938878387/12500000000000 : ℝ)*(f.sum) + (5201768291/2780000000000000000000000 : ℝ)*base66 + (35081835395713469/6950000000000000000000000000000 : ℝ)*base67 + (47673647244263469/6950000000000000000000000000000 : ℝ)*base69 + (33500320556313469/6950000000000000000000000000000 : ℝ)*base71 + (5270330113/139000000000000000000000000 : ℝ)*base73 + (66753651025013469/6950000000000000000000000000000 : ℝ)*base75 + (20499038150113469/6950000000000000000000000000000 : ℝ)*base77 + (19245529853413469/6950000000000000000000000000000 : ℝ)*base79 + (107072991863/139000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (59299041/5000000000000000000000 : ℝ)*base90 + (59299041/5000000000000000000000 : ℝ)*base92 + (59299041/5000000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (409924154959870809210016587/139000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40258327/3125000000000 : ℝ)*(base19) + (1779406947/100000000000000 : ℝ)*(base23) + (3454317/3125000000000 : ℝ)*(upper2) + (57654901/25000000000000 : ℝ)*(upper3) + (77789989/100000000000000 : ℝ)*(upper5) + (1167714031162251/100000000000000 : ℝ)*(major0) + (1167714031162251/100000000000000 : ℝ)*(major1) + (1167714031162251/100000000000000 : ℝ)*(major2) + (177148361/3125000000000 : ℝ)*(sp1) + (11384330101/100000000000000 : ℝ)*(sp2) + (781698669356223/50000000000000 : ℝ)*(sp4) + (1563390381698431/100000000000000 : ℝ)*(sp5) + (781692087487699/50000000000000 : ℝ)*(sp6) + (772030625308897/100000000000000 : ℝ)*(sp7) + (772030625308897/100000000000000 : ℝ)*(f.failure) + (781698669356223/50000000000000 : ℝ)*(f.sum) + (36602506518387/5560000000000000000000000000 : ℝ)*base66 + (790626413944969471/278000000000000000000000000000000 : ℝ)*base68 + (1152943166607030529/278000000000000000000000000000000 : ℝ)*base69 + (362852743842969471/278000000000000000000000000000000 : ℝ)*base72 + (13580326218787/5560000000000000000000000000 : ℝ)*base74 + (598669463360969471/278000000000000000000000000000000 : ℝ)*base76 + (1665064439338969471/278000000000000000000000000000000 : ℝ)*base78 + (1142080619627030529/278000000000000000000000000000000 : ℝ)*base79 + (4305482997587/5560000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (14929859/5000000000000000000000 : ℝ)*base89 + (14929859/5000000000000000000000 : ℝ)*base91 + (14929859/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1233_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2747/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (391/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (192/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20037/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1233_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1233_s2_0 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-527475051/2500000000 : ℝ)*x 0 + (1098866001/2000000000 : ℝ)*x 1 + (5173375287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527475051/2500000000 : ℝ)^4213 ≤ (12802059779161/100000000000000 : ℝ)^3189 := by
    have hnat : (527475051 : ℕ)^4213*100000000000000^3189 ≤ 12802059779161^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527475051 2500000000 12802059779161 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098866001/2000000000 : ℝ)^4213 ≤ (22665764996531/50000000000000 : ℝ)^3189 := by
    have hnat : (1098866001 : ℕ)^4213*50000000000000^3189 ≤ 22665764996531^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098866001 2000000000 22665764996531 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5173375287/10000000000 : ℝ)^4213 ≤ (2093320510733/5000000000000 : ℝ)^3189 := by
    have hnat : (5173375287 : ℕ)^4213*5000000000000^3189 ≤ 2093320510733^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173375287 10000000000 2093320510733 5000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527475051/2500000000 : ℝ), (1098866001/2000000000 : ℝ), (5173375287/10000000000 : ℝ)] ![(12802059779161/100000000000000 : ℝ), (22665764996531/50000000000000 : ℝ), (2093320510733/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527475051/2500000000 : ℝ)|^4213 ≤ (12802059779161/100000000000000 : ℝ)^3189
        have hw : |(-527475051/2500000000 : ℝ)|=(527475051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098866001/2000000000 : ℝ)|^4213 ≤ (22665764996531/50000000000000 : ℝ)^3189
        have hw : |(1098866001/2000000000 : ℝ)|=(1098866001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5173375287/10000000000 : ℝ)|^4213 ≤ (2093320510733/5000000000000 : ℝ)^3189
        have hw : |(5173375287/10000000000 : ℝ)|=(5173375287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s2_1 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074010517/2000000000 : ℝ)*x 0 + (-2276204761/10000000000 : ℝ)*x 1 + (2586687621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074010517/2000000000 : ℝ)^4213 ≤ (43981863119879/100000000000000 : ℝ)^3189 := by
    have hnat : (1074010517 : ℕ)^4213*100000000000000^3189 ≤ 43981863119879^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074010517 2000000000 43981863119879 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276204761/10000000000 : ℝ)^4213 ≤ (1415172711911/10000000000000 : ℝ)^3189 := by
    have hnat : (2276204761 : ℕ)^4213*10000000000000^3189 ≤ 1415172711911^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276204761 10000000000 1415172711911 10000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586687621/5000000000 : ℝ)^4213 ≤ (20933204866777/50000000000000 : ℝ)^3189 := by
    have hnat : (2586687621 : ℕ)^4213*50000000000000^3189 ≤ 20933204866777^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586687621 5000000000 20933204866777 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074010517/2000000000 : ℝ), (-2276204761/10000000000 : ℝ), (2586687621/5000000000 : ℝ)] ![(43981863119879/100000000000000 : ℝ), (1415172711911/10000000000000 : ℝ), (20933204866777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074010517/2000000000 : ℝ)|^4213 ≤ (43981863119879/100000000000000 : ℝ)^3189
        have hw : |(1074010517/2000000000 : ℝ)|=(1074010517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2276204761/10000000000 : ℝ)|^4213 ≤ (1415172711911/10000000000000 : ℝ)^3189
        have hw : |(-2276204761/10000000000 : ℝ)|=(2276204761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2586687621/5000000000 : ℝ)|^4213 ≤ (20933204866777/50000000000000 : ℝ)^3189
        have hw : |(2586687621/5000000000 : ℝ)|=(2586687621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s2_2 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370052407/10000000000 : ℝ)*x 0 + (5173375397/10000000000 : ℝ)*x 1 + (-569051199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370052407/10000000000 : ℝ)^4213 ≤ (21990930596949/50000000000000 : ℝ)^3189 := by
    have hnat : (5370052407 : ℕ)^4213*50000000000000^3189 ≤ 21990930596949^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370052407 10000000000 21990930596949 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5173375397/10000000000 : ℝ)^4213 ≤ (20933205695349/50000000000000 : ℝ)^3189 := by
    have hnat : (5173375397 : ℕ)^4213*50000000000000^3189 ≤ 20933205695349^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173375397 10000000000 20933205695349 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569051199/2500000000 : ℝ)^4213 ≤ (14151727406587/100000000000000 : ℝ)^3189 := by
    have hnat : (569051199 : ℕ)^4213*100000000000000^3189 ≤ 14151727406587^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569051199 2500000000 14151727406587 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370052407/10000000000 : ℝ), (5173375397/10000000000 : ℝ), (-569051199/2500000000 : ℝ)] ![(21990930596949/50000000000000 : ℝ), (20933205695349/50000000000000 : ℝ), (14151727406587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370052407/10000000000 : ℝ)|^4213 ≤ (21990930596949/50000000000000 : ℝ)^3189
        have hw : |(5370052407/10000000000 : ℝ)|=(5370052407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5173375397/10000000000 : ℝ)|^4213 ≤ (20933205695349/50000000000000 : ℝ)^3189
        have hw : |(5173375397/10000000000 : ℝ)|=(5173375397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-569051199/2500000000 : ℝ)|^4213 ≤ (14151727406587/100000000000000 : ℝ)^3189
        have hw : |(-569051199/2500000000 : ℝ)|=(569051199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s2_3 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4343114321/10000000000 : ℝ)*x 0 + (4029940379/10000000000 : ℝ)*x 1 + (187195543/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343114321/10000000000 : ℝ)^4213 ≤ (664550313937/2000000000000 : ℝ)^3189 := by
    have hnat : (4343114321 : ℕ)^4213*2000000000000^3189 ≤ 664550313937^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343114321 10000000000 664550313937 2000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4029940379/10000000000 : ℝ)^4213 ≤ (30099446583249/100000000000000 : ℝ)^3189 := by
    have hnat : (4029940379 : ℕ)^4213*100000000000000^3189 ≤ 30099446583249^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029940379 10000000000 30099446583249 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187195543/400000000 : ℝ)^4213 ≤ (9168259425007/25000000000000 : ℝ)^3189 := by
    have hnat : (187195543 : ℕ)^4213*25000000000000^3189 ≤ 9168259425007^3189*400000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187195543 400000000 9168259425007 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343114321/10000000000 : ℝ), (4029940379/10000000000 : ℝ), (187195543/400000000 : ℝ)] ![(664550313937/2000000000000 : ℝ), (30099446583249/100000000000000 : ℝ), (9168259425007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343114321/10000000000 : ℝ)|^4213 ≤ (664550313937/2000000000000 : ℝ)^3189
        have hw : |(4343114321/10000000000 : ℝ)|=(4343114321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4029940379/10000000000 : ℝ)|^4213 ≤ (30099446583249/100000000000000 : ℝ)^3189
        have hw : |(4029940379/10000000000 : ℝ)|=(4029940379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187195543/400000000 : ℝ)|^4213 ≤ (9168259425007/25000000000000 : ℝ)^3189
        have hw : |(187195543/400000000 : ℝ)|=(187195543/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s2_4 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-527495129/2500000000 : ℝ)*x 0 + (103509029/200000000 : ℝ)*x 1 + (2746117131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527495129/2500000000 : ℝ)^4213 ≤ (12802703559889/100000000000000 : ℝ)^3189 := by
    have hnat : (527495129 : ℕ)^4213*100000000000000^3189 ≤ 12802703559889^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527495129 2500000000 12802703559889 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103509029/200000000 : ℝ)^4213 ≤ (8377721686473/20000000000000 : ℝ)^3189 := by
    have hnat : (103509029 : ℕ)^4213*20000000000000^3189 ≤ 8377721686473^3189*200000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103509029 200000000 8377721686473 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746117131/5000000000 : ℝ)^4213 ≤ (45308687999697/100000000000000 : ℝ)^3189 := by
    have hnat : (2746117131 : ℕ)^4213*100000000000000^3189 ≤ 45308687999697^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746117131 5000000000 45308687999697 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527495129/2500000000 : ℝ), (103509029/200000000 : ℝ), (2746117131/5000000000 : ℝ)] ![(12802703559889/100000000000000 : ℝ), (8377721686473/20000000000000 : ℝ), (45308687999697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527495129/2500000000 : ℝ)|^4213 ≤ (12802703559889/100000000000000 : ℝ)^3189
        have hw : |(-527495129/2500000000 : ℝ)|=(527495129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103509029/200000000 : ℝ)|^4213 ≤ (8377721686473/20000000000000 : ℝ)^3189
        have hw : |(103509029/200000000 : ℝ)|=(103509029/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746117131/5000000000 : ℝ)|^4213 ≤ (45308687999697/100000000000000 : ℝ)^3189
        have hw : |(2746117131/5000000000 : ℝ)|=(2746117131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s2_5 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66101691/125000000 : ℝ)*x 0 + (-1957345549/10000000000 : ℝ)*x 1 + (5492234303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66101691/125000000 : ℝ)^4213 ≤ (43097686502703/100000000000000 : ℝ)^3189 := by
    have hnat : (66101691 : ℕ)^4213*100000000000000^3189 ≤ 43097686502703^3189*125000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66101691 125000000 43097686502703 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1957345549/10000000000 : ℝ)^4213 ≤ (2318725006487/20000000000000 : ℝ)^3189 := by
    have hnat : (1957345549 : ℕ)^4213*20000000000000^3189 ≤ 2318725006487^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957345549 10000000000 2318725006487 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492234303/10000000000 : ℝ)^4213 ≤ (45308688446539/100000000000000 : ℝ)^3189 := by
    have hnat : (5492234303 : ℕ)^4213*100000000000000^3189 ≤ 45308688446539^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492234303 10000000000 45308688446539 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66101691/125000000 : ℝ), (-1957345549/10000000000 : ℝ), (5492234303/10000000000 : ℝ)] ![(43097686502703/100000000000000 : ℝ), (2318725006487/20000000000000 : ℝ), (45308688446539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66101691/125000000 : ℝ)|^4213 ≤ (43097686502703/100000000000000 : ℝ)^3189
        have hw : |(66101691/125000000 : ℝ)|=(66101691/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1957345549/10000000000 : ℝ)|^4213 ≤ (2318725006487/20000000000000 : ℝ)^3189
        have hw : |(-1957345549/10000000000 : ℝ)|=(1957345549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492234303/10000000000 : ℝ)|^4213 ≤ (45308688446539/100000000000000 : ℝ)^3189
        have hw : |(5492234303/10000000000 : ℝ)|=(5492234303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s2_6 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165254233/312500000 : ℝ)*x 0 + (5492234369/10000000000 : ℝ)*x 1 + (-391469043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165254233/312500000 : ℝ)^4213 ≤ (43097688397667/100000000000000 : ℝ)^3189 := by
    have hnat : (165254233 : ℕ)^4213*100000000000000^3189 ≤ 43097688397667^3189*312500000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165254233 312500000 43097688397667 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492234369/10000000000 : ℝ)^4213 ≤ (11327172291461/25000000000000 : ℝ)^3189 := by
    have hnat : (5492234369 : ℕ)^4213*25000000000000^3189 ≤ 11327172291461^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492234369 10000000000 11327172291461 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391469043/2000000000 : ℝ)^4213 ≤ (11593622418859/100000000000000 : ℝ)^3189 := by
    have hnat : (391469043 : ℕ)^4213*100000000000000^3189 ≤ 11593622418859^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391469043 2000000000 11593622418859 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165254233/312500000 : ℝ), (5492234369/10000000000 : ℝ), (-391469043/2000000000 : ℝ)] ![(43097688397667/100000000000000 : ℝ), (11327172291461/25000000000000 : ℝ), (11593622418859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165254233/312500000 : ℝ)|^4213 ≤ (43097688397667/100000000000000 : ℝ)^3189
        have hw : |(165254233/312500000 : ℝ)|=(165254233/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492234369/10000000000 : ℝ)|^4213 ≤ (11327172291461/25000000000000 : ℝ)^3189
        have hw : |(5492234369/10000000000 : ℝ)|=(5492234369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391469043/2000000000 : ℝ)|^4213 ≤ (11593622418859/100000000000000 : ℝ)^3189
        have hw : |(-391469043/2000000000 : ℝ)|=(391469043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s2_7 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434327641/1000000000 : ℝ)*x 0 + (4675684429/10000000000 : ℝ)*x 1 + (806836783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434327641/1000000000 : ℝ)^4213 ≤ (33229153982759/100000000000000 : ℝ)^3189 := by
    have hnat : (434327641 : ℕ)^4213*100000000000000^3189 ≤ 33229153982759^3189*1000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434327641 1000000000 33229153982759 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4675684429/10000000000 : ℝ)^4213 ≤ (36629520249363/100000000000000 : ℝ)^3189 := by
    have hnat : (4675684429 : ℕ)^4213*100000000000000^3189 ≤ 36629520249363^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4675684429 10000000000 36629520249363 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806836783/2000000000 : ℝ)^4213 ≤ (30141325758387/100000000000000 : ℝ)^3189 := by
    have hnat : (806836783 : ℕ)^4213*100000000000000^3189 ≤ 30141325758387^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806836783 2000000000 30141325758387 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434327641/1000000000 : ℝ), (4675684429/10000000000 : ℝ), (806836783/2000000000 : ℝ)] ![(33229153982759/100000000000000 : ℝ), (36629520249363/100000000000000 : ℝ), (30141325758387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434327641/1000000000 : ℝ)|^4213 ≤ (33229153982759/100000000000000 : ℝ)^3189
        have hw : |(434327641/1000000000 : ℝ)|=(434327641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4675684429/10000000000 : ℝ)|^4213 ≤ (36629520249363/100000000000000 : ℝ)^3189
        have hw : |(4675684429/10000000000 : ℝ)|=(4675684429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806836783/2000000000 : ℝ)|^4213 ≤ (30141325758387/100000000000000 : ℝ)^3189
        have hw : |(806836783/2000000000 : ℝ)|=(806836783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1233_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (192/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (9463/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16247/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (192/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (192/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (192/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (192/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (192/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (192/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (192/3125 : ℝ) ^ (8425/2048 : ℝ) ≤ (103745075201213/10000000000000000000 : ℝ) := by
    have hpowers : (192/3125 : ℝ)^8425 ≤ (103745075201213/10000000000000000000 : ℝ)^2048 := by
      have hnat : (192 : ℕ)^8425*10000000000000000000^2048 ≤ 103745075201213^2048*3125^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        192 3125 103745075201213 10000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (192/3125 : ℝ)) (X := (103745075201213/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20037/100000 : ℝ) ^ (8425/2048 : ℝ) ≤ (67122887447467547/50000000000000000000 : ℝ) := by
    have hpowers : (20037/100000 : ℝ)^8425 ≤ (67122887447467547/50000000000000000000 : ℝ)^2048 := by
      have hnat : (20037 : ℕ)^8425*50000000000000000000^2048 ≤ 67122887447467547^2048*100000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20037 100000 67122887447467547 50000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20037/100000 : ℝ)) (X := (67122887447467547/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000103745075201213/5000000000000000000 : ℝ) ≤ (10000050437565719/10000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (5000103745075201213/5000000000000000000 : ℝ)^2048 ≤ (10000050437565719/10000000000000000 : ℝ)^8425 := by
      have hnat : (5000103745075201213 : ℕ)^2048*10000000000000000^8425 ≤ 10000050437565719^8425*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000103745075201213 5000000000000000000 10000050437565719 10000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000050437565719/10000000000000000 : ℝ)) (X := (5000103745075201213/5000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12516910403205868403/12500000000000000000 : ℝ) ≤ (10003286864175243/10000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (12516910403205868403/12500000000000000000 : ℝ)^2048 ≤ (10003286864175243/10000000000000000 : ℝ)^8425 := by
      have hnat : (12516910403205868403 : ℕ)^2048*10000000000000000^8425 ≤ 10003286864175243^8425*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12516910403205868403 12500000000000000000 10003286864175243 10000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003286864175243/10000000000000000 : ℝ)) (X := (12516910403205868403/12500000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25067122887447467547/25000000000000000000 : ℝ) ≤ (10006523290784767/10000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (25067122887447467547/25000000000000000000 : ℝ)^2048 ≤ (10006523290784767/10000000000000000 : ℝ)^8425 := by
      have hnat : (25067122887447467547 : ℕ)^2048*10000000000000000^8425 ≤ 10006523290784767^8425*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25067122887447467547 25000000000000000000 10006523290784767 10000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006523290784767/10000000000000000 : ℝ)) (X := (25067122887447467547/25000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(103745075201213/10000000000000000000 : ℝ) ≤ ((9259395434594846877/9262000000000000000 : ℝ)+2*(809106652381/347325000000000 : ℝ)*(192/3125 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (9259395434594846877/9262000000000000000 : ℝ)+2*(809106652381/347325000000000 : ℝ)*(192/3125 : ℝ)=(10000050437565719/10000000000000000 : ℝ) by norm_num, show 1+2*(103745075201213/10000000000000000000 : ℝ)=(5000103745075201213/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(67122887447467547/50000000000000000000 : ℝ)+(103745075201213/10000000000000000000 : ℝ) ≤ ((9259395434594846877/9262000000000000000 : ℝ)+(809106652381/347325000000000 : ℝ)*((20037/100000 : ℝ)+(192/3125 : ℝ)))^(8425/2048 : ℝ) := by
    rw [show (9259395434594846877/9262000000000000000 : ℝ)+(809106652381/347325000000000 : ℝ)*((20037/100000 : ℝ)+(192/3125 : ℝ))=(10003286864175243/10000000000000000 : ℝ) by norm_num, show 1+(67122887447467547/50000000000000000000 : ℝ)+(103745075201213/10000000000000000000 : ℝ)=(12516910403205868403/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(67122887447467547/50000000000000000000 : ℝ) ≤ ((9259395434594846877/9262000000000000000 : ℝ)+2*(809106652381/347325000000000 : ℝ)*(20037/100000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (9259395434594846877/9262000000000000000 : ℝ)+2*(809106652381/347325000000000 : ℝ)*(20037/100000 : ℝ)=(10006523290784767/10000000000000000 : ℝ) by norm_num, show 1+2*(67122887447467547/50000000000000000000 : ℝ)=(25067122887447467547/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9259395434594846877/9262000000000000000 : ℝ)*(X 1 0+X 2 0)+(809106652381/347325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (192/3125 : ℝ)) (hi := (20037/100000 : ℝ)) (c := (9259395434594846877/9262000000000000000 : ℝ)) (alpha := (809106652381/347325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9259395434594846877/9262000000000000000 : ℝ)*(X 0 1+X 2 1)+(809106652381/347325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (192/3125 : ℝ)) (hi := (20037/100000 : ℝ)) (c := (9259395434594846877/9262000000000000000 : ℝ)) (alpha := (809106652381/347325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9259395434594846877/9262000000000000000 : ℝ)*(X 0 2+X 1 2)+(809106652381/347325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (192/3125 : ℝ)) (hi := (20037/100000 : ℝ)) (c := (9259395434594846877/9262000000000000000 : ℝ)) (alpha := (809106652381/347325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-527475051/2500000000 : ℝ)*X 0 0+(1098866001/2000000000 : ℝ)*X 0 1+(5173375287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074010517/2000000000 : ℝ)*X 1 0+(-2276204761/10000000000 : ℝ)*X 1 1+(2586687621/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370052407/10000000000 : ℝ)*X 2 0+(5173375397/10000000000 : ℝ)*X 2 1+(-569051199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4343114321/10000000000 : ℝ)*X 0 0+(4029940379/10000000000 : ℝ)*X 0 1+(187195543/400000000 : ℝ)*X 0 2+(4343114321/10000000000 : ℝ)*X 1 0+(4029940379/10000000000 : ℝ)*X 1 1+(187195543/400000000 : ℝ)*X 1 2+(4343114321/10000000000 : ℝ)*X 2 0+(4029940379/10000000000 : ℝ)*X 2 1+(187195543/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-527495129/2500000000 : ℝ)*X 0 0+(103509029/200000000 : ℝ)*X 0 1+(2746117131/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66101691/125000000 : ℝ)*X 1 0+(-1957345549/10000000000 : ℝ)*X 1 1+(5492234303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165254233/312500000 : ℝ)*X 2 0+(5492234369/10000000000 : ℝ)*X 2 1+(-391469043/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434327641/1000000000 : ℝ)*X 0 0+(4675684429/10000000000 : ℝ)*X 0 1+(806836783/2000000000 : ℝ)*X 0 2+(434327641/1000000000 : ℝ)*X 1 0+(4675684429/10000000000 : ℝ)*X 1 1+(806836783/2000000000 : ℝ)*X 1 2+(434327641/1000000000 : ℝ)*X 2 0+(4675684429/10000000000 : ℝ)*X 2 1+(806836783/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (151066967445380309977302463/57887500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29465413/6250000000000 : ℝ)*(base19) + (13083387/4000000000000 : ℝ)*(base23) + (2206343/10000000000000 : ℝ)*(lower2) + (101952243/100000000000000 : ℝ)*(upper3) + (11086617/50000000000000 : ℝ)*(upper5) + (290893881606491/12500000000000 : ℝ)*(major0) + (290893881606491/12500000000000 : ℝ)*(major1) + (290893881606491/12500000000000 : ℝ)*(major2) + (311570958880883/10000000000000 : ℝ)*(sp0) + (623142523321867/20000000000000 : ℝ)*(sp1) + (778928190242817/25000000000000 : ℝ)*(sp2) + (153858625148937/10000000000000 : ℝ)*(sp3) + (1749623557/50000000000000 : ℝ)*(sp4) + (2679169711/100000000000000 : ℝ)*(sp7) + (38464723266477/2500000000000 : ℝ)*(f.failure) + (3115713088055943/100000000000000 : ℝ)*(f.sum) + (14517250529377/4341562500000000000000000000 : ℝ)*base65 + (4946445182131659179/347325000000000000000000000000000 : ℝ)*base68 + (3992513490100209179/347325000000000000000000000000000 : ℝ)*base70 + (603877369369359179/347325000000000000000000000000000 : ℝ)*base72 + (181293904627369/34732500000000000000000000000 : ℝ)*base74 + (3322273488321609179/347325000000000000000000000000000 : ℝ)*base76 + (614075213774184179/347325000000000000000000000000000 : ℝ)*base78 + (2430955659926109179/347325000000000000000000000000000 : ℝ)*base80 + (71473030959683/69465000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (225881/125000000000000000000 : ℝ)*base90 + (225881/125000000000000000000 : ℝ)*base92 + (225881/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1875185454371184116454148753/231550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1003800013/50000000000000 : ℝ)*(base19) + (1123174967/50000000000000 : ℝ)*(base23) + (24487353/100000000000000 : ℝ)*(upper2) + (66500589/25000000000000 : ℝ)*(upper3) + (32186251/20000000000000 : ℝ)*(upper5) + (1178895478039063/50000000000000 : ℝ)*(major0) + (1178895478039063/50000000000000 : ℝ)*(major1) + (1178895478039063/50000000000000 : ℝ)*(major2) + (5111343783/25000000000000 : ℝ)*(sp1) + (26086338369/100000000000000 : ℝ)*(sp2) + (631347046307481/20000000000000 : ℝ)*(sp4) + (3156712778562247/100000000000000 : ℝ)*(sp5) + (1578353449424551/50000000000000 : ℝ)*(sp6) + (1558846410672043/100000000000000 : ℝ)*(sp7) + (1558846410672043/100000000000000 : ℝ)*(f.failure) + (631347046307481/20000000000000 : ℝ)*(f.sum) + (79980410670113/34732500000000000000000000000 : ℝ)*base66 + (1503127114006808753/1389300000000000000000000000000000 : ℝ)*base67 + (3844222952682591247/1389300000000000000000000000000000 : ℝ)*base70 + (1473573607844091247/1389300000000000000000000000000000 : ℝ)*base72 + (1532584612123/542695312500000000000000000 : ℝ)*base73 + (1912916281460091247/1389300000000000000000000000000000 : ℝ)*base76 + (5171761836326408753/1389300000000000000000000000000000 : ℝ)*base77 + (1434418365766491247/1389300000000000000000000000000000 : ℝ)*base80 + (331832447023291/69465000000000000000000000000 : ℝ)*base82 + (7291679/5000000000000000000000 : ℝ)*base90 + (7291679/5000000000000000000000 : ℝ)*base92 + (7291679/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1233_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (192/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9463/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16247/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1233_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1233_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9463/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16247/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1233_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1233_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1233_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9463/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16247/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1233_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
