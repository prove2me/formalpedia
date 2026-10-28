-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1072_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:11:02.664994+00:00
-- url     : https://prove2.me/submissions/b3b738a3-273c-4110-b8f8-08893f7cf53f

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
theorem support_rectangle_w1072_s0_0 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914164779/10000000000 : ℝ)*x 0 + (6070650869/10000000000 : ℝ)*x 1 + (1192888979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914164779/10000000000 : ℝ)^8265 ≤ (11103232318881/100000000000000 : ℝ)^6217 := by
    have hnat : (1914164779 : ℕ)^8265*100000000000000^6217 ≤ 11103232318881^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914164779 10000000000 11103232318881 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6070650869/10000000000 : ℝ)^8265 ≤ (257512765991/500000000000 : ℝ)^6217 := by
    have hnat : (6070650869 : ℕ)^8265*500000000000^6217 ≤ 257512765991^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6070650869 10000000000 257512765991 500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192888979/2500000000 : ℝ)^8265 ≤ (3739421446371/10000000000000 : ℝ)^6217 := by
    have hnat : (1192888979 : ℕ)^8265*10000000000000^6217 ≤ 3739421446371^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192888979 2500000000 3739421446371 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914164779/10000000000 : ℝ), (6070650869/10000000000 : ℝ), (1192888979/2500000000 : ℝ)] ![(11103232318881/100000000000000 : ℝ), (257512765991/500000000000 : ℝ), (3739421446371/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914164779/10000000000 : ℝ)|^8265 ≤ (11103232318881/100000000000000 : ℝ)^6217
        have hw : |(-1914164779/10000000000 : ℝ)|=(1914164779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6070650869/10000000000 : ℝ)|^8265 ≤ (257512765991/500000000000 : ℝ)^6217
        have hw : |(6070650869/10000000000 : ℝ)|=(6070650869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192888979/2500000000 : ℝ)|^8265 ≤ (3739421446371/10000000000000 : ℝ)^6217
        have hw : |(1192888979/2500000000 : ℝ)|=(1192888979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s0_1 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2760367699/5000000000 : ℝ)*x 0 + (-665438049/2500000000 : ℝ)*x 1 + (1192888981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760367699/5000000000 : ℝ)^8265 ≤ (45394760981633/100000000000000 : ℝ)^6217 := by
    have hnat : (2760367699 : ℕ)^8265*100000000000000^6217 ≤ 45394760981633^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760367699 5000000000 45394760981633 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (665438049/2500000000 : ℝ)^8265 ≤ (4302756112431/25000000000000 : ℝ)^6217 := by
    have hnat : (665438049 : ℕ)^8265*25000000000000^6217 ≤ 4302756112431^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665438049 2500000000 4302756112431 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192888981/2500000000 : ℝ)^8265 ≤ (18697107273529/50000000000000 : ℝ)^6217 := by
    have hnat : (1192888981 : ℕ)^8265*50000000000000^6217 ≤ 18697107273529^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192888981 2500000000 18697107273529 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2760367699/5000000000 : ℝ), (-665438049/2500000000 : ℝ), (1192888981/2500000000 : ℝ)] ![(45394760981633/100000000000000 : ℝ), (4302756112431/25000000000000 : ℝ), (18697107273529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2760367699/5000000000 : ℝ)|^8265 ≤ (45394760981633/100000000000000 : ℝ)^6217
        have hw : |(2760367699/5000000000 : ℝ)|=(2760367699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-665438049/2500000000 : ℝ)|^8265 ≤ (4302756112431/25000000000000 : ℝ)^6217
        have hw : |(-665438049/2500000000 : ℝ)|=(665438049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192888981/2500000000 : ℝ)|^8265 ≤ (18697107273529/50000000000000 : ℝ)^6217
        have hw : |(1192888981/2500000000 : ℝ)|=(1192888981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s0_2 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1104147083/2000000000 : ℝ)*x 0 + (2385777959/5000000000 : ℝ)*x 1 + (-1330876091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104147083/2000000000 : ℝ)^8265 ≤ (9078952233493/20000000000000 : ℝ)^6217 := by
    have hnat : (1104147083 : ℕ)^8265*20000000000000^6217 ≤ 9078952233493^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104147083 2000000000 9078952233493 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2385777959/5000000000 : ℝ)^8265 ≤ (37394214484547/100000000000000 : ℝ)^6217 := by
    have hnat : (2385777959 : ℕ)^8265*100000000000000^6217 ≤ 37394214484547^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385777959 5000000000 37394214484547 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1330876091/5000000000 : ℝ)^8265 ≤ (17211024329379/100000000000000 : ℝ)^6217 := by
    have hnat : (1330876091 : ℕ)^8265*100000000000000^6217 ≤ 17211024329379^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330876091 5000000000 17211024329379 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104147083/2000000000 : ℝ), (2385777959/5000000000 : ℝ), (-1330876091/5000000000 : ℝ)] ![(9078952233493/20000000000000 : ℝ), (37394214484547/100000000000000 : ℝ), (17211024329379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104147083/2000000000 : ℝ)|^8265 ≤ (9078952233493/20000000000000 : ℝ)^6217
        have hw : |(1104147083/2000000000 : ℝ)|=(1104147083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2385777959/5000000000 : ℝ)|^8265 ≤ (37394214484547/100000000000000 : ℝ)^6217
        have hw : |(2385777959/5000000000 : ℝ)|=(2385777959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1330876091/5000000000 : ℝ)|^8265 ≤ (17211024329379/100000000000000 : ℝ)^6217
        have hw : |(-1330876091/5000000000 : ℝ)|=(1330876091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s0_3 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4206713283/10000000000 : ℝ)*x 0 + (1562273849/5000000000 : ℝ)*x 1 + (5673625767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206713283/10000000000 : ℝ)^8265 ≤ (31627323266339/100000000000000 : ℝ)^6217 := by
    have hnat : (4206713283 : ℕ)^8265*100000000000000^6217 ≤ 31627323266339^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206713283 10000000000 31627323266339 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562273849/5000000000 : ℝ)^8265 ≤ (10649526177641/50000000000000 : ℝ)^6217 := by
    have hnat : (1562273849 : ℕ)^8265*50000000000000^6217 ≤ 10649526177641^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562273849 5000000000 10649526177641 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5673625767/10000000000 : ℝ)^8265 ≤ (11768406091621/25000000000000 : ℝ)^6217 := by
    have hnat : (5673625767 : ℕ)^8265*25000000000000^6217 ≤ 11768406091621^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673625767 10000000000 11768406091621 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206713283/10000000000 : ℝ), (1562273849/5000000000 : ℝ), (5673625767/10000000000 : ℝ)] ![(31627323266339/100000000000000 : ℝ), (10649526177641/50000000000000 : ℝ), (11768406091621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206713283/10000000000 : ℝ)|^8265 ≤ (31627323266339/100000000000000 : ℝ)^6217
        have hw : |(4206713283/10000000000 : ℝ)|=(4206713283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1562273849/5000000000 : ℝ)|^8265 ≤ (10649526177641/50000000000000 : ℝ)^6217
        have hw : |(1562273849/5000000000 : ℝ)|=(1562273849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5673625767/10000000000 : ℝ)|^8265 ≤ (11768406091621/25000000000000 : ℝ)^6217
        have hw : |(5673625767/10000000000 : ℝ)|=(5673625767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s0_4 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-959759961/5000000000 : ℝ)*x 0 + (4805097161/10000000000 : ℝ)*x 1 + (6035935751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959759961/5000000000 : ℝ)^8265 ≤ (11144546877759/100000000000000 : ℝ)^6217 := by
    have hnat : (959759961 : ℕ)^8265*100000000000000^6217 ≤ 11144546877759^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959759961 5000000000 11144546877759 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4805097161/10000000000 : ℝ)^8265 ≤ (37744068847623/100000000000000 : ℝ)^6217 := by
    have hnat : (4805097161 : ℕ)^8265*100000000000000^6217 ≤ 37744068847623^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4805097161 10000000000 37744068847623 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6035935751/10000000000 : ℝ)^8265 ≤ (25555692129729/50000000000000 : ℝ)^6217 := by
    have hnat : (6035935751 : ℕ)^8265*50000000000000^6217 ≤ 25555692129729^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6035935751 10000000000 25555692129729 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-959759961/5000000000 : ℝ), (4805097161/10000000000 : ℝ), (6035935751/10000000000 : ℝ)] ![(11144546877759/100000000000000 : ℝ), (37744068847623/100000000000000 : ℝ), (25555692129729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-959759961/5000000000 : ℝ)|^8265 ≤ (11144546877759/100000000000000 : ℝ)^6217
        have hw : |(-959759961/5000000000 : ℝ)|=(959759961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4805097161/10000000000 : ℝ)|^8265 ≤ (37744068847623/100000000000000 : ℝ)^6217
        have hw : |(4805097161/10000000000 : ℝ)|=(4805097161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6035935751/10000000000 : ℝ)|^8265 ≤ (25555692129729/50000000000000 : ℝ)^6217
        have hw : |(6035935751/10000000000 : ℝ)|=(6035935751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s0_5 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5168107671/10000000000 : ℝ)*x 0 + (-279475199/2000000000 : ℝ)*x 1 + (3017966799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168107671/10000000000 : ℝ)^8265 ≤ (41581238833739/100000000000000 : ℝ)^6217 := by
    have hnat : (5168107671 : ℕ)^8265*100000000000000^6217 ≤ 41581238833739^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168107671 10000000000 41581238833739 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279475199/2000000000 : ℝ)^8265 ≤ (3653700562529/50000000000000 : ℝ)^6217 := by
    have hnat : (279475199 : ℕ)^8265*50000000000000^6217 ≤ 3653700562529^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279475199 2000000000 3653700562529 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3017966799/5000000000 : ℝ)^8265 ≤ (3194460001403/6250000000000 : ℝ)^6217 := by
    have hnat : (3017966799 : ℕ)^8265*6250000000000^6217 ≤ 3194460001403^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017966799 5000000000 3194460001403 6250000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168107671/10000000000 : ℝ), (-279475199/2000000000 : ℝ), (3017966799/5000000000 : ℝ)] ![(41581238833739/100000000000000 : ℝ), (3653700562529/50000000000000 : ℝ), (3194460001403/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168107671/10000000000 : ℝ)|^8265 ≤ (41581238833739/100000000000000 : ℝ)^6217
        have hw : |(5168107671/10000000000 : ℝ)|=(5168107671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279475199/2000000000 : ℝ)|^8265 ≤ (3653700562529/50000000000000 : ℝ)^6217
        have hw : |(-279475199/2000000000 : ℝ)|=(279475199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3017966799/5000000000 : ℝ)|^8265 ≤ (3194460001403/6250000000000 : ℝ)^6217
        have hw : |(3017966799/5000000000 : ℝ)|=(3017966799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s0_6 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646013451/1250000000 : ℝ)*x 0 + (6035935079/10000000000 : ℝ)*x 1 + (-279474739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646013451/1250000000 : ℝ)^8265 ≤ (41581238159881/100000000000000 : ℝ)^6217 := by
    have hnat : (646013451 : ℕ)^8265*100000000000000^6217 ≤ 41581238159881^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646013451 1250000000 41581238159881 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6035935079/10000000000 : ℝ)^8265 ≤ (51111376694539/100000000000000 : ℝ)^6217 := by
    have hnat : (6035935079 : ℕ)^8265*100000000000000^6217 ≤ 51111376694539^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6035935079 10000000000 51111376694539 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279474739/2000000000 : ℝ)^8265 ≤ (228355785481/3125000000000 : ℝ)^6217 := by
    have hnat : (279474739 : ℕ)^8265*3125000000000^6217 ≤ 228355785481^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279474739 2000000000 228355785481 3125000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646013451/1250000000 : ℝ), (6035935079/10000000000 : ℝ), (-279474739/2000000000 : ℝ)] ![(41581238159881/100000000000000 : ℝ), (51111376694539/100000000000000 : ℝ), (228355785481/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646013451/1250000000 : ℝ)|^8265 ≤ (41581238159881/100000000000000 : ℝ)^6217
        have hw : |(646013451/1250000000 : ℝ)|=(646013451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6035935079/10000000000 : ℝ)|^8265 ≤ (51111376694539/100000000000000 : ℝ)^6217
        have hw : |(6035935079/10000000000 : ℝ)|=(6035935079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279474739/2000000000 : ℝ)|^8265 ≤ (228355785481/3125000000000 : ℝ)^6217
        have hw : |(-279474739/2000000000 : ℝ)|=(279474739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s0_7 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1054304907/2500000000 : ℝ)*x 0 + (5607808591/10000000000 : ℝ)*x 1 + (79816691/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054304907/2500000000 : ℝ)^8265 ≤ (3966547131/12500000000 : ℝ)^6217 := by
    have hnat : (1054304907 : ℕ)^8265*12500000000^6217 ≤ 3966547131^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054304907 2500000000 3966547131 12500000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5607808591/10000000000 : ℝ)^8265 ≤ (23174522961481/50000000000000 : ℝ)^6217 := by
    have hnat : (5607808591 : ℕ)^8265*50000000000000^6217 ≤ 23174522961481^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607808591 10000000000 23174522961481 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79816691/250000000 : ℝ)^8265 ≤ (21918577022087/100000000000000 : ℝ)^6217 := by
    have hnat : (79816691 : ℕ)^8265*100000000000000^6217 ≤ 21918577022087^6217*250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79816691 250000000 21918577022087 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054304907/2500000000 : ℝ), (5607808591/10000000000 : ℝ), (79816691/250000000 : ℝ)] ![(3966547131/12500000000 : ℝ), (23174522961481/50000000000000 : ℝ), (21918577022087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054304907/2500000000 : ℝ)|^8265 ≤ (3966547131/12500000000 : ℝ)^6217
        have hw : |(1054304907/2500000000 : ℝ)|=(1054304907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5607808591/10000000000 : ℝ)|^8265 ≤ (23174522961481/50000000000000 : ℝ)^6217
        have hw : |(5607808591/10000000000 : ℝ)|=(5607808591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79816691/250000000 : ℝ)|^8265 ≤ (21918577022087/100000000000000 : ℝ)^6217
        have hw : |(79816691/250000000 : ℝ)|=(79816691/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1072_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (61/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14043/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (1033/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1033 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1033*1^256 ≤ 0^256*1^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1033/256 : ℝ) ≤ (1239423970653167831/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1033 ≤ (1239423970653167831/50000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1033*50000000000000000000^256 ≤ 1239423970653167831^256*5^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1239423970653167831 50000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1239423970653167831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1033 := by
      have hnat : (1 : ℕ)^256*1^1033 ≤ 1^1033*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (51239423970653167831/50000000000000000000 : ℝ) ≤ (5030433362040241/5000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (51239423970653167831/50000000000000000000 : ℝ)^256 ≤ (5030433362040241/5000000000000000 : ℝ)^1033 := by
      have hnat : (51239423970653167831 : ℕ)^256*5000000000000000^1033 ≤ 5030433362040241^1033*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51239423970653167831 50000000000000000000 5030433362040241 5000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030433362040241/5000000000000000 : ℝ)) (X := (51239423970653167831/50000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (26239423970653167831/25000000000000000000 : ℝ) ≤ (2530433362040241/2500000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (26239423970653167831/25000000000000000000 : ℝ)^256 ≤ (2530433362040241/2500000000000000 : ℝ)^1033 := by
      have hnat : (26239423970653167831 : ℕ)^256*2500000000000000^1033 ≤ 2530433362040241^1033*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26239423970653167831 25000000000000000000 2530433362040241 2500000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530433362040241/2500000000000000 : ℝ)) (X := (26239423970653167831/25000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30433362040241/2000000000000000 : ℝ)*(0 : ℝ))^(1033/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(30433362040241/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1239423970653167831/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30433362040241/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1033/256 : ℝ) := by
    rw [show (1 : ℝ)+(30433362040241/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030433362040241/5000000000000000 : ℝ) by norm_num, show 1+(1239423970653167831/50000000000000000000 : ℝ)+(0 : ℝ)=(51239423970653167831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1239423970653167831/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30433362040241/2000000000000000 : ℝ)*(2/5 : ℝ))^(1033/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(30433362040241/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530433362040241/2500000000000000 : ℝ) by norm_num, show 1+2*(1239423970653167831/50000000000000000000 : ℝ)=(26239423970653167831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30433362040241/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30433362040241/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30433362040241/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30433362040241/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30433362040241/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30433362040241/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1914164779/10000000000 : ℝ)*X 0 0+(6070650869/10000000000 : ℝ)*X 0 1+(1192888979/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2760367699/5000000000 : ℝ)*X 1 0+(-665438049/2500000000 : ℝ)*X 1 1+(1192888981/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1104147083/2000000000 : ℝ)*X 2 0+(2385777959/5000000000 : ℝ)*X 2 1+(-1330876091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4206713283/10000000000 : ℝ)*X 0 0+(1562273849/5000000000 : ℝ)*X 0 1+(5673625767/10000000000 : ℝ)*X 0 2+(4206713283/10000000000 : ℝ)*X 1 0+(1562273849/5000000000 : ℝ)*X 1 1+(5673625767/10000000000 : ℝ)*X 1 2+(4206713283/10000000000 : ℝ)*X 2 0+(1562273849/5000000000 : ℝ)*X 2 1+(5673625767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-959759961/5000000000 : ℝ)*X 0 0+(4805097161/10000000000 : ℝ)*X 0 1+(6035935751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5168107671/10000000000 : ℝ)*X 1 0+(-279475199/2000000000 : ℝ)*X 1 1+(3017966799/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646013451/1250000000 : ℝ)*X 2 0+(6035935079/10000000000 : ℝ)*X 2 1+(-279474739/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1054304907/2500000000 : ℝ)*X 0 0+(5607808591/10000000000 : ℝ)*X 0 1+(79816691/250000000 : ℝ)*X 0 2+(1054304907/2500000000 : ℝ)*X 1 0+(5607808591/10000000000 : ℝ)*X 1 1+(79816691/250000000 : ℝ)*X 1 2+(1054304907/2500000000 : ℝ)*X 2 0+(5607808591/10000000000 : ℝ)*X 2 1+(79816691/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1078901869234541400723/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (9385777/25000000000000 : ℝ)*(base1) + (864203299/100000000000000 : ℝ)*(base19) + (806069367/100000000000000 : ℝ)*(base23) + (12100857/20000000000000 : ℝ)*(base24) + (197537497/100000000000000 : ℝ)*(upper3) + (7262953590627/1250000000000 : ℝ)*(major0) + (7262953590627/1250000000000 : ℝ)*(major1) + (7262953590627/1250000000000 : ℝ)*(major2) + (15395390198493/2000000000000 : ℝ)*(sp0) + (192442620670109/25000000000000 : ℝ)*(sp1) + (384885240155041/50000000000000 : ℝ)*(sp2) + (196149786710351/50000000000000 : ℝ)*(sp3) + (1874502193/100000000000000 : ℝ)*(sp4) + (300313981/20000000000000 : ℝ)*(sp7) + (78460222506743/20000000000000 : ℝ)*(f.failure) + (153954269376747/20000000000000 : ℝ)*(f.sum) + (2387321466393/1250000000000000000000000000 : ℝ)*base66 + (649817513893/2500000000000000000000000000 : ℝ)*base68 + (8393079478607/2500000000000000000000000000 : ℝ)*base69 + (4868530586107/2500000000000000000000000000 : ℝ)*base71 + (4157161072643/1250000000000000000000000000 : ℝ)*base74 + (9897849323893/2500000000000000000000000000 : ℝ)*base76 + (2539329331107/2500000000000000000000000000 : ℝ)*base77 + (5043756603607/2500000000000000000000000000 : ℝ)*base79 + (4298715216393/1250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3300661/2000000000000000000000 : ℝ)*base90 + (3300661/2000000000000000000000 : ℝ)*base92 + (3300661/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47663777577399721762077/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6627557/390625000000 : ℝ)*(base19) + (904936053/50000000000000 : ℝ)*(base23) + (30397469/50000000000000 : ℝ)*(base39) + (64595387/20000000000000 : ℝ)*(base45) + (34933449/20000000000000 : ℝ)*(upper3) + (167953319/50000000000000 : ℝ)*(upper5) + (613252680084577/100000000000000 : ℝ)*(major0) + (613252680084577/100000000000000 : ℝ)*(major1) + (306626309644819/50000000000000 : ℝ)*(major2) + (939690117/100000000000000 : ℝ)*(sp2) + (203113058269693/25000000000000 : ℝ)*(sp4) + (40622526821209/5000000000000 : ℝ)*(sp5) + (12694524129867/1562500000000 : ℝ)*(sp6) + (25878300755539/6250000000000 : ℝ)*(sp7) + (25878300755539/6250000000000 : ℝ)*(f.failure) + (81245229387371/10000000000000 : ℝ)*(f.sum) + (90698053962837/40000000000000000000000000000 : ℝ)*base66 + (377335612438621/100000000000000000000000000000 : ℝ)*base68 + (650623868936943/200000000000000000000000000000 : ℝ)*base70 + (220241770038621/100000000000000000000000000000 : ℝ)*base72 + (150377797802837/40000000000000000000000000000 : ℝ)*base74 + (1876148242536943/200000000000000000000000000000 : ℝ)*base76 + (598504068736943/200000000000000000000000000000 : ℝ)*base78 + (1676426590936943/200000000000000000000000000000 : ℝ)*base80 + (87526233136943/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3532647/625000000000000000000 : ℝ)*base89 + (3532647/625000000000000000000 : ℝ)*base91 + (9782647/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1072_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (61/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1072_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1072_s1_0 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123864193/10000000000 : ℝ)*x 0 + (5720645603/10000000000 : ℝ)*x 1 + (4987272851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123864193/10000000000 : ℝ)^8265 ≤ (12748799258869/100000000000000 : ℝ)^6217 := by
    have hnat : (2123864193 : ℕ)^8265*100000000000000^6217 ≤ 12748799258869^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123864193 10000000000 12748799258869 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5720645603/10000000000 : ℝ)^8265 ≤ (23796481945469/50000000000000 : ℝ)^6217 := by
    have hnat : (5720645603 : ℕ)^8265*50000000000000^6217 ≤ 23796481945469^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720645603 10000000000 23796481945469 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4987272851/10000000000 : ℝ)^8265 ≤ (39658236834389/100000000000000 : ℝ)^6217 := by
    have hnat : (4987272851 : ℕ)^8265*100000000000000^6217 ≤ 39658236834389^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4987272851 10000000000 39658236834389 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123864193/10000000000 : ℝ), (5720645603/10000000000 : ℝ), (4987272851/10000000000 : ℝ)] ![(12748799258869/100000000000000 : ℝ), (23796481945469/50000000000000 : ℝ), (39658236834389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123864193/10000000000 : ℝ)|^8265 ≤ (12748799258869/100000000000000 : ℝ)^6217
        have hw : |(-2123864193/10000000000 : ℝ)|=(2123864193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5720645603/10000000000 : ℝ)|^8265 ≤ (23796481945469/50000000000000 : ℝ)^6217
        have hw : |(5720645603/10000000000 : ℝ)|=(5720645603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4987272851/10000000000 : ℝ)|^8265 ≤ (39658236834389/100000000000000 : ℝ)^6217
        have hw : |(4987272851/10000000000 : ℝ)|=(4987272851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_1 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5422982337/10000000000 : ℝ)*x 0 + (-252107871/1000000000 : ℝ)*x 1 + (4987273157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422982337/10000000000 : ℝ)^8265 ≤ (22164662144567/50000000000000 : ℝ)^6217 := by
    have hnat : (5422982337 : ℕ)^8265*50000000000000^6217 ≤ 22164662144567^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422982337 10000000000 22164662144567 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252107871/1000000000 : ℝ)^8265 ≤ (16012435629777/100000000000000 : ℝ)^6217 := by
    have hnat : (252107871 : ℕ)^8265*100000000000000^6217 ≤ 16012435629777^6217*1000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252107871 1000000000 16012435629777 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4987273157/10000000000 : ℝ)^8265 ≤ (7931648013847/20000000000000 : ℝ)^6217 := by
    have hnat : (4987273157 : ℕ)^8265*20000000000000^6217 ≤ 7931648013847^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4987273157 10000000000 7931648013847 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422982337/10000000000 : ℝ), (-252107871/1000000000 : ℝ), (4987273157/10000000000 : ℝ)] ![(22164662144567/50000000000000 : ℝ), (16012435629777/100000000000000 : ℝ), (7931648013847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422982337/10000000000 : ℝ)|^8265 ≤ (22164662144567/50000000000000 : ℝ)^6217
        have hw : |(5422982337/10000000000 : ℝ)|=(5422982337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-252107871/1000000000 : ℝ)|^8265 ≤ (16012435629777/100000000000000 : ℝ)^6217
        have hw : |(-252107871/1000000000 : ℝ)|=(252107871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4987273157/10000000000 : ℝ)|^8265 ≤ (7931648013847/20000000000000 : ℝ)^6217
        have hw : |(4987273157/10000000000 : ℝ)|=(4987273157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_2 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5422982977/10000000000 : ℝ)*x 0 + (19481533/39062500 : ℝ)*x 1 + (-1260539387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422982977/10000000000 : ℝ)^8265 ≤ (22164665622049/50000000000000 : ℝ)^6217 := by
    have hnat : (5422982977 : ℕ)^8265*50000000000000^6217 ≤ 22164665622049^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422982977 10000000000 22164665622049 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19481533/39062500 : ℝ)^8265 ≤ (39658232574117/100000000000000 : ℝ)^6217 := by
    have hnat : (19481533 : ℕ)^8265*100000000000000^6217 ≤ 39658232574117^6217*39062500^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19481533 39062500 39658232574117 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1260539387/5000000000 : ℝ)^8265 ≤ (8006218085087/50000000000000 : ℝ)^6217 := by
    have hnat : (1260539387 : ℕ)^8265*50000000000000^6217 ≤ 8006218085087^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260539387 5000000000 8006218085087 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422982977/10000000000 : ℝ), (19481533/39062500 : ℝ), (-1260539387/5000000000 : ℝ)] ![(22164665622049/50000000000000 : ℝ), (39658232574117/100000000000000 : ℝ), (8006218085087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422982977/10000000000 : ℝ)|^8265 ≤ (22164665622049/50000000000000 : ℝ)^6217
        have hw : |(5422982977/10000000000 : ℝ)|=(5422982977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19481533/39062500 : ℝ)|^8265 ≤ (39658232574117/100000000000000 : ℝ)^6217
        have hw : |(19481533/39062500 : ℝ)|=(19481533/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1260539387/5000000000 : ℝ)|^8265 ≤ (8006218085087/50000000000000 : ℝ)^6217
        have hw : |(-1260539387/5000000000 : ℝ)|=(1260539387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_3 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1080826121/2500000000 : ℝ)*x 0 + (1831848303/5000000000 : ℝ)*x 1 + (127567897/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080826121/2500000000 : ℝ)^8265 ≤ (32797936022411/100000000000000 : ℝ)^6217 := by
    have hnat : (1080826121 : ℕ)^8265*100000000000000^6217 ≤ 32797936022411^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080826121 2500000000 32797936022411 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1831848303/5000000000 : ℝ)^8265 ≤ (2631880431099/10000000000000 : ℝ)^6217 := by
    have hnat : (1831848303 : ℕ)^8265*10000000000000^6217 ≤ 2631880431099^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831848303 5000000000 2631880431099 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127567897/250000000 : ℝ)^8265 ≤ (8176651928987/20000000000000 : ℝ)^6217 := by
    have hnat : (127567897 : ℕ)^8265*20000000000000^6217 ≤ 8176651928987^6217*250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127567897 250000000 8176651928987 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080826121/2500000000 : ℝ), (1831848303/5000000000 : ℝ), (127567897/250000000 : ℝ)] ![(32797936022411/100000000000000 : ℝ), (2631880431099/10000000000000 : ℝ), (8176651928987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080826121/2500000000 : ℝ)|^8265 ≤ (32797936022411/100000000000000 : ℝ)^6217
        have hw : |(1080826121/2500000000 : ℝ)|=(1080826121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1831848303/5000000000 : ℝ)|^8265 ≤ (2631880431099/10000000000000 : ℝ)^6217
        have hw : |(1831848303/5000000000 : ℝ)|=(1831848303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127567897/250000000 : ℝ)|^8265 ≤ (8176651928987/20000000000000 : ℝ)^6217
        have hw : |(127567897/250000000 : ℝ)|=(127567897/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_4 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062388511/5000000000 : ℝ)*x 0 + (39980449/80000000 : ℝ)*x 1 + (5710151551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062388511/5000000000 : ℝ)^8265 ≤ (3189021044351/25000000000000 : ℝ)^6217 := by
    have hnat : (1062388511 : ℕ)^8265*25000000000000^6217 ≤ 3189021044351^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062388511 5000000000 3189021044351 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39980449/80000000 : ℝ)^8265 ≤ (39766982278597/100000000000000 : ℝ)^6217 := by
    have hnat : (39980449 : ℕ)^8265*100000000000000^6217 ≤ 39766982278597^6217*80000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39980449 80000000 39766982278597 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5710151551/10000000000 : ℝ)^8265 ≤ (47476933537239/100000000000000 : ℝ)^6217 := by
    have hnat : (5710151551 : ℕ)^8265*100000000000000^6217 ≤ 47476933537239^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5710151551 10000000000 47476933537239 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062388511/5000000000 : ℝ), (39980449/80000000 : ℝ), (5710151551/10000000000 : ℝ)] ![(3189021044351/25000000000000 : ℝ), (39766982278597/100000000000000 : ℝ), (47476933537239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062388511/5000000000 : ℝ)|^8265 ≤ (3189021044351/25000000000000 : ℝ)^6217
        have hw : |(-1062388511/5000000000 : ℝ)|=(1062388511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39980449/80000000 : ℝ)|^8265 ≤ (39766982278597/100000000000000 : ℝ)^6217
        have hw : |(39980449/80000000 : ℝ)|=(39980449/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5710151551/10000000000 : ℝ)|^8265 ≤ (47476933537239/100000000000000 : ℝ)^6217
        have hw : |(5710151551/10000000000 : ℝ)|=(5710151551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_5 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (41885049/80000000 : ℝ)*x 0 + (-1798197923/10000000000 : ℝ)*x 1 + (2855076717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41885049/80000000 : ℝ)^8265 ≤ (42305030202151/100000000000000 : ℝ)^6217 := by
    have hnat : (41885049 : ℕ)^8265*100000000000000^6217 ≤ 42305030202151^6217*80000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41885049 80000000 42305030202151 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1798197923/10000000000 : ℝ)^8265 ≤ (10218015436257/100000000000000 : ℝ)^6217 := by
    have hnat : (1798197923 : ℕ)^8265*100000000000000^6217 ≤ 10218015436257^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798197923 10000000000 10218015436257 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2855076717/5000000000 : ℝ)^8265 ≤ (23738477175423/50000000000000 : ℝ)^6217 := by
    have hnat : (2855076717 : ℕ)^8265*50000000000000^6217 ≤ 23738477175423^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855076717 5000000000 23738477175423 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41885049/80000000 : ℝ), (-1798197923/10000000000 : ℝ), (2855076717/5000000000 : ℝ)] ![(42305030202151/100000000000000 : ℝ), (10218015436257/100000000000000 : ℝ), (23738477175423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41885049/80000000 : ℝ)|^8265 ≤ (42305030202151/100000000000000 : ℝ)^6217
        have hw : |(41885049/80000000 : ℝ)|=(41885049/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1798197923/10000000000 : ℝ)|^8265 ≤ (10218015436257/100000000000000 : ℝ)^6217
        have hw : |(-1798197923/10000000000 : ℝ)|=(1798197923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2855076717/5000000000 : ℝ)|^8265 ≤ (23738477175423/50000000000000 : ℝ)^6217
        have hw : |(2855076717/5000000000 : ℝ)|=(2855076717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_6 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1047125813/2000000000 : ℝ)*x 0 + (5710155717/10000000000 : ℝ)*x 1 + (-224774689/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047125813/2000000000 : ℝ)^8265 ≤ (21152504036821/50000000000000 : ℝ)^6217 := by
    have hnat : (1047125813 : ℕ)^8265*50000000000000^6217 ≤ 21152504036821^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047125813 2000000000 21152504036821 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5710155717/10000000000 : ℝ)^8265 ≤ (11869244896457/25000000000000 : ℝ)^6217 := by
    have hnat : (5710155717 : ℕ)^8265*25000000000000^6217 ≤ 11869244896457^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5710155717 10000000000 11869244896457 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224774689/1250000000 : ℝ)^8265 ≤ (10218012331463/100000000000000 : ℝ)^6217 := by
    have hnat : (224774689 : ℕ)^8265*100000000000000^6217 ≤ 10218012331463^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224774689 1250000000 10218012331463 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047125813/2000000000 : ℝ), (5710155717/10000000000 : ℝ), (-224774689/1250000000 : ℝ)] ![(21152504036821/50000000000000 : ℝ), (11869244896457/25000000000000 : ℝ), (10218012331463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047125813/2000000000 : ℝ)|^8265 ≤ (21152504036821/50000000000000 : ℝ)^6217
        have hw : |(1047125813/2000000000 : ℝ)|=(1047125813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5710155717/10000000000 : ℝ)|^8265 ≤ (11869244896457/25000000000000 : ℝ)^6217
        have hw : |(5710155717/10000000000 : ℝ)|=(5710155717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224774689/1250000000 : ℝ)|^8265 ≤ (10218012331463/100000000000000 : ℝ)^6217
        have hw : |(-224774689/1250000000 : ℝ)|=(224774689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_7 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (540636417/1250000000 : ℝ)*x 0 + (5082534659/10000000000 : ℝ)*x 1 + (1842142091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540636417/1250000000 : ℝ)^8265 ≤ (131263833391/400000000000 : ℝ)^6217 := by
    have hnat : (540636417 : ℕ)^8265*400000000000^6217 ≤ 131263833391^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540636417 1250000000 131263833391 400000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082534659/10000000000 : ℝ)^8265 ≤ (10167110456501/25000000000000 : ℝ)^6217 := by
    have hnat : (5082534659 : ℕ)^8265*25000000000000^6217 ≤ 10167110456501^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082534659 10000000000 10167110456501 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842142091/5000000000 : ℝ)^8265 ≤ (5303119959653/20000000000000 : ℝ)^6217 := by
    have hnat : (1842142091 : ℕ)^8265*20000000000000^6217 ≤ 5303119959653^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842142091 5000000000 5303119959653 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540636417/1250000000 : ℝ), (5082534659/10000000000 : ℝ), (1842142091/5000000000 : ℝ)] ![(131263833391/400000000000 : ℝ), (10167110456501/25000000000000 : ℝ), (5303119959653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540636417/1250000000 : ℝ)|^8265 ≤ (131263833391/400000000000 : ℝ)^6217
        have hw : |(540636417/1250000000 : ℝ)|=(540636417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082534659/10000000000 : ℝ)|^8265 ≤ (10167110456501/25000000000000 : ℝ)^6217
        have hw : |(5082534659/10000000000 : ℝ)|=(5082534659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1842142091/5000000000 : ℝ)|^8265 ≤ (5303119959653/20000000000000 : ℝ)^6217
        have hw : |(1842142091/5000000000 : ℝ)|=(1842142091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_8 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2122123/2500000000 : ℝ)*x 0 + (1372465263/2500000000 : ℝ)*x 1 + (398279023/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122123/2500000000 : ℝ)^8265 ≤ (8262813427/100000000000000 : ℝ)^6217 := by
    have hnat : (2122123 : ℕ)^8265*100000000000000^6217 ≤ 8262813427^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122123 2500000000 8262813427 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372465263/2500000000 : ℝ)^8265 ≤ (9011515260689/20000000000000 : ℝ)^6217 := by
    have hnat : (1372465263 : ℕ)^8265*20000000000000^6217 ≤ 9011515260689^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372465263 2500000000 9011515260689 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398279023/625000000 : ℝ)^8265 ≤ (54934160871543/100000000000000 : ℝ)^6217 := by
    have hnat : (398279023 : ℕ)^8265*100000000000000^6217 ≤ 54934160871543^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398279023 625000000 54934160871543 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2122123/2500000000 : ℝ), (1372465263/2500000000 : ℝ), (398279023/625000000 : ℝ)] ![(8262813427/100000000000000 : ℝ), (9011515260689/20000000000000 : ℝ), (54934160871543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2122123/2500000000 : ℝ)|^8265 ≤ (8262813427/100000000000000 : ℝ)^6217
        have hw : |(2122123/2500000000 : ℝ)|=(2122123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372465263/2500000000 : ℝ)|^8265 ≤ (9011515260689/20000000000000 : ℝ)^6217
        have hw : |(1372465263/2500000000 : ℝ)|=(1372465263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398279023/625000000 : ℝ)|^8265 ≤ (54934160871543/100000000000000 : ℝ)^6217
        have hw : |(398279023/625000000 : ℝ)|=(398279023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_9 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (482600333/5000000000 : ℝ)*x 0 + (-4455059187/10000000000 : ℝ)*x 1 + (6928677141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482600333/5000000000 : ℝ)^8265 ≤ (4468183732827/100000000000000 : ℝ)^6217 := by
    have hnat : (482600333 : ℕ)^8265*100000000000000^6217 ≤ 4468183732827^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482600333 5000000000 4468183732827 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4455059187/10000000000 : ℝ)^8265 ≤ (34133358708019/100000000000000 : ℝ)^6217 := by
    have hnat : (4455059187 : ℕ)^8265*100000000000000^6217 ≤ 34133358708019^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4455059187 10000000000 34133358708019 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6928677141/10000000000 : ℝ)^8265 ≤ (30699228769507/50000000000000 : ℝ)^6217 := by
    have hnat : (6928677141 : ℕ)^8265*50000000000000^6217 ≤ 30699228769507^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6928677141 10000000000 30699228769507 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(482600333/5000000000 : ℝ), (-4455059187/10000000000 : ℝ), (6928677141/10000000000 : ℝ)] ![(4468183732827/100000000000000 : ℝ), (34133358708019/100000000000000 : ℝ), (30699228769507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(482600333/5000000000 : ℝ)|^8265 ≤ (4468183732827/100000000000000 : ℝ)^6217
        have hw : |(482600333/5000000000 : ℝ)|=(482600333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4455059187/10000000000 : ℝ)|^8265 ≤ (34133358708019/100000000000000 : ℝ)^6217
        have hw : |(-4455059187/10000000000 : ℝ)|=(4455059187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6928677141/10000000000 : ℝ)|^8265 ≤ (30699228769507/50000000000000 : ℝ)^6217
        have hw : |(6928677141/10000000000 : ℝ)|=(6928677141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_10 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (120649291/1250000000 : ℝ)*x 0 + (3464331707/5000000000 : ℝ)*x 1 + (-2227539447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120649291/1250000000 : ℝ)^8265 ≤ (4468144727209/100000000000000 : ℝ)^6217 := by
    have hnat : (120649291 : ℕ)^8265*100000000000000^6217 ≤ 4468144727209^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120649291 1250000000 4468144727209 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3464331707/5000000000 : ℝ)^8265 ≤ (15349573956533/25000000000000 : ℝ)^6217 := by
    have hnat : (3464331707 : ℕ)^8265*25000000000000^6217 ≤ 15349573956533^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3464331707 5000000000 15349573956533 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2227539447/5000000000 : ℝ)^8265 ≤ (3413355943621/10000000000000 : ℝ)^6217 := by
    have hnat : (2227539447 : ℕ)^8265*10000000000000^6217 ≤ 3413355943621^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227539447 5000000000 3413355943621 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(120649291/1250000000 : ℝ), (3464331707/5000000000 : ℝ), (-2227539447/5000000000 : ℝ)] ![(4468144727209/100000000000000 : ℝ), (15349573956533/25000000000000 : ℝ), (3413355943621/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(120649291/1250000000 : ℝ)|^8265 ≤ (4468144727209/100000000000000 : ℝ)^6217
        have hw : |(120649291/1250000000 : ℝ)|=(120649291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3464331707/5000000000 : ℝ)|^8265 ≤ (15349573956533/25000000000000 : ℝ)^6217
        have hw : |(3464331707/5000000000 : ℝ)|=(3464331707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2227539447/5000000000 : ℝ)|^8265 ≤ (3413355943621/10000000000000 : ℝ)^6217
        have hw : |(-2227539447/5000000000 : ℝ)|=(2227539447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s1_11 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1924366659/10000000000 : ℝ)*x 0 + (2914514037/5000000000 : ℝ)*x 1 + (2510851111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1924366659/10000000000 : ℝ)^8265 ≤ (11181971869611/100000000000000 : ℝ)^6217 := by
    have hnat : (1924366659 : ℕ)^8265*100000000000000^6217 ≤ 11181971869611^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924366659 10000000000 11181971869611 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2914514037/5000000000 : ℝ)^8265 ≤ (48795411611681/100000000000000 : ℝ)^6217 := by
    have hnat : (2914514037 : ℕ)^8265*100000000000000^6217 ≤ 48795411611681^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914514037 5000000000 48795411611681 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510851111/5000000000 : ℝ)^8265 ≤ (40022616500417/100000000000000 : ℝ)^6217 := by
    have hnat : (2510851111 : ℕ)^8265*100000000000000^6217 ≤ 40022616500417^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510851111 5000000000 40022616500417 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1924366659/10000000000 : ℝ), (2914514037/5000000000 : ℝ), (2510851111/5000000000 : ℝ)] ![(11181971869611/100000000000000 : ℝ), (48795411611681/100000000000000 : ℝ), (40022616500417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1924366659/10000000000 : ℝ)|^8265 ≤ (11181971869611/100000000000000 : ℝ)^6217
        have hw : |(1924366659/10000000000 : ℝ)|=(1924366659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2914514037/5000000000 : ℝ)|^8265 ≤ (48795411611681/100000000000000 : ℝ)^6217
        have hw : |(2914514037/5000000000 : ℝ)|=(2914514037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510851111/5000000000 : ℝ)|^8265 ≤ (40022616500417/100000000000000 : ℝ)^6217
        have hw : |(2510851111/5000000000 : ℝ)|=(2510851111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1072_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (61/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (164/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (61/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (61/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (61/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (61/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (61/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (61/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (61/50000 : ℝ) ^ (1033/256 : ℝ) ≤ (174987353/100000000000000000000 : ℝ) := by
    have hpowers : (61/50000 : ℝ)^1033 ≤ (174987353/100000000000000000000 : ℝ)^256 := by
      have hnat : (61 : ℕ)^1033*100000000000000000000^256 ≤ 174987353^256*50000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61 50000 174987353 100000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61/50000 : ℝ)) (X := (174987353/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14043/50000 : ℝ) ^ (1033/256 : ℝ) ≤ (297536700833974317/50000000000000000000 : ℝ) := by
    have hpowers : (14043/50000 : ℝ)^1033 ≤ (297536700833974317/50000000000000000000 : ℝ)^256 := by
      have hnat : (14043 : ℕ)^1033*50000000000000000000^256 ≤ 297536700833974317^256*50000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14043 50000 297536700833974317 50000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14043/50000 : ℝ)) (X := (297536700833974317/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000174987353/50000000000000000000 : ℝ) ≤ (5000000000004337/5000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (50000000000174987353/50000000000000000000 : ℝ)^256 ≤ (5000000000004337/5000000000000000 : ℝ)^1033 := by
      have hnat : (50000000000174987353 : ℕ)^256*5000000000000000^1033 ≤ 5000000000004337^1033*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000174987353 50000000000000000000 5000000000004337 5000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000004337/5000000000000000 : ℝ)) (X := (50000000000174987353/50000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100595073401842935987/100000000000000000000 : ℝ) ≤ (5007357165337193/5000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (100595073401842935987/100000000000000000000 : ℝ)^256 ≤ (5007357165337193/5000000000000000 : ℝ)^1033 := by
      have hnat : (100595073401842935987 : ℕ)^256*5000000000000000^1033 ≤ 5007357165337193^1033*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100595073401842935987 100000000000000000000 5007357165337193 5000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007357165337193/5000000000000000 : ℝ)) (X := (100595073401842935987/100000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25297536700833974317/25000000000000000000 : ℝ) ≤ (5014714330670049/5000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (25297536700833974317/25000000000000000000 : ℝ)^256 ≤ (5014714330670049/5000000000000000 : ℝ)^1033 := by
      have hnat : (25297536700833974317 : ℕ)^256*5000000000000000^1033 ≤ 5014714330670049^1033*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25297536700833974317 25000000000000000000 5014714330670049 5000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014714330670049/5000000000000000 : ℝ)) (X := (25297536700833974317/25000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(174987353/100000000000000000000 : ℝ) ≤ ((34954551212945015751/34955000000000000000 : ℝ)+2*(919645666607/174775000000000 : ℝ)*(61/50000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (34954551212945015751/34955000000000000000 : ℝ)+2*(919645666607/174775000000000 : ℝ)*(61/50000 : ℝ)=(5000000000004337/5000000000000000 : ℝ) by norm_num, show 1+2*(174987353/100000000000000000000 : ℝ)=(50000000000174987353/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(297536700833974317/50000000000000000000 : ℝ)+(174987353/100000000000000000000 : ℝ) ≤ ((34954551212945015751/34955000000000000000 : ℝ)+(919645666607/174775000000000 : ℝ)*((14043/50000 : ℝ)+(61/50000 : ℝ)))^(1033/256 : ℝ) := by
    rw [show (34954551212945015751/34955000000000000000 : ℝ)+(919645666607/174775000000000 : ℝ)*((14043/50000 : ℝ)+(61/50000 : ℝ))=(5007357165337193/5000000000000000 : ℝ) by norm_num, show 1+(297536700833974317/50000000000000000000 : ℝ)+(174987353/100000000000000000000 : ℝ)=(100595073401842935987/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(297536700833974317/50000000000000000000 : ℝ) ≤ ((34954551212945015751/34955000000000000000 : ℝ)+2*(919645666607/174775000000000 : ℝ)*(14043/50000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (34954551212945015751/34955000000000000000 : ℝ)+2*(919645666607/174775000000000 : ℝ)*(14043/50000 : ℝ)=(5014714330670049/5000000000000000 : ℝ) by norm_num, show 1+2*(297536700833974317/50000000000000000000 : ℝ)=(25297536700833974317/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34954551212945015751/34955000000000000000 : ℝ)*(X 1 0+X 2 0)+(919645666607/174775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (61/50000 : ℝ)) (hi := (14043/50000 : ℝ)) (c := (34954551212945015751/34955000000000000000 : ℝ)) (alpha := (919645666607/174775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34954551212945015751/34955000000000000000 : ℝ)*(X 0 1+X 2 1)+(919645666607/174775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (61/50000 : ℝ)) (hi := (14043/50000 : ℝ)) (c := (34954551212945015751/34955000000000000000 : ℝ)) (alpha := (919645666607/174775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34954551212945015751/34955000000000000000 : ℝ)*(X 0 2+X 1 2)+(919645666607/174775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (61/50000 : ℝ)) (hi := (14043/50000 : ℝ)) (c := (34954551212945015751/34955000000000000000 : ℝ)) (alpha := (919645666607/174775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2123864193/10000000000 : ℝ)*X 0 0+(5720645603/10000000000 : ℝ)*X 0 1+(4987272851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5422982337/10000000000 : ℝ)*X 1 0+(-252107871/1000000000 : ℝ)*X 1 1+(4987273157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5422982977/10000000000 : ℝ)*X 2 0+(19481533/39062500 : ℝ)*X 2 1+(-1260539387/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080826121/2500000000 : ℝ)*X 0 0+(1831848303/5000000000 : ℝ)*X 0 1+(127567897/250000000 : ℝ)*X 0 2+(1080826121/2500000000 : ℝ)*X 1 0+(1831848303/5000000000 : ℝ)*X 1 1+(127567897/250000000 : ℝ)*X 1 2+(1080826121/2500000000 : ℝ)*X 2 0+(1831848303/5000000000 : ℝ)*X 2 1+(127567897/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1062388511/5000000000 : ℝ)*X 0 0+(39980449/80000000 : ℝ)*X 0 1+(5710151551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41885049/80000000 : ℝ)*X 1 0+(-1798197923/10000000000 : ℝ)*X 1 1+(2855076717/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1047125813/2000000000 : ℝ)*X 2 0+(5710155717/10000000000 : ℝ)*X 2 1+(-224774689/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540636417/1250000000 : ℝ)*X 0 0+(5082534659/10000000000 : ℝ)*X 0 1+(1842142091/5000000000 : ℝ)*X 0 2+(540636417/1250000000 : ℝ)*X 1 0+(5082534659/10000000000 : ℝ)*X 1 1+(1842142091/5000000000 : ℝ)*X 1 2+(540636417/1250000000 : ℝ)*X 2 0+(5082534659/10000000000 : ℝ)*X 2 1+(1842142091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((2122123/2500000000 : ℝ)*X 0 0+(1372465263/2500000000 : ℝ)*X 0 1+(398279023/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((482600333/5000000000 : ℝ)*X 1 0+(-4455059187/10000000000 : ℝ)*X 1 1+(6928677141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((120649291/1250000000 : ℝ)*X 2 0+(3464331707/5000000000 : ℝ)*X 2 1+(-2227539447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1924366659/10000000000 : ℝ)*X 0 0+(2914514037/5000000000 : ℝ)*X 0 1+(2510851111/5000000000 : ℝ)*X 0 2+(1924366659/10000000000 : ℝ)*X 1 0+(2914514037/5000000000 : ℝ)*X 1 1+(2510851111/5000000000 : ℝ)*X 1 2+(1924366659/10000000000 : ℝ)*X 2 0+(2914514037/5000000000 : ℝ)*X 2 1+(2510851111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30965851723076318735547/2184687500000000000000000000 : ℝ) := by norm_num
    linear_combination (514622475829427/50000000000000 : ℝ)*(major0) + (514622475829427/50000000000000 : ℝ)*(major1) + (514622475829427/50000000000000 : ℝ)*(major2) + (340891525666373/25000000000000 : ℝ)*(sp0) + (1363566945281737/100000000000000 : ℝ)*(sp1) + (681783025949327/50000000000000 : ℝ)*(sp2) + (86864826844877/12500000000000 : ℝ)*(sp3) + (209062637/12500000000000 : ℝ)*(sp4) + (634410189/50000000000000 : ℝ)*(sp5) + (1997045589/100000000000000 : ℝ)*(sp6) + (326632931/25000000000000 : ℝ)*(sp8) + (867596197/100000000000000 : ℝ)*(sp9) + (1032754069/100000000000000 : ℝ)*(sp10) + (867196161/50000000000000 : ℝ)*(sp11) + (347460174575669/50000000000000 : ℝ)*(f.failure) + (170446135212289/12500000000000 : ℝ)*(f.sum) + (19075882353601/17477500000000000000000000000 : ℝ)*base65 + (1396743397300104677/1747750000000000000000000000000000 : ℝ)*base67 + (2930817970293895323/1747750000000000000000000000000000 : ℝ)*base70 + (7041930604358854677/1747750000000000000000000000000000 : ℝ)*base71 + (41421964386957/34955000000000000000000000000 : ℝ)*base73 + (2702520779628395323/1747750000000000000000000000000000 : ℝ)*base76 + (1461074633480354677/1747750000000000000000000000000000 : ℝ)*base77 + (869634893719145323/1747750000000000000000000000000000 : ℝ)*base80 + (14100858986821/17477500000000000000000000000 : ℝ)*base81 + (6913137/5000000000000000000000 : ℝ)*base89 + (6913137/5000000000000000000000 : ℝ)*base91 + (6913137/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1329693292650122547050916039/436937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (242334233/100000000000000 : ℝ)*(lower4) + (4729201/20000000000000 : ℝ)*(upper5) + (264812437497421/25000000000000 : ℝ)*(major0) + (264812437497421/25000000000000 : ℝ)*(major1) + (264812437497421/25000000000000 : ℝ)*(major2) + (270766287/25000000000000 : ℝ)*(sp0) + (784311177/50000000000000 : ℝ)*(sp1) + (4063866723/100000000000000 : ℝ)*(sp2) + (1403316020076077/100000000000000 : ℝ)*(sp4) + (1403318994290637/100000000000000 : ℝ)*(sp5) + (1403316499046269/100000000000000 : ℝ)*(sp6) + (357588900390171/50000000000000 : ℝ)*(sp7) + (1729885883/50000000000000 : ℝ)*(sp8) + (25871141/2500000000000 : ℝ)*(sp11) + (357589417812991/50000000000000 : ℝ)*(f.failure) + (1403320562912991/100000000000000 : ℝ)*(f.sum) + (62776306889189/17477500000000000000000000000 : ℝ)*base66 + (5983426845904846829/873875000000000000000000000000000 : ℝ)*base68 + (3848850963238346829/873875000000000000000000000000000 : ℝ)*base70 + (1695651808104346829/873875000000000000000000000000000 : ℝ)*base72 + (226318726196133/34955000000000000000000000000 : ℝ)*base74 + (3745972082743721829/873875000000000000000000000000000 : ℝ)*base76 + (5928129861429721829/873875000000000000000000000000000 : ℝ)*base78 + (8361322931569346829/873875000000000000000000000000000 : ℝ)*base80 + (5272530385759/17477500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (53461043/5000000000000000000000 : ℝ)*base89 + (53461043/5000000000000000000000 : ℝ)*base91 + (53461043/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1072_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (61/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (164/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1072_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1072_s2_0 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-272619187/1250000000 : ℝ)*x 0 + (1104932861/2000000000 : ℝ)*x 1 + (5147026919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272619187/1250000000 : ℝ)^8265 ≤ (13206378633413/100000000000000 : ℝ)^6217 := by
    have hnat : (272619187 : ℕ)^8265*100000000000000^6217 ≤ 13206378633413^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272619187 1250000000 13206378633413 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104932861/2000000000 : ℝ)^8265 ≤ (5679714246897/12500000000000 : ℝ)^6217 := by
    have hnat : (1104932861 : ℕ)^8265*12500000000000^6217 ≤ 5679714246897^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104932861 2000000000 5679714246897 12500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5147026919/10000000000 : ℝ)^8265 ≤ (5169488422771/12500000000000 : ℝ)^6217 := by
    have hnat : (5147026919 : ℕ)^8265*12500000000000^6217 ≤ 5169488422771^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147026919 10000000000 5169488422771 12500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272619187/1250000000 : ℝ), (1104932861/2000000000 : ℝ), (5147026919/10000000000 : ℝ)] ![(13206378633413/100000000000000 : ℝ), (5679714246897/12500000000000 : ℝ), (5169488422771/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272619187/1250000000 : ℝ)|^8265 ≤ (13206378633413/100000000000000 : ℝ)^6217
        have hw : |(-272619187/1250000000 : ℝ)|=(272619187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104932861/2000000000 : ℝ)|^8265 ≤ (5679714246897/12500000000000 : ℝ)^6217
        have hw : |(1104932861/2000000000 : ℝ)|=(1104932861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5147026919/10000000000 : ℝ)|^8265 ≤ (5169488422771/12500000000000 : ℝ)^6217
        have hw : |(5147026919/10000000000 : ℝ)|=(5147026919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_1 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2688467231/5000000000 : ℝ)*x 0 + (-2377843477/10000000000 : ℝ)*x 1 + (5147027903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688467231/5000000000 : ℝ)^8265 ≤ (43829617187373/100000000000000 : ℝ)^6217 := by
    have hnat : (2688467231 : ℕ)^8265*100000000000000^6217 ≤ 43829617187373^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688467231 5000000000 43829617187373 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2377843477/10000000000 : ℝ)^8265 ≤ (14814464909059/100000000000000 : ℝ)^6217 := by
    have hnat : (2377843477 : ℕ)^8265*100000000000000^6217 ≤ 14814464909059^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2377843477 10000000000 14814464909059 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5147027903/10000000000 : ℝ)^8265 ≤ (41355917893027/100000000000000 : ℝ)^6217 := by
    have hnat : (5147027903 : ℕ)^8265*100000000000000^6217 ≤ 41355917893027^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147027903 10000000000 41355917893027 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688467231/5000000000 : ℝ), (-2377843477/10000000000 : ℝ), (5147027903/10000000000 : ℝ)] ![(43829617187373/100000000000000 : ℝ), (14814464909059/100000000000000 : ℝ), (41355917893027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688467231/5000000000 : ℝ)|^8265 ≤ (43829617187373/100000000000000 : ℝ)^6217
        have hw : |(2688467231/5000000000 : ℝ)|=(2688467231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2377843477/10000000000 : ℝ)|^8265 ≤ (14814464909059/100000000000000 : ℝ)^6217
        have hw : |(-2377843477/10000000000 : ℝ)|=(2377843477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5147027903/10000000000 : ℝ)|^8265 ≤ (41355917893027/100000000000000 : ℝ)^6217
        have hw : |(5147027903/10000000000 : ℝ)|=(5147027903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_2 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2688467007/5000000000 : ℝ)*x 0 + (643378549/1250000000 : ℝ)*x 1 + (-297230429/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688467007/5000000000 : ℝ)^8265 ≤ (8765922466511/20000000000000 : ℝ)^6217 := by
    have hnat : (2688467007 : ℕ)^8265*20000000000000^6217 ≤ 8765922466511^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688467007 5000000000 8765922466511 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643378549/1250000000 : ℝ)^8265 ≤ (10338980779103/25000000000000 : ℝ)^6217 := by
    have hnat : (643378549 : ℕ)^8265*25000000000000^6217 ≤ 10338980779103^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643378549 1250000000 10338980779103 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297230429/1250000000 : ℝ)^8265 ≤ (1851808067043/12500000000000 : ℝ)^6217 := by
    have hnat : (297230429 : ℕ)^8265*12500000000000^6217 ≤ 1851808067043^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297230429 1250000000 1851808067043 12500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688467007/5000000000 : ℝ), (643378549/1250000000 : ℝ), (-297230429/1250000000 : ℝ)] ![(8765922466511/20000000000000 : ℝ), (10338980779103/25000000000000 : ℝ), (1851808067043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688467007/5000000000 : ℝ)|^8265 ≤ (8765922466511/20000000000000 : ℝ)^6217
        have hw : |(2688467007/5000000000 : ℝ)|=(2688467007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643378549/1250000000 : ℝ)|^8265 ≤ (10338980779103/25000000000000 : ℝ)^6217
        have hw : |(643378549/1250000000 : ℝ)|=(643378549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-297230429/1250000000 : ℝ)|^8265 ≤ (1851808067043/12500000000000 : ℝ)^6217
        have hw : |(-297230429/1250000000 : ℝ)|=(297230429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_3 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090569243/2500000000 : ℝ)*x 0 + (62619103/156250000 : ℝ)*x 1 + (47486091/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090569243/2500000000 : ℝ)^8265 ≤ (33191571173587/100000000000000 : ℝ)^6217 := by
    have hnat : (1090569243 : ℕ)^8265*100000000000000^6217 ≤ 33191571173587^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090569243 2500000000 33191571173587 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62619103/156250000 : ℝ)^8265 ≤ (29653096820079/100000000000000 : ℝ)^6217 := by
    have hnat : (62619103 : ℕ)^8265*100000000000000^6217 ≤ 29653096820079^6217*156250000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62619103 156250000 29653096820079 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47486091/100000000 : ℝ)^8265 ≤ (37155331978953/100000000000000 : ℝ)^6217 := by
    have hnat : (47486091 : ℕ)^8265*100000000000000^6217 ≤ 37155331978953^6217*100000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47486091 100000000 37155331978953 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090569243/2500000000 : ℝ), (62619103/156250000 : ℝ), (47486091/100000000 : ℝ)] ![(33191571173587/100000000000000 : ℝ), (29653096820079/100000000000000 : ℝ), (37155331978953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090569243/2500000000 : ℝ)|^8265 ≤ (33191571173587/100000000000000 : ℝ)^6217
        have hw : |(1090569243/2500000000 : ℝ)|=(1090569243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62619103/156250000 : ℝ)|^8265 ≤ (29653096820079/100000000000000 : ℝ)^6217
        have hw : |(62619103/156250000 : ℝ)|=(62619103/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(47486091/100000000 : ℝ)|^8265 ≤ (37155331978953/100000000000000 : ℝ)^6217
        have hw : |(47486091/100000000 : ℝ)|=(47486091/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_4 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2181077039/10000000000 : ℝ)*x 0 + (321860271/625000000 : ℝ)*x 1 + (2760949287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181077039/10000000000 : ℝ)^8265 ≤ (13207373171741/100000000000000 : ℝ)^6217 := by
    have hnat : (2181077039 : ℕ)^8265*100000000000000^6217 ≤ 13207373171741^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181077039 10000000000 13207373171741 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321860271/625000000 : ℝ)^8265 ≤ (20692575197099/50000000000000 : ℝ)^6217 := by
    have hnat : (321860271 : ℕ)^8265*50000000000000^6217 ≤ 20692575197099^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321860271 625000000 20692575197099 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2760949287/5000000000 : ℝ)^8265 ≤ (11351869104691/25000000000000 : ℝ)^6217 := by
    have hnat : (2760949287 : ℕ)^8265*25000000000000^6217 ≤ 11351869104691^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760949287 5000000000 11351869104691 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2181077039/10000000000 : ℝ), (321860271/625000000 : ℝ), (2760949287/5000000000 : ℝ)] ![(13207373171741/100000000000000 : ℝ), (20692575197099/50000000000000 : ℝ), (11351869104691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2181077039/10000000000 : ℝ)|^8265 ≤ (13207373171741/100000000000000 : ℝ)^6217
        have hw : |(-2181077039/10000000000 : ℝ)|=(2181077039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321860271/625000000 : ℝ)|^8265 ≤ (20692575197099/50000000000000 : ℝ)^6217
        have hw : |(321860271/625000000 : ℝ)|=(321860271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2760949287/5000000000 : ℝ)|^8265 ≤ (11351869104691/25000000000000 : ℝ)^6217
        have hw : |(2760949287/5000000000 : ℝ)|=(2760949287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_5 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5281574039/10000000000 : ℝ)*x 0 + (-2002974991/10000000000 : ℝ)*x 1 + (690237333/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281574039/10000000000 : ℝ)^8265 ≤ (2139963033771/5000000000000 : ℝ)^6217 := by
    have hnat : (5281574039 : ℕ)^8265*5000000000000^6217 ≤ 2139963033771^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281574039 10000000000 2139963033771 5000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002974991/10000000000 : ℝ)^8265 ≤ (11793261914253/100000000000000 : ℝ)^6217 := by
    have hnat : (2002974991 : ℕ)^8265*100000000000000^6217 ≤ 11793261914253^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002974991 10000000000 11793261914253 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (690237333/1250000000 : ℝ)^8265 ≤ (45407477402647/100000000000000 : ℝ)^6217 := by
    have hnat : (690237333 : ℕ)^8265*100000000000000^6217 ≤ 45407477402647^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690237333 1250000000 45407477402647 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281574039/10000000000 : ℝ), (-2002974991/10000000000 : ℝ), (690237333/1250000000 : ℝ)] ![(2139963033771/5000000000000 : ℝ), (11793261914253/100000000000000 : ℝ), (45407477402647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281574039/10000000000 : ℝ)|^8265 ≤ (2139963033771/5000000000000 : ℝ)^6217
        have hw : |(5281574039/10000000000 : ℝ)|=(5281574039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2002974991/10000000000 : ℝ)|^8265 ≤ (11793261914253/100000000000000 : ℝ)^6217
        have hw : |(-2002974991/10000000000 : ℝ)|=(2002974991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(690237333/1250000000 : ℝ)|^8265 ≤ (45407477402647/100000000000000 : ℝ)^6217
        have hw : |(690237333/1250000000 : ℝ)|=(690237333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_6 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2640787141/5000000000 : ℝ)*x 0 + (2760949251/5000000000 : ℝ)*x 1 + (-2002974881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640787141/5000000000 : ℝ)^8265 ≤ (42799263293249/100000000000000 : ℝ)^6217 := by
    have hnat : (2640787141 : ℕ)^8265*100000000000000^6217 ≤ 42799263293249^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640787141 5000000000 42799263293249 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760949251/5000000000 : ℝ)^8265 ≤ (22703737815829/50000000000000 : ℝ)^6217 := by
    have hnat : (2760949251 : ℕ)^8265*50000000000000^6217 ≤ 22703737815829^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760949251 5000000000 22703737815829 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2002974881/10000000000 : ℝ)^8265 ≤ (11793261053233/100000000000000 : ℝ)^6217 := by
    have hnat : (2002974881 : ℕ)^8265*100000000000000^6217 ≤ 11793261053233^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002974881 10000000000 11793261053233 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640787141/5000000000 : ℝ), (2760949251/5000000000 : ℝ), (-2002974881/10000000000 : ℝ)] ![(42799263293249/100000000000000 : ℝ), (22703737815829/50000000000000 : ℝ), (11793261053233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640787141/5000000000 : ℝ)|^8265 ≤ (42799263293249/100000000000000 : ℝ)^6217
        have hw : |(2640787141/5000000000 : ℝ)|=(2640787141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2760949251/5000000000 : ℝ)|^8265 ≤ (22703737815829/50000000000000 : ℝ)^6217
        have hw : |(2760949251/5000000000 : ℝ)|=(2760949251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2002974881/10000000000 : ℝ)|^8265 ≤ (11793261053233/100000000000000 : ℝ)^6217
        have hw : |(-2002974881/10000000000 : ℝ)|=(2002974881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_7 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362516691/10000000000 : ℝ)*x 0 + (1185811457/2500000000 : ℝ)*x 1 + (2006522681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362516691/10000000000 : ℝ)^8265 ≤ (8298499003209/25000000000000 : ℝ)^6217 := by
    have hnat : (4362516691 : ℕ)^8265*25000000000000^6217 ≤ 8298499003209^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362516691 10000000000 8298499003209 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1185811457/2500000000 : ℝ)^8265 ≤ (37099553621721/100000000000000 : ℝ)^6217 := by
    have hnat : (1185811457 : ℕ)^8265*100000000000000^6217 ≤ 37099553621721^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185811457 2500000000 37099553621721 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006522681/5000000000 : ℝ)^8265 ≤ (5941290070203/20000000000000 : ℝ)^6217 := by
    have hnat : (2006522681 : ℕ)^8265*20000000000000^6217 ≤ 5941290070203^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006522681 5000000000 5941290070203 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362516691/10000000000 : ℝ), (1185811457/2500000000 : ℝ), (2006522681/5000000000 : ℝ)] ![(8298499003209/25000000000000 : ℝ), (37099553621721/100000000000000 : ℝ), (5941290070203/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362516691/10000000000 : ℝ)|^8265 ≤ (8298499003209/25000000000000 : ℝ)^6217
        have hw : |(4362516691/10000000000 : ℝ)|=(4362516691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1185811457/2500000000 : ℝ)|^8265 ≤ (37099553621721/100000000000000 : ℝ)^6217
        have hw : |(1185811457/2500000000 : ℝ)|=(1185811457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2006522681/5000000000 : ℝ)|^8265 ≤ (5941290070203/20000000000000 : ℝ)^6217
        have hw : |(2006522681/5000000000 : ℝ)|=(2006522681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_8 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-50001457/5000000000 : ℝ)*x 0 + (1185447141/2000000000 : ℝ)*x 1 + (5927049349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50001457/5000000000 : ℝ)^8265 ≤ (21937046501/10000000000000 : ℝ)^6217 := by
    have hnat : (50001457 : ℕ)^8265*10000000000000^6217 ≤ 21937046501^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50001457 5000000000 21937046501 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1185447141/2000000000 : ℝ)^8265 ≤ (12472839356427/25000000000000 : ℝ)^6217 := by
    have hnat : (1185447141 : ℕ)^8265*25000000000000^6217 ≤ 12472839356427^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185447141 2000000000 12472839356427 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5927049349/10000000000 : ℝ)^8265 ≤ (12472318022183/25000000000000 : ℝ)^6217 := by
    have hnat : (5927049349 : ℕ)^8265*25000000000000^6217 ≤ 12472318022183^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5927049349 10000000000 12472318022183 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50001457/5000000000 : ℝ), (1185447141/2000000000 : ℝ), (5927049349/10000000000 : ℝ)] ![(21937046501/10000000000000 : ℝ), (12472839356427/25000000000000 : ℝ), (12472318022183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50001457/5000000000 : ℝ)|^8265 ≤ (21937046501/10000000000000 : ℝ)^6217
        have hw : |(-50001457/5000000000 : ℝ)|=(50001457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1185447141/2000000000 : ℝ)|^8265 ≤ (12472839356427/25000000000000 : ℝ)^6217
        have hw : |(1185447141/2000000000 : ℝ)|=(1185447141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5927049349/10000000000 : ℝ)|^8265 ≤ (12472318022183/25000000000000 : ℝ)^6217
        have hw : |(5927049349/10000000000 : ℝ)|=(5927049349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_9 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (6215531/78125000 : ℝ)*x 0 + (-2483345519/5000000000 : ℝ)*x 1 + (6560831631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6215531/78125000 : ℝ)^8265 ≤ (172792008119/5000000000000 : ℝ)^6217 := by
    have hnat : (6215531 : ℕ)^8265*5000000000000^6217 ≤ 172792008119^6217*78125000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6215531 78125000 172792008119 5000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2483345519/5000000000 : ℝ)^8265 ≤ (39440806410169/100000000000000 : ℝ)^6217 := by
    have hnat : (2483345519 : ℕ)^8265*100000000000000^6217 ≤ 39440806410169^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2483345519 5000000000 39440806410169 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6560831631/10000000000 : ℝ)^8265 ≤ (1427583835177/2500000000000 : ℝ)^6217 := by
    have hnat : (6560831631 : ℕ)^8265*2500000000000^6217 ≤ 1427583835177^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6560831631 10000000000 1427583835177 2500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6215531/78125000 : ℝ), (-2483345519/5000000000 : ℝ), (6560831631/10000000000 : ℝ)] ![(172792008119/5000000000000 : ℝ), (39440806410169/100000000000000 : ℝ), (1427583835177/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6215531/78125000 : ℝ)|^8265 ≤ (172792008119/5000000000000 : ℝ)^6217
        have hw : |(6215531/78125000 : ℝ)|=(6215531/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2483345519/5000000000 : ℝ)|^8265 ≤ (39440806410169/100000000000000 : ℝ)^6217
        have hw : |(-2483345519/5000000000 : ℝ)|=(2483345519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6560831631/10000000000 : ℝ)|^8265 ≤ (1427583835177/2500000000000 : ℝ)^6217
        have hw : |(6560831631/10000000000 : ℝ)|=(6560831631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_10 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (397110521/5000000000 : ℝ)*x 0 + (6557313509/10000000000 : ℝ)*x 1 + (-4971293473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397110521/5000000000 : ℝ)^8265 ≤ (3447948845759/100000000000000 : ℝ)^6217 := by
    have hnat : (397110521 : ℕ)^8265*100000000000000^6217 ≤ 3447948845759^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397110521 5000000000 3447948845759 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6557313509/10000000000 : ℝ)^8265 ≤ (14265662348193/25000000000000 : ℝ)^6217 := by
    have hnat : (6557313509 : ℕ)^8265*25000000000000^6217 ≤ 14265662348193^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6557313509 10000000000 14265662348193 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4971293473/10000000000 : ℝ)^8265 ≤ (39489401743227/100000000000000 : ℝ)^6217 := by
    have hnat : (4971293473 : ℕ)^8265*100000000000000^6217 ≤ 39489401743227^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4971293473 10000000000 39489401743227 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(397110521/5000000000 : ℝ), (6557313509/10000000000 : ℝ), (-4971293473/10000000000 : ℝ)] ![(3447948845759/100000000000000 : ℝ), (14265662348193/25000000000000 : ℝ), (39489401743227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(397110521/5000000000 : ℝ)|^8265 ≤ (3447948845759/100000000000000 : ℝ)^6217
        have hw : |(397110521/5000000000 : ℝ)|=(397110521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6557313509/10000000000 : ℝ)|^8265 ≤ (14265662348193/25000000000000 : ℝ)^6217
        have hw : |(6557313509/10000000000 : ℝ)|=(6557313509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4971293473/10000000000 : ℝ)|^8265 ≤ (39489401743227/100000000000000 : ℝ)^6217
        have hw : |(-4971293473/10000000000 : ℝ)|=(4971293473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s2_11 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (419752291/10000000000 : ℝ)*x 0 + (5868921703/10000000000 : ℝ)*x 1 + (587279877/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419752291/10000000000 : ℝ)^8265 ≤ (1476999577181/100000000000000 : ℝ)^6217 := by
    have hnat : (419752291 : ℕ)^8265*100000000000000^6217 ≤ 1476999577181^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419752291 10000000000 1476999577181 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5868921703/10000000000 : ℝ)^8265 ≤ (49239875946621/100000000000000 : ℝ)^6217 := by
    have hnat : (5868921703 : ℕ)^8265*100000000000000^6217 ≤ 49239875946621^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5868921703 10000000000 49239875946621 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587279877/1000000000 : ℝ)^8265 ≤ (24641562229653/50000000000000 : ℝ)^6217 := by
    have hnat : (587279877 : ℕ)^8265*50000000000000^6217 ≤ 24641562229653^6217*1000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587279877 1000000000 24641562229653 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419752291/10000000000 : ℝ), (5868921703/10000000000 : ℝ), (587279877/1000000000 : ℝ)] ![(1476999577181/100000000000000 : ℝ), (49239875946621/100000000000000 : ℝ), (24641562229653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419752291/10000000000 : ℝ)|^8265 ≤ (1476999577181/100000000000000 : ℝ)^6217
        have hw : |(419752291/10000000000 : ℝ)|=(419752291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5868921703/10000000000 : ℝ)|^8265 ≤ (49239875946621/100000000000000 : ℝ)^6217
        have hw : |(5868921703/10000000000 : ℝ)|=(5868921703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(587279877/1000000000 : ℝ)|^8265 ≤ (24641562229653/50000000000000 : ℝ)^6217
        have hw : |(587279877/1000000000 : ℝ)|=(587279877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1072_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (164/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (8741/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16721/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (164/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (164/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (164/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (164/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (164/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (164/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (164/3125 : ℝ) ^ (1033/256 : ℝ) ≤ (341936209270883/50000000000000000000 : ℝ) := by
    have hpowers : (164/3125 : ℝ)^1033 ≤ (341936209270883/50000000000000000000 : ℝ)^256 := by
      have hnat : (164 : ℕ)^1033*50000000000000000000^256 ≤ 341936209270883^256*3125^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        164 3125 341936209270883 50000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (164/3125 : ℝ)) (X := (341936209270883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hpowhi : (10381/50000 : ℝ) ^ (1033/256 : ℝ) ≤ (87911258243846691/50000000000000000000 : ℝ) := by
    have hpowers : (10381/50000 : ℝ)^1033 ≤ (87911258243846691/50000000000000000000 : ℝ)^256 := by
      have hnat : (10381 : ℕ)^1033*50000000000000000000^256 ≤ 87911258243846691^256*50000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10381 50000 87911258243846691 50000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10381/50000 : ℝ)) (X := (87911258243846691/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000341936209270883/25000000000000000000 : ℝ) ≤ (10000033895535063/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (25000341936209270883/25000000000000000000 : ℝ)^256 ≤ (10000033895535063/10000000000000000 : ℝ)^1033 := by
      have hnat : (25000341936209270883 : ℕ)^256*10000000000000000^1033 ≤ 10000033895535063^1033*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000341936209270883 25000000000000000000 10000033895535063 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000033895535063/10000000000000000 : ℝ)) (X := (25000341936209270883/25000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25044126597226558787/25000000000000000000 : ℝ) ≤ (10004371313771621/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (25044126597226558787/25000000000000000000 : ℝ)^256 ≤ (10004371313771621/10000000000000000 : ℝ)^1033 := by
      have hnat : (25044126597226558787 : ℕ)^256*10000000000000000^1033 ≤ 10004371313771621^1033*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25044126597226558787 25000000000000000000 10004371313771621 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004371313771621/10000000000000000 : ℝ)) (X := (25044126597226558787/25000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25087911258243846691/25000000000000000000 : ℝ) ≤ (10008708732008179/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (25087911258243846691/25000000000000000000 : ℝ)^256 ≤ (10008708732008179/10000000000000000 : ℝ)^1033 := by
      have hnat : (25087911258243846691 : ℕ)^256*10000000000000000^1033 ≤ 10008708732008179^1033*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25087911258243846691 25000000000000000000 10008708732008179 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008708732008179/10000000000000000 : ℝ)) (X := (25087911258243846691/25000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(341936209270883/50000000000000000000 : ℝ) ≤ ((77547500156760027307/77570000000000000000 : ℝ)+2*(2168709118279/775700000000000 : ℝ)*(164/3125 : ℝ))^(1033/256 : ℝ) := by
    rw [show (77547500156760027307/77570000000000000000 : ℝ)+2*(2168709118279/775700000000000 : ℝ)*(164/3125 : ℝ)=(10000033895535063/10000000000000000 : ℝ) by norm_num, show 1+2*(341936209270883/50000000000000000000 : ℝ)=(25000341936209270883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(87911258243846691/50000000000000000000 : ℝ)+(341936209270883/50000000000000000000 : ℝ) ≤ ((77547500156760027307/77570000000000000000 : ℝ)+(2168709118279/775700000000000 : ℝ)*((10381/50000 : ℝ)+(164/3125 : ℝ)))^(1033/256 : ℝ) := by
    rw [show (77547500156760027307/77570000000000000000 : ℝ)+(2168709118279/775700000000000 : ℝ)*((10381/50000 : ℝ)+(164/3125 : ℝ))=(10004371313771621/10000000000000000 : ℝ) by norm_num, show 1+(87911258243846691/50000000000000000000 : ℝ)+(341936209270883/50000000000000000000 : ℝ)=(25044126597226558787/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(87911258243846691/50000000000000000000 : ℝ) ≤ ((77547500156760027307/77570000000000000000 : ℝ)+2*(2168709118279/775700000000000 : ℝ)*(10381/50000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (77547500156760027307/77570000000000000000 : ℝ)+2*(2168709118279/775700000000000 : ℝ)*(10381/50000 : ℝ)=(10008708732008179/10000000000000000 : ℝ) by norm_num, show 1+2*(87911258243846691/50000000000000000000 : ℝ)=(25087911258243846691/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (77547500156760027307/77570000000000000000 : ℝ)*(X 1 0+X 2 0)+(2168709118279/775700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (164/3125 : ℝ)) (hi := (10381/50000 : ℝ)) (c := (77547500156760027307/77570000000000000000 : ℝ)) (alpha := (2168709118279/775700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (77547500156760027307/77570000000000000000 : ℝ)*(X 0 1+X 2 1)+(2168709118279/775700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (164/3125 : ℝ)) (hi := (10381/50000 : ℝ)) (c := (77547500156760027307/77570000000000000000 : ℝ)) (alpha := (2168709118279/775700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (77547500156760027307/77570000000000000000 : ℝ)*(X 0 2+X 1 2)+(2168709118279/775700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (164/3125 : ℝ)) (hi := (10381/50000 : ℝ)) (c := (77547500156760027307/77570000000000000000 : ℝ)) (alpha := (2168709118279/775700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-272619187/1250000000 : ℝ)*X 0 0+(1104932861/2000000000 : ℝ)*X 0 1+(5147026919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688467231/5000000000 : ℝ)*X 1 0+(-2377843477/10000000000 : ℝ)*X 1 1+(5147027903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688467007/5000000000 : ℝ)*X 2 0+(643378549/1250000000 : ℝ)*X 2 1+(-297230429/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090569243/2500000000 : ℝ)*X 0 0+(62619103/156250000 : ℝ)*X 0 1+(47486091/100000000 : ℝ)*X 0 2+(1090569243/2500000000 : ℝ)*X 1 0+(62619103/156250000 : ℝ)*X 1 1+(47486091/100000000 : ℝ)*X 1 2+(1090569243/2500000000 : ℝ)*X 2 0+(62619103/156250000 : ℝ)*X 2 1+(47486091/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2181077039/10000000000 : ℝ)*X 0 0+(321860271/625000000 : ℝ)*X 0 1+(2760949287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5281574039/10000000000 : ℝ)*X 1 0+(-2002974991/10000000000 : ℝ)*X 1 1+(690237333/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640787141/5000000000 : ℝ)*X 2 0+(2760949251/5000000000 : ℝ)*X 2 1+(-2002974881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362516691/10000000000 : ℝ)*X 0 0+(1185811457/2500000000 : ℝ)*X 0 1+(2006522681/5000000000 : ℝ)*X 0 2+(4362516691/10000000000 : ℝ)*X 1 0+(1185811457/2500000000 : ℝ)*X 1 1+(2006522681/5000000000 : ℝ)*X 1 2+(4362516691/10000000000 : ℝ)*X 2 0+(1185811457/2500000000 : ℝ)*X 2 1+(2006522681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-50001457/5000000000 : ℝ)*X 0 0+(1185447141/2000000000 : ℝ)*X 0 1+(5927049349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((6215531/78125000 : ℝ)*X 1 0+(-2483345519/5000000000 : ℝ)*X 1 1+(6560831631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((397110521/5000000000 : ℝ)*X 2 0+(6557313509/10000000000 : ℝ)*X 2 1+(-4971293473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((419752291/10000000000 : ℝ)*X 0 0+(5868921703/10000000000 : ℝ)*X 0 1+(587279877/1000000000 : ℝ)*X 0 2+(419752291/10000000000 : ℝ)*X 1 0+(5868921703/10000000000 : ℝ)*X 1 1+(587279877/1000000000 : ℝ)*X 1 2+(419752291/10000000000 : ℝ)*X 2 0+(5868921703/10000000000 : ℝ)*X 2 1+(587279877/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29335716891161338794719624223/3878500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1998822032500737/100000000000000 : ℝ)*(major0) + (1998822032500737/100000000000000 : ℝ)*(major1) + (1998822032500737/100000000000000 : ℝ)*(major2) + (331008157131531/12500000000000 : ℝ)*(sp0) + (662018815190487/25000000000000 : ℝ)*(sp1) + (1324038838842333/50000000000000 : ℝ)*(sp2) + (269910488991317/20000000000000 : ℝ)*(sp3) + (22251784743/100000000000000 : ℝ)*(sp4) + (12277546167/100000000000000 : ℝ)*(sp5) + (5037095339/50000000000000 : ℝ)*(sp6) + (370795651/20000000000000 : ℝ)*(sp8) + (456126783/25000000000000 : ℝ)*(sp9) + (1610939903/100000000000000 : ℝ)*(sp10) + (200510711/10000000000000 : ℝ)*(sp11) + (269910890012739/20000000000000 : ℝ)*(f.failure) + (2648089362815247/100000000000000 : ℝ)*(f.sum) + (3349787890297/2424062500000000000000000000 : ℝ)*base66 + (67688960882038925259/7757000000000000000000000000000000 : ℝ)*base67 + (11505786543906925259/7757000000000000000000000000000000 : ℝ)*base69 + (6303845680735074741/7757000000000000000000000000000000 : ℝ)*base72 + (21840249137531/19392500000000000000000000000 : ℝ)*base74 + (3493411869811925259/7757000000000000000000000000000000 : ℝ)*base75 + (6696452125752074741/7757000000000000000000000000000000 : ℝ)*base78 + (10759383833094925259/7757000000000000000000000000000000 : ℝ)*base79 + (10143222468397/9696250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (398247/2000000000000000000000 : ℝ)*base89 + (398247/2000000000000000000000 : ℝ)*base91 + (398247/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30681060972573191677007863449/3878500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202834610035703/10000000000000 : ℝ)*(major0) + (202834610035703/10000000000000 : ℝ)*(major1) + (2028346100357031/100000000000000 : ℝ)*(major2) + (723497809/100000000000000 : ℝ)*(sp1) + (23409981/12500000000000 : ℝ)*(sp2) + (33110541/10000000000000 : ℝ)*(sp3) + (268720261415427/10000000000000 : ℝ)*(sp4) + (1343601225071191/50000000000000 : ℝ)*(sp5) + (2687202852360633/100000000000000 : ℝ)*(sp6) + (342371852421329/25000000000000 : ℝ)*(sp7) + (963482767/100000000000000 : ℝ)*(sp8) + (201998423/50000000000000 : ℝ)*(sp9) + (134499139/25000000000000 : ℝ)*(sp10) + (77325169/12500000000000 : ℝ)*(sp11) + (684744179696039/50000000000000 : ℝ)*(f.failure) + (1343601788818519/50000000000000 : ℝ)*(f.sum) + (64685845930781/77570000000000000000000000000 : ℝ)*base66 + (31675233901131821/775700000000000000000000000000000 : ℝ)*base67 + (29138091456231445517/7757000000000000000000000000000000 : ℝ)*base69 + (4001151532302968179/775700000000000000000000000000000 : ℝ)*base72 + (121762975221951/77570000000000000000000000000 : ℝ)*base74 + (30147290048365445517/7757000000000000000000000000000000 : ℝ)*base75 + (6801984117337958179/775700000000000000000000000000000 : ℝ)*base78 + (224484139681641821/775700000000000000000000000000000 : ℝ)*base79 + (29156241019021/7757000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (45289147/5000000000000000000000 : ℝ)*base89 + (45289147/5000000000000000000000 : ℝ)*base91 + (4710853/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1072_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (164/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16721/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1072_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1072_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16721/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1072_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1072_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1072_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16721/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1072_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
