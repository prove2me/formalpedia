-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1358_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:10:26.837993+00:00
-- url     : https://prove2.me/submissions/3b3d7865-13b0-4eee-a60e-d90c3fa72227

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
theorem support_rectangle_w1358_s0_0 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-899862607/5000000000 : ℝ)*x 0 + (2995017467/5000000000 : ℝ)*x 1 + (1203678039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899862607/5000000000 : ℝ)^2159 ≤ (5280116004339/50000000000000 : ℝ)^1647 := by
    have hnat : (899862607 : ℕ)^2159*50000000000000^1647 ≤ 5280116004339^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899862607 5000000000 5280116004339 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2995017467/5000000000 : ℝ)^2159 ≤ (51078626359423/100000000000000 : ℝ)^1647 := by
    have hnat : (2995017467 : ℕ)^2159*100000000000000^1647 ≤ 51078626359423^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995017467 5000000000 51078626359423 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203678039/2500000000 : ℝ)^2159 ≤ (38361141619681/100000000000000 : ℝ)^1647 := by
    have hnat : (1203678039 : ℕ)^2159*100000000000000^1647 ≤ 38361141619681^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203678039 2500000000 38361141619681 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-899862607/5000000000 : ℝ), (2995017467/5000000000 : ℝ), (1203678039/2500000000 : ℝ)] ![(5280116004339/50000000000000 : ℝ), (51078626359423/100000000000000 : ℝ), (38361141619681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-899862607/5000000000 : ℝ)|^2159 ≤ (5280116004339/50000000000000 : ℝ)^1647
        have hw : |(-899862607/5000000000 : ℝ)|=(899862607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2995017467/5000000000 : ℝ)|^2159 ≤ (51078626359423/100000000000000 : ℝ)^1647
        have hw : |(2995017467/5000000000 : ℝ)|=(2995017467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203678039/2500000000 : ℝ)|^2159 ≤ (38361141619681/100000000000000 : ℝ)^1647
        have hw : |(1203678039/2500000000 : ℝ)|=(1203678039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s0_1 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5500021629/10000000000 : ℝ)*x 0 + (-2467000221/10000000000 : ℝ)*x 1 + (1203678161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5500021629/10000000000 : ℝ)^2159 ≤ (1141805003621/2500000000000 : ℝ)^1647 := by
    have hnat : (5500021629 : ℕ)^2159*2500000000000^1647 ≤ 1141805003621^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500021629 10000000000 1141805003621 2500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2467000221/10000000000 : ℝ)^2159 ≤ (3193330626433/20000000000000 : ℝ)^1647 := by
    have hnat : (2467000221 : ℕ)^2159*20000000000000^1647 ≤ 3193330626433^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2467000221 10000000000 3193330626433 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203678161/2500000000 : ℝ)^2159 ≤ (3836114671651/10000000000000 : ℝ)^1647 := by
    have hnat : (1203678161 : ℕ)^2159*10000000000000^1647 ≤ 3836114671651^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203678161 2500000000 3836114671651 10000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5500021629/10000000000 : ℝ), (-2467000221/10000000000 : ℝ), (1203678161/2500000000 : ℝ)] ![(1141805003621/2500000000000 : ℝ), (3193330626433/20000000000000 : ℝ), (3836114671651/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5500021629/10000000000 : ℝ)|^2159 ≤ (1141805003621/2500000000000 : ℝ)^1647
        have hw : |(5500021629/10000000000 : ℝ)|=(5500021629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2467000221/10000000000 : ℝ)|^2159 ≤ (3193330626433/20000000000000 : ℝ)^1647
        have hw : |(-2467000221/10000000000 : ℝ)|=(2467000221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203678161/2500000000 : ℝ)|^2159 ≤ (3836114671651/10000000000000 : ℝ)^1647
        have hw : |(1203678161/2500000000 : ℝ)|=(1203678161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s0_2 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2750010741/5000000000 : ℝ)*x 0 + (4814712177/10000000000 : ℝ)*x 1 + (-308375123/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750010741/5000000000 : ℝ)^2159 ≤ (22836099272339/50000000000000 : ℝ)^1647 := by
    have hnat : (2750010741 : ℕ)^2159*50000000000000^1647 ≤ 22836099272339^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750010741 5000000000 22836099272339 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4814712177/10000000000 : ℝ)^2159 ≤ (38361141839011/100000000000000 : ℝ)^1647 := by
    have hnat : (4814712177 : ℕ)^2159*100000000000000^1647 ≤ 38361141839011^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814712177 10000000000 38361141839011 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (308375123/1250000000 : ℝ)^2159 ≤ (15592441021/97656250000 : ℝ)^1647 := by
    have hnat : (308375123 : ℕ)^2159*97656250000^1647 ≤ 15592441021^1647*1250000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308375123 1250000000 15592441021 97656250000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750010741/5000000000 : ℝ), (4814712177/10000000000 : ℝ), (-308375123/1250000000 : ℝ)] ![(22836099272339/50000000000000 : ℝ), (38361141839011/100000000000000 : ℝ), (15592441021/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750010741/5000000000 : ℝ)|^2159 ≤ (22836099272339/50000000000000 : ℝ)^1647
        have hw : |(2750010741/5000000000 : ℝ)|=(2750010741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4814712177/10000000000 : ℝ)|^2159 ≤ (38361141839011/100000000000000 : ℝ)^1647
        have hw : |(4814712177/10000000000 : ℝ)|=(4814712177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-308375123/1250000000 : ℝ)|^2159 ≤ (15592441021/97656250000 : ℝ)^1647
        have hw : |(-308375123/1250000000 : ℝ)|=(308375123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s0_3 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (522045179/1250000000 : ℝ)*x 0 + (776452577/2500000000 : ℝ)*x 1 + (2791218047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522045179/1250000000 : ℝ)^2159 ≤ (7958958653511/25000000000000 : ℝ)^1647 := by
    have hnat : (522045179 : ℕ)^2159*25000000000000^1647 ≤ 7958958653511^1647*1250000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522045179 1250000000 7958958653511 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776452577/2500000000 : ℝ)^2159 ≤ (21592763977129/100000000000000 : ℝ)^1647 := by
    have hnat : (776452577 : ℕ)^2159*100000000000000^1647 ≤ 21592763977129^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776452577 2500000000 21592763977129 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2791218047/5000000000 : ℝ)^2159 ≤ (23285700699219/50000000000000 : ℝ)^1647 := by
    have hnat : (2791218047 : ℕ)^2159*50000000000000^1647 ≤ 23285700699219^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791218047 5000000000 23285700699219 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522045179/1250000000 : ℝ), (776452577/2500000000 : ℝ), (2791218047/5000000000 : ℝ)] ![(7958958653511/25000000000000 : ℝ), (21592763977129/100000000000000 : ℝ), (23285700699219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522045179/1250000000 : ℝ)|^2159 ≤ (7958958653511/25000000000000 : ℝ)^1647
        have hw : |(522045179/1250000000 : ℝ)|=(522045179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776452577/2500000000 : ℝ)|^2159 ≤ (21592763977129/100000000000000 : ℝ)^1647
        have hw : |(776452577/2500000000 : ℝ)|=(776452577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2791218047/5000000000 : ℝ)|^2159 ≤ (23285700699219/50000000000000 : ℝ)^1647
        have hw : |(2791218047/5000000000 : ℝ)|=(2791218047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s0_4 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1804098583/10000000000 : ℝ)*x 0 + (302808291/625000000 : ℝ)*x 1 + (1489683711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1804098583/10000000000 : ℝ)^2159 ≤ (5296941828363/50000000000000 : ℝ)^1647 := by
    have hnat : (1804098583 : ℕ)^2159*50000000000000^1647 ≤ 5296941828363^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804098583 10000000000 5296941828363 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302808291/625000000 : ℝ)^2159 ≤ (38677081734609/100000000000000 : ℝ)^1647 := by
    have hnat : (302808291 : ℕ)^2159*100000000000000^1647 ≤ 38677081734609^1647*625000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302808291 625000000 38677081734609 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1489683711/2500000000 : ℝ)^2159 ≤ (12682258650981/25000000000000 : ℝ)^1647 := by
    have hnat : (1489683711 : ℕ)^2159*25000000000000^1647 ≤ 12682258650981^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489683711 2500000000 12682258650981 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1804098583/10000000000 : ℝ), (302808291/625000000 : ℝ), (1489683711/2500000000 : ℝ)] ![(5296941828363/50000000000000 : ℝ), (38677081734609/100000000000000 : ℝ), (12682258650981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1804098583/10000000000 : ℝ)|^2159 ≤ (5296941828363/50000000000000 : ℝ)^1647
        have hw : |(-1804098583/10000000000 : ℝ)|=(1804098583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(302808291/625000000 : ℝ)|^2159 ≤ (38677081734609/100000000000000 : ℝ)^1647
        have hw : |(302808291/625000000 : ℝ)|=(302808291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1489683711/2500000000 : ℝ)|^2159 ≤ (12682258650981/25000000000000 : ℝ)^1647
        have hw : |(1489683711/2500000000 : ℝ)|=(1489683711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s0_5 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5179609039/10000000000 : ℝ)*x 0 + (-661489821/5000000000 : ℝ)*x 1 + (5958734263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179609039/10000000000 : ℝ)^2159 ≤ (659630927229/1562500000000 : ℝ)^1647 := by
    have hnat : (5179609039 : ℕ)^2159*1562500000000^1647 ≤ 659630927229^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179609039 10000000000 659630927229 1562500000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (661489821/5000000000 : ℝ)^2159 ≤ (3527296263597/50000000000000 : ℝ)^1647 := by
    have hnat : (661489821 : ℕ)^2159*50000000000000^1647 ≤ 3527296263597^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661489821 5000000000 3527296263597 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5958734263/10000000000 : ℝ)^2159 ≤ (50729028120003/100000000000000 : ℝ)^1647 := by
    have hnat : (5958734263 : ℕ)^2159*100000000000000^1647 ≤ 50729028120003^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5958734263 10000000000 50729028120003 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179609039/10000000000 : ℝ), (-661489821/5000000000 : ℝ), (5958734263/10000000000 : ℝ)] ![(659630927229/1562500000000 : ℝ), (3527296263597/50000000000000 : ℝ), (50729028120003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179609039/10000000000 : ℝ)|^2159 ≤ (659630927229/1562500000000 : ℝ)^1647
        have hw : |(5179609039/10000000000 : ℝ)|=(5179609039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-661489821/5000000000 : ℝ)|^2159 ≤ (3527296263597/50000000000000 : ℝ)^1647
        have hw : |(-661489821/5000000000 : ℝ)|=(661489821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5958734263/10000000000 : ℝ)|^2159 ≤ (50729028120003/100000000000000 : ℝ)^1647
        have hw : |(5958734263/10000000000 : ℝ)|=(5958734263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s0_6 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2589804433/5000000000 : ℝ)*x 0 + (595873501/1000000000 : ℝ)*x 1 + (-165372339/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589804433/5000000000 : ℝ)^2159 ≤ (8443275498857/20000000000000 : ℝ)^1647 := by
    have hnat : (2589804433 : ℕ)^2159*20000000000000^1647 ≤ 8443275498857^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589804433 5000000000 8443275498857 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (595873501/1000000000 : ℝ)^2159 ≤ (50729036456473/100000000000000 : ℝ)^1647 := by
    have hnat : (595873501 : ℕ)^2159*100000000000000^1647 ≤ 50729036456473^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595873501 1000000000 50729036456473 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165372339/1250000000 : ℝ)^2159 ≤ (1410917205297/20000000000000 : ℝ)^1647 := by
    have hnat : (165372339 : ℕ)^2159*20000000000000^1647 ≤ 1410917205297^1647*1250000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165372339 1250000000 1410917205297 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589804433/5000000000 : ℝ), (595873501/1000000000 : ℝ), (-165372339/1250000000 : ℝ)] ![(8443275498857/20000000000000 : ℝ), (50729036456473/100000000000000 : ℝ), (1410917205297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589804433/5000000000 : ℝ)|^2159 ≤ (8443275498857/20000000000000 : ℝ)^1647
        have hw : |(2589804433/5000000000 : ℝ)|=(2589804433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(595873501/1000000000 : ℝ)|^2159 ≤ (50729036456473/100000000000000 : ℝ)^1647
        have hw : |(595873501/1000000000 : ℝ)|=(595873501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-165372339/1250000000 : ℝ)|^2159 ≤ (1410917205297/20000000000000 : ℝ)^1647
        have hw : |(-165372339/1250000000 : ℝ)|=(165372339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s0_7 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1046393291/2500000000 : ℝ)*x 0 + (1379689333/2500000000 : ℝ)*x 1 + (396470677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046393291/2500000000 : ℝ)^2159 ≤ (1995494689647/6250000000000 : ℝ)^1647 := by
    have hnat : (1046393291 : ℕ)^2159*6250000000000^1647 ≤ 1995494689647^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046393291 2500000000 1995494689647 6250000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379689333/2500000000 : ℝ)^2159 ≤ (9175250938991/20000000000000 : ℝ)^1647 := by
    have hnat : (1379689333 : ℕ)^2159*20000000000000^1647 ≤ 9175250938991^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379689333 2500000000 9175250938991 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396470677/1250000000 : ℝ)^2159 ≤ (11097915125987/50000000000000 : ℝ)^1647 := by
    have hnat : (396470677 : ℕ)^2159*50000000000000^1647 ≤ 11097915125987^1647*1250000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396470677 1250000000 11097915125987 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046393291/2500000000 : ℝ), (1379689333/2500000000 : ℝ), (396470677/1250000000 : ℝ)] ![(1995494689647/6250000000000 : ℝ), (9175250938991/20000000000000 : ℝ), (11097915125987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046393291/2500000000 : ℝ)|^2159 ≤ (1995494689647/6250000000000 : ℝ)^1647
        have hw : |(1046393291/2500000000 : ℝ)|=(1046393291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379689333/2500000000 : ℝ)|^2159 ≤ (9175250938991/20000000000000 : ℝ)^1647
        have hw : |(1379689333/2500000000 : ℝ)|=(1379689333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396470677/1250000000 : ℝ)|^2159 ≤ (11097915125987/50000000000000 : ℝ)^1647
        have hw : |(396470677/1250000000 : ℝ)|=(396470677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1358_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (767/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6689/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4317/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4317 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4317*1^1024 ≤ 0^1024*1^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4317/1024 : ℝ) ≤ (2100663204204858477/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4317 ≤ (2100663204204858477/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4317*100000000000000000000^1024 ≤ 2100663204204858477^1024*5^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2100663204204858477 100000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2100663204204858477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4317 := by
      have hnat : (1 : ℕ)^1024*1^4317 ≤ 1^4317*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102100663204204858477/100000000000000000000 : ℝ) ≤ (10049433740071341/10000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (102100663204204858477/100000000000000000000 : ℝ)^1024 ≤ (10049433740071341/10000000000000000 : ℝ)^4317 := by
      have hnat : (102100663204204858477 : ℕ)^1024*10000000000000000^4317 ≤ 10049433740071341^4317*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102100663204204858477 100000000000000000000 10049433740071341 10000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049433740071341/10000000000000000 : ℝ)) (X := (102100663204204858477/100000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52100663204204858477/50000000000000000000 : ℝ) ≤ (5049433740071341/5000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (52100663204204858477/50000000000000000000 : ℝ)^1024 ≤ (5049433740071341/5000000000000000 : ℝ)^4317 := by
      have hnat : (52100663204204858477 : ℕ)^1024*5000000000000000^4317 ≤ 5049433740071341^4317*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52100663204204858477 50000000000000000000 5049433740071341 5000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049433740071341/5000000000000000 : ℝ)) (X := (52100663204204858477/50000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(49433740071341/4000000000000000 : ℝ)*(0 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(49433740071341/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2100663204204858477/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(49433740071341/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4317/1024 : ℝ) := by
    rw [show (1 : ℝ)+(49433740071341/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10049433740071341/10000000000000000 : ℝ) by norm_num, show 1+(2100663204204858477/100000000000000000000 : ℝ)+(0 : ℝ)=(102100663204204858477/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2100663204204858477/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(49433740071341/4000000000000000 : ℝ)*(2/5 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(49433740071341/4000000000000000 : ℝ)*(2/5 : ℝ)=(5049433740071341/5000000000000000 : ℝ) by norm_num, show 1+2*(2100663204204858477/100000000000000000000 : ℝ)=(52100663204204858477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(49433740071341/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49433740071341/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(49433740071341/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49433740071341/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(49433740071341/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49433740071341/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-899862607/5000000000 : ℝ)*X 0 0+(2995017467/5000000000 : ℝ)*X 0 1+(1203678039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5500021629/10000000000 : ℝ)*X 1 0+(-2467000221/10000000000 : ℝ)*X 1 1+(1203678161/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2750010741/5000000000 : ℝ)*X 2 0+(4814712177/10000000000 : ℝ)*X 2 1+(-308375123/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((522045179/1250000000 : ℝ)*X 0 0+(776452577/2500000000 : ℝ)*X 0 1+(2791218047/5000000000 : ℝ)*X 0 2+(522045179/1250000000 : ℝ)*X 1 0+(776452577/2500000000 : ℝ)*X 1 1+(2791218047/5000000000 : ℝ)*X 1 2+(522045179/1250000000 : ℝ)*X 2 0+(776452577/2500000000 : ℝ)*X 2 1+(2791218047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1804098583/10000000000 : ℝ)*X 0 0+(302808291/625000000 : ℝ)*X 0 1+(1489683711/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5179609039/10000000000 : ℝ)*X 1 0+(-661489821/5000000000 : ℝ)*X 1 1+(5958734263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2589804433/5000000000 : ℝ)*X 2 0+(595873501/1000000000 : ℝ)*X 2 1+(-165372339/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1046393291/2500000000 : ℝ)*X 0 0+(1379689333/2500000000 : ℝ)*X 0 1+(396470677/1250000000 : ℝ)*X 0 2+(1046393291/2500000000 : ℝ)*X 1 0+(1379689333/2500000000 : ℝ)*X 1 1+(396470677/1250000000 : ℝ)*X 1 2+(1046393291/2500000000 : ℝ)*X 2 0+(1379689333/2500000000 : ℝ)*X 2 1+(396470677/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (488535350890794842997957/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11938907/10000000000000 : ℝ)*(base1) + (17901001/50000000000000 : ℝ)*(base16) + (526589283/100000000000000 : ℝ)*(base19) + (539650937/100000000000000 : ℝ)*(base23) + (21020827/25000000000000 : ℝ)*(upper3) + (627304928880753/100000000000000 : ℝ)*(major0) + (627304928880753/100000000000000 : ℝ)*(major1) + (627304928880753/100000000000000 : ℝ)*(major2) + (106353996840197/12500000000000 : ℝ)*(sp0) + (85083265453129/10000000000000 : ℝ)*(sp1) + (425416338635819/50000000000000 : ℝ)*(sp2) + (100943921521831/25000000000000 : ℝ)*(sp3) + (340397517/25000000000000 : ℝ)*(sp4) + (753939973/100000000000000 : ℝ)*(sp7) + (201888279708183/50000000000000 : ℝ)*(f.failure) + (425416608461287/50000000000000 : ℝ)*(f.sum) + (590398824600227/200000000000000000000000000000 : ℝ)*base66 + (335351733799773/400000000000000000000000000000 : ℝ)*base67 + (2345643887000227/400000000000000000000000000000 : ℝ)*base70 + (624520078200227/400000000000000000000000000000 : ℝ)*base72 + (622226954199773/200000000000000000000000000000 : ℝ)*base73 + (1440853291800227/400000000000000000000000000000 : ℝ)*base76 + (1541342520600227/400000000000000000000000000000 : ℝ)*base78 + (2429983999800227/400000000000000000000000000000 : ℝ)*base80 + (1374973384600227/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5224887/2500000000000000000000 : ℝ)*base90 + (5224887/2500000000000000000000 : ℝ)*base92 + (5224887/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (531951574948545886015551/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73950799/50000000000000 : ℝ)*(base19) + (105114947/25000000000000 : ℝ)*(base23) + (170605319/100000000000000 : ℝ)*(base39) + (52479721/100000000000000 : ℝ)*(upper2) + (44868217/50000000000000 : ℝ)*(upper5) + (132390170800943/20000000000000 : ℝ)*(major0) + (132390170800943/20000000000000 : ℝ)*(major1) + (165487670849849/25000000000000 : ℝ)*(major2) + (33248361/50000000000000 : ℝ)*(sp1) + (156823501/25000000000000 : ℝ)*(sp2) + (448912195558997/50000000000000 : ℝ)*(sp4) + (35912967068787/4000000000000 : ℝ)*(sp5) + (448911756984761/50000000000000 : ℝ)*(sp6) + (106519264406879/25000000000000 : ℝ)*(sp7) + (106519264406879/25000000000000 : ℝ)*(f.failure) + (448912280861657/50000000000000 : ℝ)*(f.sum) + (1128866162117149/400000000000000000000000000000 : ℝ)*base66 + (122544578522491/100000000000000000000000000000 : ℝ)*base68 + (397434362714563/80000000000000000000000000000 : ℝ)*base69 + (303000949622491/100000000000000000000000000000 : ℝ)*base72 + (1328041073317149/400000000000000000000000000000 : ℝ)*base74 + (210845201845437/80000000000000000000000000000 : ℝ)*base76 + (225796598245437/80000000000000000000000000000 : ℝ)*base78 + (215384009125437/80000000000000000000000000000 : ℝ)*base80 + (21234912165437/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (9631969/1250000000000000000000 : ℝ)*base89 + (9631969/1250000000000000000000 : ℝ)*base91 + (9631969/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1358_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (767/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6689/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1358_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1358_s1_0 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1982237351/10000000000 : ℝ)*x 0 + (5635018089/10000000000 : ℝ)*x 1 + (2526414699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1982237351/10000000000 : ℝ)^2159 ≤ (2397141456449/20000000000000 : ℝ)^1647 := by
    have hnat : (1982237351 : ℕ)^2159*20000000000000^1647 ≤ 2397141456449^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982237351 10000000000 2397141456449 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5635018089/10000000000 : ℝ)^2159 ≤ (47147272984041/100000000000000 : ℝ)^1647 := by
    have hnat : (5635018089 : ℕ)^2159*100000000000000^1647 ≤ 47147272984041^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5635018089 10000000000 47147272984041 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2526414699/5000000000 : ℝ)^2159 ≤ (40867019716343/100000000000000 : ℝ)^1647 := by
    have hnat : (2526414699 : ℕ)^2159*100000000000000^1647 ≤ 40867019716343^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526414699 5000000000 40867019716343 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1982237351/10000000000 : ℝ), (5635018089/10000000000 : ℝ), (2526414699/5000000000 : ℝ)] ![(2397141456449/20000000000000 : ℝ), (47147272984041/100000000000000 : ℝ), (40867019716343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1982237351/10000000000 : ℝ)|^2159 ≤ (2397141456449/20000000000000 : ℝ)^1647
        have hw : |(-1982237351/10000000000 : ℝ)|=(1982237351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5635018089/10000000000 : ℝ)|^2159 ≤ (47147272984041/100000000000000 : ℝ)^1647
        have hw : |(5635018089/10000000000 : ℝ)|=(5635018089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2526414699/5000000000 : ℝ)|^2159 ≤ (40867019716343/100000000000000 : ℝ)^1647
        have hw : |(2526414699/5000000000 : ℝ)|=(2526414699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s1_1 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5404051149/10000000000 : ℝ)*x 0 + (-114624257/500000000 : ℝ)*x 1 + (5052830199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404051149/10000000000 : ℝ)^2159 ≤ (44630362637483/100000000000000 : ℝ)^1647 := by
    have hnat : (5404051149 : ℕ)^2159*100000000000000^1647 ≤ 44630362637483^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404051149 10000000000 44630362637483 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114624257/500000000 : ℝ)^2159 ≤ (7251304569937/50000000000000 : ℝ)^1647 := by
    have hnat : (114624257 : ℕ)^2159*50000000000000^1647 ≤ 7251304569937^1647*500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114624257 500000000 7251304569937 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5052830199/10000000000 : ℝ)^2159 ≤ (10216757052183/25000000000000 : ℝ)^1647 := by
    have hnat : (5052830199 : ℕ)^2159*25000000000000^1647 ≤ 10216757052183^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5052830199 10000000000 10216757052183 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404051149/10000000000 : ℝ), (-114624257/500000000 : ℝ), (5052830199/10000000000 : ℝ)] ![(44630362637483/100000000000000 : ℝ), (7251304569937/50000000000000 : ℝ), (10216757052183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404051149/10000000000 : ℝ)|^2159 ≤ (44630362637483/100000000000000 : ℝ)^1647
        have hw : |(5404051149/10000000000 : ℝ)|=(5404051149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114624257/500000000 : ℝ)|^2159 ≤ (7251304569937/50000000000000 : ℝ)^1647
        have hw : |(-114624257/500000000 : ℝ)|=(114624257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5052830199/10000000000 : ℝ)|^2159 ≤ (10216757052183/25000000000000 : ℝ)^1647
        have hw : |(5052830199/10000000000 : ℝ)|=(5052830199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s1_2 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2702025631/5000000000 : ℝ)*x 0 + (1010565911/2000000000 : ℝ)*x 1 + (-458497163/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702025631/5000000000 : ℝ)^2159 ≤ (44630363860827/100000000000000 : ℝ)^1647 := by
    have hnat : (2702025631 : ℕ)^2159*100000000000000^1647 ≤ 44630363860827^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702025631 5000000000 44630363860827 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010565911/2000000000 : ℝ)^2159 ≤ (40867021380893/100000000000000 : ℝ)^1647 := by
    have hnat : (1010565911 : ℕ)^2159*100000000000000^1647 ≤ 40867021380893^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010565911 2000000000 40867021380893 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458497163/2000000000 : ℝ)^2159 ≤ (14502614737481/100000000000000 : ℝ)^1647 := by
    have hnat : (458497163 : ℕ)^2159*100000000000000^1647 ≤ 14502614737481^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458497163 2000000000 14502614737481 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2702025631/5000000000 : ℝ), (1010565911/2000000000 : ℝ), (-458497163/2000000000 : ℝ)] ![(44630363860827/100000000000000 : ℝ), (40867021380893/100000000000000 : ℝ), (14502614737481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2702025631/5000000000 : ℝ)|^2159 ≤ (44630363860827/100000000000000 : ℝ)^1647
        have hw : |(2702025631/5000000000 : ℝ)|=(2702025631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1010565911/2000000000 : ℝ)|^2159 ≤ (40867021380893/100000000000000 : ℝ)^1647
        have hw : |(1010565911/2000000000 : ℝ)|=(1010565911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-458497163/2000000000 : ℝ)|^2159 ≤ (14502614737481/100000000000000 : ℝ)^1647
        have hw : |(-458497163/2000000000 : ℝ)|=(458497163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s1_3 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4289453221/10000000000 : ℝ)*x 0 + (3716427127/10000000000 : ℝ)*x 1 + (4943204643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4289453221/10000000000 : ℝ)^2159 ≤ (16485319749553/50000000000000 : ℝ)^1647 := by
    have hnat : (4289453221 : ℕ)^2159*50000000000000^1647 ≤ 16485319749553^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289453221 10000000000 16485319749553 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3716427127/10000000000 : ℝ)^2159 ≤ (1366033443617/5000000000000 : ℝ)^1647 := by
    have hnat : (3716427127 : ℕ)^2159*5000000000000^1647 ≤ 1366033443617^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716427127 10000000000 1366033443617 5000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4943204643/10000000000 : ℝ)^2159 ≤ (7941738322777/20000000000000 : ℝ)^1647 := by
    have hnat : (4943204643 : ℕ)^2159*20000000000000^1647 ≤ 7941738322777^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4943204643 10000000000 7941738322777 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4289453221/10000000000 : ℝ), (3716427127/10000000000 : ℝ), (4943204643/10000000000 : ℝ)] ![(16485319749553/50000000000000 : ℝ), (1366033443617/5000000000000 : ℝ), (7941738322777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4289453221/10000000000 : ℝ)|^2159 ≤ (16485319749553/50000000000000 : ℝ)^1647
        have hw : |(4289453221/10000000000 : ℝ)|=(4289453221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3716427127/10000000000 : ℝ)|^2159 ≤ (1366033443617/5000000000000 : ℝ)^1647
        have hw : |(3716427127/10000000000 : ℝ)|=(3716427127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4943204643/10000000000 : ℝ)|^2159 ≤ (7941738322777/20000000000000 : ℝ)^1647
        have hw : |(4943204643/10000000000 : ℝ)|=(4943204643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s1_4 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1982745321/10000000000 : ℝ)*x 0 + (5060045071/10000000000 : ℝ)*x 1 + (2813836391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1982745321/10000000000 : ℝ)^2159 ≤ (2997433433307/25000000000000 : ℝ)^1647 := by
    have hnat : (1982745321 : ℕ)^2159*25000000000000^1647 ≤ 2997433433307^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982745321 10000000000 2997433433307 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5060045071/10000000000 : ℝ)^2159 ≤ (20471769471819/50000000000000 : ℝ)^1647 := by
    have hnat : (5060045071 : ℕ)^2159*50000000000000^1647 ≤ 20471769471819^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060045071 10000000000 20471769471819 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2813836391/5000000000 : ℝ)^2159 ≤ (47066727308003/100000000000000 : ℝ)^1647 := by
    have hnat : (2813836391 : ℕ)^2159*100000000000000^1647 ≤ 47066727308003^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813836391 5000000000 47066727308003 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1982745321/10000000000 : ℝ), (5060045071/10000000000 : ℝ), (2813836391/5000000000 : ℝ)] ![(2997433433307/25000000000000 : ℝ), (20471769471819/50000000000000 : ℝ), (47066727308003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1982745321/10000000000 : ℝ)|^2159 ≤ (2997433433307/25000000000000 : ℝ)^1647
        have hw : |(-1982745321/10000000000 : ℝ)|=(1982745321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5060045071/10000000000 : ℝ)|^2159 ≤ (20471769471819/50000000000000 : ℝ)^1647
        have hw : |(5060045071/10000000000 : ℝ)|=(5060045071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2813836391/5000000000 : ℝ)|^2159 ≤ (47066727308003/100000000000000 : ℝ)^1647
        have hw : |(2813836391/5000000000 : ℝ)|=(2813836391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s1_5 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2626390619/5000000000 : ℝ)*x 0 + (-1717642369/10000000000 : ℝ)*x 1 + (1125534569/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626390619/5000000000 : ℝ)^2159 ≤ (1719995149707/4000000000000 : ℝ)^1647 := by
    have hnat : (2626390619 : ℕ)^2159*4000000000000^1647 ≤ 1719995149707^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626390619 5000000000 1719995149707 4000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1717642369/10000000000 : ℝ)^2159 ≤ (1986678650013/20000000000000 : ℝ)^1647 := by
    have hnat : (1717642369 : ℕ)^2159*20000000000000^1647 ≤ 1986678650013^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717642369 10000000000 1986678650013 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125534569/2000000000 : ℝ)^2159 ≤ (5883340999837/12500000000000 : ℝ)^1647 := by
    have hnat : (1125534569 : ℕ)^2159*12500000000000^1647 ≤ 5883340999837^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125534569 2000000000 5883340999837 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626390619/5000000000 : ℝ), (-1717642369/10000000000 : ℝ), (1125534569/2000000000 : ℝ)] ![(1719995149707/4000000000000 : ℝ), (1986678650013/20000000000000 : ℝ), (5883340999837/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626390619/5000000000 : ℝ)|^2159 ≤ (1719995149707/4000000000000 : ℝ)^1647
        have hw : |(2626390619/5000000000 : ℝ)|=(2626390619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1717642369/10000000000 : ℝ)|^2159 ≤ (1986678650013/20000000000000 : ℝ)^1647
        have hw : |(-1717642369/10000000000 : ℝ)|=(1717642369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125534569/2000000000 : ℝ)|^2159 ≤ (5883340999837/12500000000000 : ℝ)^1647
        have hw : |(1125534569/2000000000 : ℝ)|=(1125534569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s1_6 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5252781131/10000000000 : ℝ)*x 0 + (175864779/312500000 : ℝ)*x 1 + (-2147053/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252781131/10000000000 : ℝ)^2159 ≤ (42999877594467/100000000000000 : ℝ)^1647 := by
    have hnat : (5252781131 : ℕ)^2159*100000000000000^1647 ≤ 42999877594467^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252781131 10000000000 42999877594467 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175864779/312500000 : ℝ)^2159 ≤ (2941670556791/6250000000000 : ℝ)^1647 := by
    have hnat : (175864779 : ℕ)^2159*6250000000000^1647 ≤ 2941670556791^1647*312500000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175864779 312500000 2941670556791 6250000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147053/12500000 : ℝ)^2159 ≤ (4966696742537/50000000000000 : ℝ)^1647 := by
    have hnat : (2147053 : ℕ)^2159*50000000000000^1647 ≤ 4966696742537^1647*12500000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147053 12500000 4966696742537 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252781131/10000000000 : ℝ), (175864779/312500000 : ℝ), (-2147053/12500000 : ℝ)] ![(42999877594467/100000000000000 : ℝ), (2941670556791/6250000000000 : ℝ), (4966696742537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252781131/10000000000 : ℝ)|^2159 ≤ (42999877594467/100000000000000 : ℝ)^1647
        have hw : |(5252781131/10000000000 : ℝ)|=(5252781131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175864779/312500000 : ℝ)|^2159 ≤ (2941670556791/6250000000000 : ℝ)^1647
        have hw : |(175864779/312500000 : ℝ)|=(175864779/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2147053/12500000 : ℝ)|^2159 ≤ (4966696742537/50000000000000 : ℝ)^1647
        have hw : |(-2147053/12500000 : ℝ)|=(2147053/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s1_7 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1072631051/2500000000 : ℝ)*x 0 + (492800121/1000000000 : ℝ)*x 1 + (3731902511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072631051/2500000000 : ℝ)^2159 ≤ (32981431051119/100000000000000 : ℝ)^1647 := by
    have hnat : (1072631051 : ℕ)^2159*100000000000000^1647 ≤ 32981431051119^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072631051 2500000000 32981431051119 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492800121/1000000000 : ℝ)^2159 ≤ (3954867322957/10000000000000 : ℝ)^1647 := by
    have hnat : (492800121 : ℕ)^2159*10000000000000^1647 ≤ 3954867322957^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492800121 1000000000 3954867322957 10000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3731902511/10000000000 : ℝ)^2159 ≤ (13734947851471/50000000000000 : ℝ)^1647 := by
    have hnat : (3731902511 : ℕ)^2159*50000000000000^1647 ≤ 13734947851471^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731902511 10000000000 13734947851471 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072631051/2500000000 : ℝ), (492800121/1000000000 : ℝ), (3731902511/10000000000 : ℝ)] ![(32981431051119/100000000000000 : ℝ), (3954867322957/10000000000000 : ℝ), (13734947851471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072631051/2500000000 : ℝ)|^2159 ≤ (32981431051119/100000000000000 : ℝ)^1647
        have hw : |(1072631051/2500000000 : ℝ)|=(1072631051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(492800121/1000000000 : ℝ)|^2159 ≤ (3954867322957/10000000000000 : ℝ)^1647
        have hw : |(492800121/1000000000 : ℝ)|=(492800121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3731902511/10000000000 : ℝ)|^2159 ≤ (13734947851471/50000000000000 : ℝ)^1647
        have hw : |(3731902511/10000000000 : ℝ)|=(3731902511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1358_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (767/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7037/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9671/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (767/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (767/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (767/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (767/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (767/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (767/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (767/50000 : ℝ) ^ (4317/1024 : ℝ) ≤ (1123920790549/50000000000000000000 : ℝ) := by
    have hpowers : (767/50000 : ℝ)^4317 ≤ (1123920790549/50000000000000000000 : ℝ)^1024 := by
      have hnat : (767 : ℕ)^4317*50000000000000000000^1024 ≤ 1123920790549^1024*50000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        767 50000 1123920790549 50000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (767/50000 : ℝ)) (X := (1123920790549/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6689/25000 : ℝ) ^ (4317/1024 : ℝ) ≤ (77115309595918653/20000000000000000000 : ℝ) := by
    have hpowers : (6689/25000 : ℝ)^4317 ≤ (77115309595918653/20000000000000000000 : ℝ)^1024 := by
      have hnat : (6689 : ℕ)^4317*20000000000000000000^1024 ≤ 77115309595918653^1024*25000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6689 25000 77115309595918653 20000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6689/25000 : ℝ)) (X := (77115309595918653/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000001123920790549/25000000000000000000 : ℝ) ≤ (2000000021327679/2000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (25000001123920790549/25000000000000000000 : ℝ)^1024 ≤ (2000000021327679/2000000000000000 : ℝ)^4317 := by
      have hnat : (25000001123920790549 : ℕ)^1024*2000000000000000^4317 ≤ 2000000021327679^4317*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000001123920790549 25000000000000000000 2000000021327679 2000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000021327679/2000000000000000 : ℝ)) (X := (25000001123920790549/25000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100385578795821174363/100000000000000000000 : ℝ) ≤ (1251141572157527/1250000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (100385578795821174363/100000000000000000000 : ℝ)^1024 ≤ (1251141572157527/1250000000000000 : ℝ)^4317 := by
      have hnat : (100385578795821174363 : ℕ)^1024*1250000000000000^4317 ≤ 1251141572157527^4317*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100385578795821174363 100000000000000000000 1251141572157527 1250000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251141572157527/1250000000000000 : ℝ)) (X := (100385578795821174363/100000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10077115309595918653/10000000000000000000 : ℝ) ≤ (10018265047882037/10000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (10077115309595918653/10000000000000000000 : ℝ)^1024 ≤ (10018265047882037/10000000000000000 : ℝ)^4317 := by
      have hnat : (10077115309595918653 : ℕ)^1024*10000000000000000^4317 ≤ 10018265047882037^4317*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10077115309595918653 10000000000000000000 10018265047882037 10000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018265047882037/10000000000000000 : ℝ)) (X := (10077115309595918653/10000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1123920790549/50000000000000000000 : ℝ) ≤ ((126095992134882925931/126110000000000000000 : ℝ)+2*(9132470621821/2522200000000000 : ℝ)*(767/50000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (126095992134882925931/126110000000000000000 : ℝ)+2*(9132470621821/2522200000000000 : ℝ)*(767/50000 : ℝ)=(2000000021327679/2000000000000000 : ℝ) by norm_num, show 1+2*(1123920790549/50000000000000000000 : ℝ)=(25000001123920790549/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(77115309595918653/20000000000000000000 : ℝ)+(1123920790549/50000000000000000000 : ℝ) ≤ ((126095992134882925931/126110000000000000000 : ℝ)+(9132470621821/2522200000000000 : ℝ)*((6689/25000 : ℝ)+(767/50000 : ℝ)))^(4317/1024 : ℝ) := by
    rw [show (126095992134882925931/126110000000000000000 : ℝ)+(9132470621821/2522200000000000 : ℝ)*((6689/25000 : ℝ)+(767/50000 : ℝ))=(1251141572157527/1250000000000000 : ℝ) by norm_num, show 1+(77115309595918653/20000000000000000000 : ℝ)+(1123920790549/50000000000000000000 : ℝ)=(100385578795821174363/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(77115309595918653/20000000000000000000 : ℝ) ≤ ((126095992134882925931/126110000000000000000 : ℝ)+2*(9132470621821/2522200000000000 : ℝ)*(6689/25000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (126095992134882925931/126110000000000000000 : ℝ)+2*(9132470621821/2522200000000000 : ℝ)*(6689/25000 : ℝ)=(10018265047882037/10000000000000000 : ℝ) by norm_num, show 1+2*(77115309595918653/20000000000000000000 : ℝ)=(10077115309595918653/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (126095992134882925931/126110000000000000000 : ℝ)*(X 1 0+X 2 0)+(9132470621821/2522200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (767/50000 : ℝ)) (hi := (6689/25000 : ℝ)) (c := (126095992134882925931/126110000000000000000 : ℝ)) (alpha := (9132470621821/2522200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (126095992134882925931/126110000000000000000 : ℝ)*(X 0 1+X 2 1)+(9132470621821/2522200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (767/50000 : ℝ)) (hi := (6689/25000 : ℝ)) (c := (126095992134882925931/126110000000000000000 : ℝ)) (alpha := (9132470621821/2522200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (126095992134882925931/126110000000000000000 : ℝ)*(X 0 2+X 1 2)+(9132470621821/2522200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (767/50000 : ℝ)) (hi := (6689/25000 : ℝ)) (c := (126095992134882925931/126110000000000000000 : ℝ)) (alpha := (9132470621821/2522200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1982237351/10000000000 : ℝ)*X 0 0+(5635018089/10000000000 : ℝ)*X 0 1+(2526414699/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5404051149/10000000000 : ℝ)*X 1 0+(-114624257/500000000 : ℝ)*X 1 1+(5052830199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2702025631/5000000000 : ℝ)*X 2 0+(1010565911/2000000000 : ℝ)*X 2 1+(-458497163/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4289453221/10000000000 : ℝ)*X 0 0+(3716427127/10000000000 : ℝ)*X 0 1+(4943204643/10000000000 : ℝ)*X 0 2+(4289453221/10000000000 : ℝ)*X 1 0+(3716427127/10000000000 : ℝ)*X 1 1+(4943204643/10000000000 : ℝ)*X 1 2+(4289453221/10000000000 : ℝ)*X 2 0+(3716427127/10000000000 : ℝ)*X 2 1+(4943204643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1982745321/10000000000 : ℝ)*X 0 0+(5060045071/10000000000 : ℝ)*X 0 1+(2813836391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2626390619/5000000000 : ℝ)*X 1 0+(-1717642369/10000000000 : ℝ)*X 1 1+(1125534569/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252781131/10000000000 : ℝ)*X 2 0+(175864779/312500000 : ℝ)*X 2 1+(-2147053/12500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1072631051/2500000000 : ℝ)*X 0 0+(492800121/1000000000 : ℝ)*X 0 1+(3731902511/10000000000 : ℝ)*X 0 2+(1072631051/2500000000 : ℝ)*X 1 0+(492800121/1000000000 : ℝ)*X 1 1+(3731902511/10000000000 : ℝ)*X 1 2+(1072631051/2500000000 : ℝ)*X 2 0+(492800121/1000000000 : ℝ)*X 2 1+(3731902511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6279032962555640725152691977/788187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8025573/100000000000000 : ℝ)*(base1) + (4606741/50000000000000 : ℝ)*(base16) + (1249325431/100000000000000 : ℝ)*(base19) + (258891181/20000000000000 : ℝ)*(base23) + (248664303/100000000000000 : ℝ)*(upper3) + (158301700423611/12500000000000 : ℝ)*(major0) + (158301700423611/12500000000000 : ℝ)*(major1) + (158301700423611/12500000000000 : ℝ)*(major2) + (429416865155123/25000000000000 : ℝ)*(sp0) + (171767486204229/10000000000000 : ℝ)*(sp1) + (1717674826125299/100000000000000 : ℝ)*(sp2) + (203786651640953/25000000000000 : ℝ)*(sp3) + (1733597257/20000000000000 : ℝ)*(sp4) + (4206059837/100000000000000 : ℝ)*(sp7) + (407575410324611/50000000000000 : ℝ)*(f.failure) + (429419030145301/25000000000000 : ℝ)*(f.sum) + (250058517857741/63055000000000000000000000000 : ℝ)*base66 + (3350693080207231841/1576375000000000000000000000000000 : ℝ)*base67 + (5897348028743231841/1576375000000000000000000000000000 : ℝ)*base69 + (398655732195643159/1576375000000000000000000000000000 : ℝ)*base72 + (316503530737823/31527500000000000000000000000 : ℝ)*base74 + (3399586532535231841/1576375000000000000000000000000000 : ℝ)*base75 + (1382669885278356841/1576375000000000000000000000000000 : ℝ)*base77 + (474350783210518159/1576375000000000000000000000000000 : ℝ)*base80 + (131608484309533/31527500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1332579/2500000000000000000000 : ℝ)*base90 + (1332579/2500000000000000000000 : ℝ)*base92 + (1332579/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9004004677182931650775877523/3152750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31470167/100000000000000 : ℝ)*(base1) + (147764567/25000000000000 : ℝ)*(base19) + (138377587/25000000000000 : ℝ)*(base23) + (17265951/25000000000000 : ℝ)*(upper3) + (7425943/12500000000000 : ℝ)*(upper5) + (1298884695952389/100000000000000 : ℝ)*(major0) + (1298884695952389/100000000000000 : ℝ)*(major1) + (1298884695952389/100000000000000 : ℝ)*(major2) + (3179211741/100000000000000 : ℝ)*(sp1) + (1560756953/50000000000000 : ℝ)*(sp2) + (440429470250857/25000000000000 : ℝ)*(sp4) + (440428519815813/25000000000000 : ℝ)*(sp5) + (880857087254503/50000000000000 : ℝ)*(sp6) + (836051415703979/100000000000000 : ℝ)*(sp7) + (418025723587073/50000000000000 : ℝ)*(f.failure) + (88085892476663/5000000000000 : ℝ)*(f.sum) + (216560945946289/126110000000000000000000000000 : ℝ)*base65 + (28146322944449949159/12611000000000000000000000000000000 : ℝ)*base67 + (53068559638392949159/12611000000000000000000000000000000 : ℝ)*base69 + (72089401337296949159/12611000000000000000000000000000000 : ℝ)*base71 + (661576081063549/126110000000000000000000000000 : ℝ)*base73 + (50627427098140050841/12611000000000000000000000000000000 : ℝ)*base76 + (145959484300993949159/12611000000000000000000000000000000 : ℝ)*base77 + (16125795060339949159/12611000000000000000000000000000000 : ℝ)*base79 + (292422901843679/126110000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (11024097/2500000000000000000000 : ℝ)*base90 + (11024097/2500000000000000000000 : ℝ)*base92 + (11024097/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1358_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (767/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7037/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9671/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1358_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1358_s2_0 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2021017567/10000000000 : ℝ)*x 0 + (5475440781/10000000000 : ℝ)*x 1 + (1296885767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021017567/10000000000 : ℝ)^2159 ≤ (384188094141/3125000000000 : ℝ)^1647 := by
    have hnat : (2021017567 : ℕ)^2159*3125000000000^1647 ≤ 384188094141^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021017567 10000000000 384188094141 3125000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475440781/10000000000 : ℝ)^2159 ≤ (22702406250817/50000000000000 : ℝ)^1647 := by
    have hnat : (5475440781 : ℕ)^2159*50000000000000^1647 ≤ 22702406250817^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475440781 10000000000 22702406250817 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296885767/2500000000 : ℝ)^2159 ≤ (42301168473463/100000000000000 : ℝ)^1647 := by
    have hnat : (1296885767 : ℕ)^2159*100000000000000^1647 ≤ 42301168473463^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296885767 2500000000 42301168473463 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2021017567/10000000000 : ℝ), (5475440781/10000000000 : ℝ), (1296885767/2500000000 : ℝ)] ![(384188094141/3125000000000 : ℝ), (22702406250817/50000000000000 : ℝ), (42301168473463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2021017567/10000000000 : ℝ)|^2159 ≤ (384188094141/3125000000000 : ℝ)^1647
        have hw : |(-2021017567/10000000000 : ℝ)|=(2021017567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475440781/10000000000 : ℝ)|^2159 ≤ (22702406250817/50000000000000 : ℝ)^1647
        have hw : |(5475440781/10000000000 : ℝ)|=(5475440781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296885767/2500000000 : ℝ)|^2159 ≤ (42301168473463/100000000000000 : ℝ)^1647
        have hw : |(1296885767/2500000000 : ℝ)|=(1296885767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s2_1 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5364835001/10000000000 : ℝ)*x 0 + (-216964791/1000000000 : ℝ)*x 1 + (5187543427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364835001/10000000000 : ℝ)^2159 ≤ (44206286359463/100000000000000 : ℝ)^1647 := by
    have hnat : (5364835001 : ℕ)^2159*100000000000000^1647 ≤ 44206286359463^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364835001 10000000000 44206286359463 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216964791/1000000000 : ℝ)^2159 ≤ (1686567665163/12500000000000 : ℝ)^1647 := by
    have hnat : (216964791 : ℕ)^2159*12500000000000^1647 ≤ 1686567665163^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216964791 1000000000 1686567665163 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5187543427/10000000000 : ℝ)^2159 ≤ (1692046892437/4000000000000 : ℝ)^1647 := by
    have hnat : (5187543427 : ℕ)^2159*4000000000000^1647 ≤ 1692046892437^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187543427 10000000000 1692046892437 4000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364835001/10000000000 : ℝ), (-216964791/1000000000 : ℝ), (5187543427/10000000000 : ℝ)] ![(44206286359463/100000000000000 : ℝ), (1686567665163/12500000000000 : ℝ), (1692046892437/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364835001/10000000000 : ℝ)|^2159 ≤ (44206286359463/100000000000000 : ℝ)^1647
        have hw : |(5364835001/10000000000 : ℝ)|=(5364835001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216964791/1000000000 : ℝ)|^2159 ≤ (1686567665163/12500000000000 : ℝ)^1647
        have hw : |(-216964791/1000000000 : ℝ)|=(216964791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5187543427/10000000000 : ℝ)|^2159 ≤ (1692046892437/4000000000000 : ℝ)^1647
        have hw : |(5187543427/10000000000 : ℝ)|=(5187543427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s2_2 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5364835059/10000000000 : ℝ)*x 0 + (1296885839/2500000000 : ℝ)*x 1 + (-86785917/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364835059/10000000000 : ℝ)^2159 ≤ (44206286985953/100000000000000 : ℝ)^1647 := by
    have hnat : (5364835059 : ℕ)^2159*100000000000000^1647 ≤ 44206286985953^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364835059 10000000000 44206286985953 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296885839/2500000000 : ℝ)^2159 ≤ (2643823221999/6250000000000 : ℝ)^1647 := by
    have hnat : (1296885839 : ℕ)^2159*6250000000000^1647 ≤ 2643823221999^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296885839 2500000000 2643823221999 6250000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86785917/400000000 : ℝ)^2159 ≤ (26352620007/195312500000 : ℝ)^1647 := by
    have hnat : (86785917 : ℕ)^2159*195312500000^1647 ≤ 26352620007^1647*400000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86785917 400000000 26352620007 195312500000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364835059/10000000000 : ℝ), (1296885839/2500000000 : ℝ), (-86785917/400000000 : ℝ)] ![(44206286985953/100000000000000 : ℝ), (2643823221999/6250000000000 : ℝ), (26352620007/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364835059/10000000000 : ℝ)|^2159 ≤ (44206286985953/100000000000000 : ℝ)^1647
        have hw : |(5364835059/10000000000 : ℝ)|=(5364835059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296885839/2500000000 : ℝ)|^2159 ≤ (2643823221999/6250000000000 : ℝ)^1647
        have hw : |(1296885839/2500000000 : ℝ)|=(1296885839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86785917/400000000 : ℝ)|^2159 ≤ (26352620007/195312500000 : ℝ)^1647
        have hw : |(-86785917/400000000 : ℝ)|=(86785917/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s2_3 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4316619781/10000000000 : ℝ)*x 0 + (40231583/100000000 : ℝ)*x 1 + (4629812251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316619781/10000000000 : ℝ)^2159 ≤ (33244636509153/100000000000000 : ℝ)^1647 := by
    have hnat : (4316619781 : ℕ)^2159*100000000000000^1647 ≤ 33244636509153^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316619781 10000000000 33244636509153 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40231583/100000000 : ℝ)^2159 ≤ (3789218151279/12500000000000 : ℝ)^1647 := by
    have hnat : (40231583 : ℕ)^2159*12500000000000^1647 ≤ 3789218151279^1647*100000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40231583 100000000 3789218151279 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4629812251/10000000000 : ℝ)^2159 ≤ (36441618267347/100000000000000 : ℝ)^1647 := by
    have hnat : (4629812251 : ℕ)^2159*100000000000000^1647 ≤ 36441618267347^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4629812251 10000000000 36441618267347 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316619781/10000000000 : ℝ), (40231583/100000000 : ℝ), (4629812251/10000000000 : ℝ)] ![(33244636509153/100000000000000 : ℝ), (3789218151279/12500000000000 : ℝ), (36441618267347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316619781/10000000000 : ℝ)|^2159 ≤ (33244636509153/100000000000000 : ℝ)^1647
        have hw : |(4316619781/10000000000 : ℝ)|=(4316619781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40231583/100000000 : ℝ)|^2159 ≤ (3789218151279/12500000000000 : ℝ)^1647
        have hw : |(40231583/100000000 : ℝ)|=(40231583/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4629812251/10000000000 : ℝ)|^2159 ≤ (36441618267347/100000000000000 : ℝ)^1647
        have hw : |(4629812251/10000000000 : ℝ)|=(4629812251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s2_4 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-126317439/625000000 : ℝ)*x 0 + (5189317473/10000000000 : ℝ)*x 1 + (2736825327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126317439/625000000 : ℝ)^2159 ≤ (6147254540199/50000000000000 : ℝ)^1647 := by
    have hnat : (126317439 : ℕ)^2159*50000000000000^1647 ≤ 6147254540199^1647*625000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126317439 625000000 6147254540199 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5189317473/10000000000 : ℝ)^2159 ≤ (8464027329553/20000000000000 : ℝ)^1647 := by
    have hnat : (5189317473 : ℕ)^2159*20000000000000^1647 ≤ 8464027329553^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189317473 10000000000 8464027329553 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736825327/5000000000 : ℝ)^2159 ≤ (11346338564749/25000000000000 : ℝ)^1647 := by
    have hnat : (2736825327 : ℕ)^2159*25000000000000^1647 ≤ 11346338564749^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736825327 5000000000 11346338564749 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126317439/625000000 : ℝ), (5189317473/10000000000 : ℝ), (2736825327/5000000000 : ℝ)] ![(6147254540199/50000000000000 : ℝ), (8464027329553/20000000000000 : ℝ), (11346338564749/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126317439/625000000 : ℝ)|^2159 ≤ (6147254540199/50000000000000 : ℝ)^1647
        have hw : |(-126317439/625000000 : ℝ)|=(126317439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5189317473/10000000000 : ℝ)|^2159 ≤ (8464027329553/20000000000000 : ℝ)^1647
        have hw : |(5189317473/10000000000 : ℝ)|=(5189317473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736825327/5000000000 : ℝ)|^2159 ≤ (11346338564749/25000000000000 : ℝ)^1647
        have hw : |(2736825327/5000000000 : ℝ)|=(2736825327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s2_5 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2645251047/5000000000 : ℝ)*x 0 + (-1883540393/10000000000 : ℝ)*x 1 + (5473650613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645251047/5000000000 : ℝ)^2159 ≤ (10851277325383/25000000000000 : ℝ)^1647 := by
    have hnat : (2645251047 : ℕ)^2159*25000000000000^1647 ≤ 10851277325383^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645251047 5000000000 10851277325383 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1883540393/10000000000 : ℝ)^2159 ≤ (1401192107641/12500000000000 : ℝ)^1647 := by
    have hnat : (1883540393 : ℕ)^2159*12500000000000^1647 ≤ 1401192107641^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883540393 10000000000 1401192107641 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473650613/10000000000 : ℝ)^2159 ≤ (45385353813359/100000000000000 : ℝ)^1647 := by
    have hnat : (5473650613 : ℕ)^2159*100000000000000^1647 ≤ 45385353813359^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473650613 10000000000 45385353813359 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645251047/5000000000 : ℝ), (-1883540393/10000000000 : ℝ), (5473650613/10000000000 : ℝ)] ![(10851277325383/25000000000000 : ℝ), (1401192107641/12500000000000 : ℝ), (45385353813359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645251047/5000000000 : ℝ)|^2159 ≤ (10851277325383/25000000000000 : ℝ)^1647
        have hw : |(2645251047/5000000000 : ℝ)|=(2645251047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1883540393/10000000000 : ℝ)|^2159 ≤ (1401192107641/12500000000000 : ℝ)^1647
        have hw : |(-1883540393/10000000000 : ℝ)|=(1883540393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473650613/10000000000 : ℝ)|^2159 ≤ (45385353813359/100000000000000 : ℝ)^1647
        have hw : |(5473650613/10000000000 : ℝ)|=(5473650613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s2_6 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5290502067/10000000000 : ℝ)*x 0 + (5473650659/10000000000 : ℝ)*x 1 + (-117721273/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290502067/10000000000 : ℝ)^2159 ≤ (2712819313197/6250000000000 : ℝ)^1647 := by
    have hnat : (5290502067 : ℕ)^2159*6250000000000^1647 ≤ 2712819313197^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290502067 10000000000 2712819313197 6250000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473650659/10000000000 : ℝ)^2159 ≤ (22692677156671/50000000000000 : ℝ)^1647 := by
    have hnat : (5473650659 : ℕ)^2159*50000000000000^1647 ≤ 22692677156671^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473650659 10000000000 22692677156671 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117721273/625000000 : ℝ)^2159 ≤ (11209536666093/100000000000000 : ℝ)^1647 := by
    have hnat : (117721273 : ℕ)^2159*100000000000000^1647 ≤ 11209536666093^1647*625000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117721273 625000000 11209536666093 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290502067/10000000000 : ℝ), (5473650659/10000000000 : ℝ), (-117721273/625000000 : ℝ)] ![(2712819313197/6250000000000 : ℝ), (22692677156671/50000000000000 : ℝ), (11209536666093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290502067/10000000000 : ℝ)|^2159 ≤ (2712819313197/6250000000000 : ℝ)^1647
        have hw : |(5290502067/10000000000 : ℝ)|=(5290502067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473650659/10000000000 : ℝ)|^2159 ≤ (22692677156671/50000000000000 : ℝ)^1647
        have hw : |(5473650659/10000000000 : ℝ)|=(5473650659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117721273/625000000 : ℝ)|^2159 ≤ (11209536666093/100000000000000 : ℝ)^1647
        have hw : |(-117721273/625000000 : ℝ)|=(117721273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s2_7 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4316749581/10000000000 : ℝ)*x 0 + (2313036911/5000000000 : ℝ)*x 1 + (62920779/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316749581/10000000000 : ℝ)^2159 ≤ (1662297346917/5000000000000 : ℝ)^1647 := by
    have hnat : (4316749581 : ℕ)^2159*5000000000000^1647 ≤ 1662297346917^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316749581 10000000000 1662297346917 5000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2313036911/5000000000 : ℝ)^2159 ≤ (18201525097471/50000000000000 : ℝ)^1647 := by
    have hnat : (2313036911 : ℕ)^2159*50000000000000^1647 ≤ 18201525097471^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313036911 5000000000 18201525097471 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62920779/156250000 : ℝ)^2159 ≤ (30351002850299/100000000000000 : ℝ)^1647 := by
    have hnat : (62920779 : ℕ)^2159*100000000000000^1647 ≤ 30351002850299^1647*156250000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62920779 156250000 30351002850299 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316749581/10000000000 : ℝ), (2313036911/5000000000 : ℝ), (62920779/156250000 : ℝ)] ![(1662297346917/5000000000000 : ℝ), (18201525097471/50000000000000 : ℝ), (30351002850299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316749581/10000000000 : ℝ)|^2159 ≤ (1662297346917/5000000000000 : ℝ)^1647
        have hw : |(4316749581/10000000000 : ℝ)|=(4316749581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2313036911/5000000000 : ℝ)|^2159 ≤ (18201525097471/50000000000000 : ℝ)^1647
        have hw : |(2313036911/5000000000 : ℝ)|=(2313036911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62920779/156250000 : ℝ)|^2159 ≤ (30351002850299/100000000000000 : ℝ)^1647
        have hw : |(62920779/156250000 : ℝ)|=(62920779/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1358_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9671/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1991/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8021/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9671/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9671/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9671/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9671/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9671/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9671/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7037/100000 : ℝ) ^ (4317/1024 : ℝ) ≤ (691453579985181/50000000000000000000 : ℝ) := by
    have hpowers : (7037/100000 : ℝ)^4317 ≤ (691453579985181/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7037 : ℕ)^4317*50000000000000000000^1024 ≤ 691453579985181^1024*100000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7037 100000 691453579985181 50000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7037/100000 : ℝ)) (X := (691453579985181/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9671/50000 : ℝ) ^ (4317/1024 : ℝ) ≤ (49089434007232677/50000000000000000000 : ℝ) := by
    have hpowers : (9671/50000 : ℝ)^4317 ≤ (49089434007232677/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9671 : ℕ)^4317*50000000000000000000^1024 ≤ 49089434007232677^1024*50000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9671 50000 49089434007232677 50000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9671/50000 : ℝ)) (X := (49089434007232677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000691453579985181/25000000000000000000 : ℝ) ≤ (5000032802455269/5000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (25000691453579985181/25000000000000000000 : ℝ)^1024 ≤ (5000032802455269/5000000000000000 : ℝ)^4317 := by
      have hnat : (25000691453579985181 : ℕ)^1024*5000000000000000^4317 ≤ 5000032802455269^4317*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000691453579985181 25000000000000000000 5000032802455269 5000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000032802455269/5000000000000000 : ℝ)) (X := (25000691453579985181/25000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25024890443793608929/25000000000000000000 : ℝ) ≤ (5001180363292697/5000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (25024890443793608929/25000000000000000000 : ℝ)^1024 ≤ (5001180363292697/5000000000000000 : ℝ)^4317 := by
      have hnat : (25024890443793608929 : ℕ)^1024*5000000000000000^4317 ≤ 5001180363292697^4317*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024890443793608929 25000000000000000000 5001180363292697 5000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001180363292697/5000000000000000 : ℝ)) (X := (25024890443793608929/25000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25049089434007232677/25000000000000000000 : ℝ) ≤ (40018623393041/40000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (25049089434007232677/25000000000000000000 : ℝ)^1024 ≤ (40018623393041/40000000000000 : ℝ)^4317 := by
      have hnat : (25049089434007232677 : ℕ)^1024*40000000000000^4317 ≤ 40018623393041^4317*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25049089434007232677 25000000000000000000 40018623393041 40000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40018623393041/40000000000000 : ℝ)) (X := (25049089434007232677/25000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(691453579985181/50000000000000000000 : ℝ) ≤ ((61509252862986123373/61525000000000000000 : ℝ)+2*(286890209357/153812500000000 : ℝ)*(7037/100000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (61509252862986123373/61525000000000000000 : ℝ)+2*(286890209357/153812500000000 : ℝ)*(7037/100000 : ℝ)=(5000032802455269/5000000000000000 : ℝ) by norm_num, show 1+2*(691453579985181/50000000000000000000 : ℝ)=(25000691453579985181/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(49089434007232677/50000000000000000000 : ℝ)+(691453579985181/50000000000000000000 : ℝ) ≤ ((61509252862986123373/61525000000000000000 : ℝ)+(286890209357/153812500000000 : ℝ)*((9671/50000 : ℝ)+(7037/100000 : ℝ)))^(4317/1024 : ℝ) := by
    rw [show (61509252862986123373/61525000000000000000 : ℝ)+(286890209357/153812500000000 : ℝ)*((9671/50000 : ℝ)+(7037/100000 : ℝ))=(5001180363292697/5000000000000000 : ℝ) by norm_num, show 1+(49089434007232677/50000000000000000000 : ℝ)+(691453579985181/50000000000000000000 : ℝ)=(25024890443793608929/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(49089434007232677/50000000000000000000 : ℝ) ≤ ((61509252862986123373/61525000000000000000 : ℝ)+2*(286890209357/153812500000000 : ℝ)*(9671/50000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (61509252862986123373/61525000000000000000 : ℝ)+2*(286890209357/153812500000000 : ℝ)*(9671/50000 : ℝ)=(40018623393041/40000000000000 : ℝ) by norm_num, show 1+2*(49089434007232677/50000000000000000000 : ℝ)=(25049089434007232677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (61509252862986123373/61525000000000000000 : ℝ)*(X 1 0+X 2 0)+(286890209357/153812500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (7037/100000 : ℝ)) (hi := (9671/50000 : ℝ)) (c := (61509252862986123373/61525000000000000000 : ℝ)) (alpha := (286890209357/153812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (61509252862986123373/61525000000000000000 : ℝ)*(X 0 1+X 2 1)+(286890209357/153812500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (7037/100000 : ℝ)) (hi := (9671/50000 : ℝ)) (c := (61509252862986123373/61525000000000000000 : ℝ)) (alpha := (286890209357/153812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (61509252862986123373/61525000000000000000 : ℝ)*(X 0 2+X 1 2)+(286890209357/153812500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (7037/100000 : ℝ)) (hi := (9671/50000 : ℝ)) (c := (61509252862986123373/61525000000000000000 : ℝ)) (alpha := (286890209357/153812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2021017567/10000000000 : ℝ)*X 0 0+(5475440781/10000000000 : ℝ)*X 0 1+(1296885767/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5364835001/10000000000 : ℝ)*X 1 0+(-216964791/1000000000 : ℝ)*X 1 1+(5187543427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5364835059/10000000000 : ℝ)*X 2 0+(1296885839/2500000000 : ℝ)*X 2 1+(-86785917/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4316619781/10000000000 : ℝ)*X 0 0+(40231583/100000000 : ℝ)*X 0 1+(4629812251/10000000000 : ℝ)*X 0 2+(4316619781/10000000000 : ℝ)*X 1 0+(40231583/100000000 : ℝ)*X 1 1+(4629812251/10000000000 : ℝ)*X 1 2+(4316619781/10000000000 : ℝ)*X 2 0+(40231583/100000000 : ℝ)*X 2 1+(4629812251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-126317439/625000000 : ℝ)*X 0 0+(5189317473/10000000000 : ℝ)*X 0 1+(2736825327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645251047/5000000000 : ℝ)*X 1 0+(-1883540393/10000000000 : ℝ)*X 1 1+(5473650613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290502067/10000000000 : ℝ)*X 2 0+(5473650659/10000000000 : ℝ)*X 2 1+(-117721273/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316749581/10000000000 : ℝ)*X 0 0+(2313036911/5000000000 : ℝ)*X 0 1+(62920779/156250000 : ℝ)*X 0 2+(4316749581/10000000000 : ℝ)*X 1 0+(2313036911/5000000000 : ℝ)*X 1 1+(62920779/156250000 : ℝ)*X 1 2+(4316749581/10000000000 : ℝ)*X 2 0+(2313036911/5000000000 : ℝ)*X 2 1+(62920779/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13778154732940975737784889679/3076250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (666282939/100000000000000 : ℝ)*(base19) + (702041913/100000000000000 : ℝ)*(base23) + (481041/50000000000000 : ℝ)*(lower2) + (45502261/50000000000000 : ℝ)*(upper3) + (85007679/100000000000000 : ℝ)*(upper5) + (2560938192039241/100000000000000 : ℝ)*(major0) + (2560938192039241/100000000000000 : ℝ)*(major1) + (2560938192039241/100000000000000 : ℝ)*(major2) + (1736734023406693/50000000000000 : ℝ)*(sp0) + (3473479765353949/100000000000000 : ℝ)*(sp1) + (1736739864797487/50000000000000 : ℝ)*(sp2) + (824195449984257/50000000000000 : ℝ)*(sp3) + (6192411751/50000000000000 : ℝ)*(sp4) + (4903177073/100000000000000 : ℝ)*(sp7) + (1648395803145587/100000000000000 : ℝ)*(f.failure) + (434185053954611/12500000000000 : ℝ)*(f.sum) + (19135917049629/61525000000000000000000000000 : ℝ)*base66 + (3444826559696920107/6152500000000000000000000000000000 : ℝ)*base68 + (37796946943046920107/6152500000000000000000000000000000 : ℝ)*base70 + (4402646103908079893/6152500000000000000000000000000000 : ℝ)*base71 + (8869941260153/1922656250000000000000000000 : ℝ)*base73 + (93370416306764420107/6152500000000000000000000000000000 : ℝ)*base76 + (17971686236934420107/6152500000000000000000000000000000 : ℝ)*base78 + (32276909403923079893/6152500000000000000000000000000000 : ℝ)*base79 + (16084144701563/7690625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (39085357/5000000000000000000000 : ℝ)*base89 + (39085357/5000000000000000000000 : ℝ)*base91 + (39085357/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (498843837891322807126617/61525000000000000000000000000 : ℝ) := by norm_num
    linear_combination (415768519/25000000000000 : ℝ)*(base19) + (365652159/20000000000000 : ℝ)*(base23) + (11999581/6250000000000 : ℝ)*(upper3) + (14976623/20000000000000 : ℝ)*(lower4) + (34419951/25000000000000 : ℝ)*(upper5) + (40515991776379/1562500000000 : ℝ)*(major0) + (40515991776379/1562500000000 : ℝ)*(major1) + (40515991776379/1562500000000 : ℝ)*(major2) + (3819215097/20000000000000 : ℝ)*(sp1) + (551409007/2500000000000 : ℝ)*(sp2) + (1758499290928271/50000000000000 : ℝ)*(sp4) + (175848891135349/5000000000000 : ℝ)*(sp5) + (1758487348617733/50000000000000 : ℝ)*(sp6) + (1669048095253763/100000000000000 : ℝ)*(sp7) + (1669048095253763/100000000000000 : ℝ)*(f.failure) + (1758499290928271/50000000000000 : ℝ)*(f.sum) + (310179478841261/61525000000000000000000000000 : ℝ)*base65 + (316429044138531133/96132812500000000000000000000000 : ℝ)*base68 + (161095342743374883/96132812500000000000000000000000 : ℝ)*base70 + (1115436574802250117/96132812500000000000000000000000 : ℝ)*base71 + (1912620272533/7690625000000000000000000000 : ℝ)*base74 + (360066313717390859/192265625000000000000000000000000 : ℝ)*base75 + (1455408562482859609/192265625000000000000000000000000 : ℝ)*base77 + (107379919024781133/96132812500000000000000000000000 : ℝ)*base80 + (24554089298767/7690625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (18497507/5000000000000000000000 : ℝ)*base90 + (18497507/5000000000000000000000 : ℝ)*base92 + (18497507/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1358_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9671/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1991/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8021/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1358_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1358_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1991/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8021/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1358_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1358_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1358_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1991/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8021/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1358_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
