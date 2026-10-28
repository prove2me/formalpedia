-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1184_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:50:28.426113+00:00
-- url     : https://prove2.me/submissions/693d5eed-fcbf-47d9-acf4-396a74aa4948

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
theorem support_rectangle_w1184_s0_0 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-234823591/1250000000 : ℝ)*x 0 + (604467367/1000000000 : ℝ)*x 1 + (2392880549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234823591/1250000000 : ℝ)^8377 ≤ (10935812192641/100000000000000 : ℝ)^6329 := by
    have hnat : (234823591 : ℕ)^8377*100000000000000^6329 ≤ 10935812192641^6329*1250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234823591 1250000000 10935812192641 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604467367/1000000000 : ℝ)^8377 ≤ (25680137587709/50000000000000 : ℝ)^6329 := by
    have hnat : (604467367 : ℕ)^8377*50000000000000^6329 ≤ 25680137587709^6329*1000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604467367 1000000000 25680137587709 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2392880549/5000000000 : ℝ)^8377 ≤ (4712989077311/12500000000000 : ℝ)^6329 := by
    have hnat : (2392880549 : ℕ)^8377*12500000000000^6329 ≤ 4712989077311^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392880549 5000000000 4712989077311 12500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-234823591/1250000000 : ℝ), (604467367/1000000000 : ℝ), (2392880549/5000000000 : ℝ)] ![(10935812192641/100000000000000 : ℝ), (25680137587709/50000000000000 : ℝ), (4712989077311/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-234823591/1250000000 : ℝ)|^8377 ≤ (10935812192641/100000000000000 : ℝ)^6329
        have hw : |(-234823591/1250000000 : ℝ)|=(234823591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(604467367/1000000000 : ℝ)|^8377 ≤ (25680137587709/50000000000000 : ℝ)^6329
        have hw : |(604467367/1000000000 : ℝ)|=(604467367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2392880549/5000000000 : ℝ)|^8377 ≤ (4712989077311/12500000000000 : ℝ)^6329
        have hw : |(2392880549/5000000000 : ℝ)|=(2392880549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s0_1 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5514427347/10000000000 : ℝ)*x 0 + (-2599879559/10000000000 : ℝ)*x 1 + (4785761099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5514427347/10000000000 : ℝ)^8377 ≤ (45483364746131/100000000000000 : ℝ)^6329 := by
    have hnat : (5514427347 : ℕ)^8377*100000000000000^6329 ≤ 45483364746131^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514427347 10000000000 45483364746131 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2599879559/10000000000 : ℝ)^8377 ≤ (525397581473/3125000000000 : ℝ)^6329 := by
    have hnat : (2599879559 : ℕ)^8377*3125000000000^6329 ≤ 525397581473^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599879559 10000000000 525397581473 3125000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4785761099/10000000000 : ℝ)^8377 ≤ (9425978157229/25000000000000 : ℝ)^6329 := by
    have hnat : (4785761099 : ℕ)^8377*25000000000000^6329 ≤ 9425978157229^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785761099 10000000000 9425978157229 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5514427347/10000000000 : ℝ), (-2599879559/10000000000 : ℝ), (4785761099/10000000000 : ℝ)] ![(45483364746131/100000000000000 : ℝ), (525397581473/3125000000000 : ℝ), (9425978157229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5514427347/10000000000 : ℝ)|^8377 ≤ (45483364746131/100000000000000 : ℝ)^6329
        have hw : |(5514427347/10000000000 : ℝ)|=(5514427347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2599879559/10000000000 : ℝ)|^8377 ≤ (525397581473/3125000000000 : ℝ)^6329
        have hw : |(-2599879559/10000000000 : ℝ)|=(2599879559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4785761099/10000000000 : ℝ)|^8377 ≤ (9425978157229/25000000000000 : ℝ)^6329
        have hw : |(4785761099/10000000000 : ℝ)|=(4785761099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s0_2 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757213663/5000000000 : ℝ)*x 0 + (4785761103/10000000000 : ℝ)*x 1 + (-2599879581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757213663/5000000000 : ℝ)^8377 ≤ (45483364516873/100000000000000 : ℝ)^6329 := by
    have hnat : (2757213663 : ℕ)^8377*100000000000000^6329 ≤ 45483364516873^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757213663 5000000000 45483364516873 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4785761103/10000000000 : ℝ)^8377 ≤ (37703912670627/100000000000000 : ℝ)^6329 := by
    have hnat : (4785761103 : ℕ)^8377*100000000000000^6329 ≤ 37703912670627^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785761103 10000000000 37703912670627 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599879581/10000000000 : ℝ)^8377 ≤ (210159034943/1250000000000 : ℝ)^6329 := by
    have hnat : (2599879581 : ℕ)^8377*1250000000000^6329 ≤ 210159034943^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599879581 10000000000 210159034943 1250000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757213663/5000000000 : ℝ), (4785761103/10000000000 : ℝ), (-2599879581/10000000000 : ℝ)] ![(45483364516873/100000000000000 : ℝ), (37703912670627/100000000000000 : ℝ), (210159034943/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757213663/5000000000 : ℝ)|^8377 ≤ (45483364516873/100000000000000 : ℝ)^6329
        have hw : |(2757213663/5000000000 : ℝ)|=(2757213663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4785761103/10000000000 : ℝ)|^8377 ≤ (37703912670627/100000000000000 : ℝ)^6329
        have hw : |(4785761103/10000000000 : ℝ)|=(4785761103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2599879581/10000000000 : ℝ)|^8377 ≤ (210159034943/1250000000000 : ℝ)^6329
        have hw : |(-2599879581/10000000000 : ℝ)|=(2599879581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s0_3 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4197615207/10000000000 : ℝ)*x 0 + (1559606129/5000000000 : ℝ)*x 1 + (5644435729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197615207/10000000000 : ℝ)^8377 ≤ (792410312059/2500000000000 : ℝ)^6329 := by
    have hnat : (4197615207 : ℕ)^8377*2500000000000^6329 ≤ 792410312059^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197615207 10000000000 792410312059 2500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559606129/5000000000 : ℝ)^8377 ≤ (5348882094479/25000000000000 : ℝ)^6329 := by
    have hnat : (1559606129 : ℕ)^8377*25000000000000^6329 ≤ 5348882094479^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559606129 5000000000 5348882094479 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5644435729/10000000000 : ℝ)^8377 ≤ (23454029561017/50000000000000 : ℝ)^6329 := by
    have hnat : (5644435729 : ℕ)^8377*50000000000000^6329 ≤ 23454029561017^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5644435729 10000000000 23454029561017 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197615207/10000000000 : ℝ), (1559606129/5000000000 : ℝ), (5644435729/10000000000 : ℝ)] ![(792410312059/2500000000000 : ℝ), (5348882094479/25000000000000 : ℝ), (23454029561017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197615207/10000000000 : ℝ)|^8377 ≤ (792410312059/2500000000000 : ℝ)^6329
        have hw : |(4197615207/10000000000 : ℝ)|=(4197615207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1559606129/5000000000 : ℝ)|^8377 ≤ (5348882094479/25000000000000 : ℝ)^6329
        have hw : |(1559606129/5000000000 : ℝ)|=(1559606129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5644435729/10000000000 : ℝ)|^8377 ≤ (23454029561017/50000000000000 : ℝ)^6329
        have hw : |(5644435729/10000000000 : ℝ)|=(5644435729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s0_4 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-941805943/5000000000 : ℝ)*x 0 + (2409107561/5000000000 : ℝ)*x 1 + (6011075621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941805943/5000000000 : ℝ)^8377 ≤ (1371816546071/12500000000000 : ℝ)^6329 := by
    have hnat : (941805943 : ℕ)^8377*12500000000000^6329 ≤ 1371816546071^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941805943 5000000000 1371816546071 12500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2409107561/5000000000 : ℝ)^8377 ≤ (38042704422269/100000000000000 : ℝ)^6329 := by
    have hnat : (2409107561 : ℕ)^8377*100000000000000^6329 ≤ 38042704422269^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409107561 5000000000 38042704422269 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6011075621/10000000000 : ℝ)^8377 ≤ (5098276320087/10000000000000 : ℝ)^6329 := by
    have hnat : (6011075621 : ℕ)^8377*10000000000000^6329 ≤ 5098276320087^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6011075621 10000000000 5098276320087 10000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-941805943/5000000000 : ℝ), (2409107561/5000000000 : ℝ), (6011075621/10000000000 : ℝ)] ![(1371816546071/12500000000000 : ℝ), (38042704422269/100000000000000 : ℝ), (5098276320087/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-941805943/5000000000 : ℝ)|^8377 ≤ (1371816546071/12500000000000 : ℝ)^6329
        have hw : |(-941805943/5000000000 : ℝ)|=(941805943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2409107561/5000000000 : ℝ)|^8377 ≤ (38042704422269/100000000000000 : ℝ)^6329
        have hw : |(2409107561/5000000000 : ℝ)|=(2409107561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6011075621/10000000000 : ℝ)|^8377 ≤ (5098276320087/10000000000000 : ℝ)^6329
        have hw : |(6011075621/10000000000 : ℝ)|=(6011075621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s0_5 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586076807/5000000000 : ℝ)*x 0 + (-1374565269/10000000000 : ℝ)*x 1 + (6011075309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586076807/5000000000 : ℝ)^8377 ≤ (41784806797713/100000000000000 : ℝ)^6329 := by
    have hnat : (2586076807 : ℕ)^8377*100000000000000^6329 ≤ 41784806797713^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586076807 5000000000 41784806797713 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374565269/10000000000 : ℝ)^8377 ≤ (3616216744837/50000000000000 : ℝ)^6329 := by
    have hnat : (1374565269 : ℕ)^8377*50000000000000^6329 ≤ 3616216744837^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374565269 10000000000 3616216744837 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6011075309/10000000000 : ℝ)^8377 ≤ (25491379849181/50000000000000 : ℝ)^6329 := by
    have hnat : (6011075309 : ℕ)^8377*50000000000000^6329 ≤ 25491379849181^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6011075309 10000000000 25491379849181 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586076807/5000000000 : ℝ), (-1374565269/10000000000 : ℝ), (6011075309/10000000000 : ℝ)] ![(41784806797713/100000000000000 : ℝ), (3616216744837/50000000000000 : ℝ), (25491379849181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586076807/5000000000 : ℝ)|^8377 ≤ (41784806797713/100000000000000 : ℝ)^6329
        have hw : |(2586076807/5000000000 : ℝ)|=(2586076807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1374565269/10000000000 : ℝ)|^8377 ≤ (3616216744837/50000000000000 : ℝ)^6329
        have hw : |(-1374565269/10000000000 : ℝ)|=(1374565269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6011075309/10000000000 : ℝ)|^8377 ≤ (25491379849181/50000000000000 : ℝ)^6329
        have hw : |(6011075309/10000000000 : ℝ)|=(6011075309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s0_6 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586076777/5000000000 : ℝ)*x 0 + (3005537739/5000000000 : ℝ)*x 1 + (-1374565089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586076777/5000000000 : ℝ)^8377 ≤ (10446201539033/25000000000000 : ℝ)^6329 := by
    have hnat : (2586076777 : ℕ)^8377*25000000000000^6329 ≤ 10446201539033^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586076777 5000000000 10446201539033 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3005537739/5000000000 : ℝ)^8377 ≤ (25491380797777/50000000000000 : ℝ)^6329 := by
    have hnat : (3005537739 : ℕ)^8377*50000000000000^6329 ≤ 25491380797777^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005537739 5000000000 25491380797777 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1374565089/10000000000 : ℝ)^8377 ≤ (3616216118057/50000000000000 : ℝ)^6329 := by
    have hnat : (1374565089 : ℕ)^8377*50000000000000^6329 ≤ 3616216118057^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374565089 10000000000 3616216118057 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586076777/5000000000 : ℝ), (3005537739/5000000000 : ℝ), (-1374565089/10000000000 : ℝ)] ![(10446201539033/25000000000000 : ℝ), (25491380797777/50000000000000 : ℝ), (3616216118057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586076777/5000000000 : ℝ)|^8377 ≤ (10446201539033/25000000000000 : ℝ)^6329
        have hw : |(2586076777/5000000000 : ℝ)|=(2586076777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3005537739/5000000000 : ℝ)|^8377 ≤ (25491380797777/50000000000000 : ℝ)^6329
        have hw : |(3005537739/5000000000 : ℝ)|=(3005537739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1374565089/10000000000 : ℝ)|^8377 ≤ (3616216118057/50000000000000 : ℝ)^6329
        have hw : |(-1374565089/10000000000 : ℝ)|=(1374565089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s0_7 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42076911/100000000 : ℝ)*x 0 + (348708533/625000000 : ℝ)*x 1 + (796651539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42076911/100000000 : ℝ)^8377 ≤ (1589857752263/5000000000000 : ℝ)^6329 := by
    have hnat : (42076911 : ℕ)^8377*5000000000000^6329 ≤ 1589857752263^6329*100000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42076911 100000000 1589857752263 5000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (348708533/625000000 : ℝ)^8377 ≤ (23096663976507/50000000000000 : ℝ)^6329 := by
    have hnat : (348708533 : ℕ)^8377*50000000000000^6329 ≤ 23096663976507^6329*625000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348708533 625000000 23096663976507 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796651539/2500000000 : ℝ)^8377 ≤ (22009516991371/100000000000000 : ℝ)^6329 := by
    have hnat : (796651539 : ℕ)^8377*100000000000000^6329 ≤ 22009516991371^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796651539 2500000000 22009516991371 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42076911/100000000 : ℝ), (348708533/625000000 : ℝ), (796651539/2500000000 : ℝ)] ![(1589857752263/5000000000000 : ℝ), (23096663976507/50000000000000 : ℝ), (22009516991371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42076911/100000000 : ℝ)|^8377 ≤ (1589857752263/5000000000000 : ℝ)^6329
        have hw : |(42076911/100000000 : ℝ)|=(42076911/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(348708533/625000000 : ℝ)|^8377 ≤ (23096663976507/50000000000000 : ℝ)^6329
        have hw : |(348708533/625000000 : ℝ)|=(348708533/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796651539/2500000000 : ℝ)|^8377 ≤ (22009516991371/100000000000000 : ℝ)^6329
        have hw : |(796651539/2500000000 : ℝ)|=(796651539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1184_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (117/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5531/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1047/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1047 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1047*1^256 ≤ 0^256*1^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1047/256 : ℝ) ≤ (2357694566666689447/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1047 ≤ (2357694566666689447/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1047*100000000000000000000^256 ≤ 2357694566666689447^256*5^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2357694566666689447 100000000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2357694566666689447/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1047 := by
      have hnat : (1 : ℕ)^256*1^1047 ≤ 1^1047*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (102357694566666689447/100000000000000000000 : ℝ) ≤ (5028570550949507/5000000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (102357694566666689447/100000000000000000000 : ℝ)^256 ≤ (5028570550949507/5000000000000000 : ℝ)^1047 := by
      have hnat : (102357694566666689447 : ℕ)^256*5000000000000000^1047 ≤ 5028570550949507^1047*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102357694566666689447 100000000000000000000 5028570550949507 5000000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028570550949507/5000000000000000 : ℝ)) (X := (102357694566666689447/100000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (52357694566666689447/50000000000000000000 : ℝ) ≤ (2528570550949507/2500000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (52357694566666689447/50000000000000000000 : ℝ)^256 ≤ (2528570550949507/2500000000000000 : ℝ)^1047 := by
      have hnat : (52357694566666689447 : ℕ)^256*2500000000000000^1047 ≤ 2528570550949507^1047*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52357694566666689447 50000000000000000000 2528570550949507 2500000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528570550949507/2500000000000000 : ℝ)) (X := (52357694566666689447/50000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28570550949507/2000000000000000 : ℝ)*(0 : ℝ))^(1047/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(28570550949507/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2357694566666689447/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28570550949507/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1047/256 : ℝ) := by
    rw [show (1 : ℝ)+(28570550949507/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028570550949507/5000000000000000 : ℝ) by norm_num, show 1+(2357694566666689447/100000000000000000000 : ℝ)+(0 : ℝ)=(102357694566666689447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2357694566666689447/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28570550949507/2000000000000000 : ℝ)*(2/5 : ℝ))^(1047/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(28570550949507/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528570550949507/2500000000000000 : ℝ) by norm_num, show 1+2*(2357694566666689447/100000000000000000000 : ℝ)=(52357694566666689447/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28570550949507/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28570550949507/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28570550949507/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28570550949507/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28570550949507/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28570550949507/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-234823591/1250000000 : ℝ)*X 0 0+(604467367/1000000000 : ℝ)*X 0 1+(2392880549/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5514427347/10000000000 : ℝ)*X 1 0+(-2599879559/10000000000 : ℝ)*X 1 1+(4785761099/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2757213663/5000000000 : ℝ)*X 2 0+(4785761103/10000000000 : ℝ)*X 2 1+(-2599879581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4197615207/10000000000 : ℝ)*X 0 0+(1559606129/5000000000 : ℝ)*X 0 1+(5644435729/10000000000 : ℝ)*X 0 2+(4197615207/10000000000 : ℝ)*X 1 0+(1559606129/5000000000 : ℝ)*X 1 1+(5644435729/10000000000 : ℝ)*X 1 2+(4197615207/10000000000 : ℝ)*X 2 0+(1559606129/5000000000 : ℝ)*X 2 1+(5644435729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-941805943/5000000000 : ℝ)*X 0 0+(2409107561/5000000000 : ℝ)*X 0 1+(6011075621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586076807/5000000000 : ℝ)*X 1 0+(-1374565269/10000000000 : ℝ)*X 1 1+(6011075309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2586076777/5000000000 : ℝ)*X 2 0+(3005537739/5000000000 : ℝ)*X 2 1+(-1374565089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((42076911/100000000 : ℝ)*X 0 0+(348708533/625000000 : ℝ)*X 0 1+(796651539/2500000000 : ℝ)*X 0 2+(42076911/100000000 : ℝ)*X 1 0+(348708533/625000000 : ℝ)*X 1 1+(796651539/2500000000 : ℝ)*X 1 2+(42076911/100000000 : ℝ)*X 2 0+(348708533/625000000 : ℝ)*X 2 1+(796651539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109352296115837841533919/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11572031/20000000000000 : ℝ)*(base1) + (1340286039/100000000000000 : ℝ)*(base19) + (623266811/50000000000000 : ℝ)*(base23) + (90727409/100000000000000 : ℝ)*(base24) + (38593419/12500000000000 : ℝ)*(upper3) + (595176148450361/100000000000000 : ℝ)*(major0) + (595176148450361/100000000000000 : ℝ)*(major1) + (595176148450361/100000000000000 : ℝ)*(major2) + (794340861168869/100000000000000 : ℝ)*(sp0) + (794342421436597/100000000000000 : ℝ)*(sp1) + (158868484892321/20000000000000 : ℝ)*(sp2) + (396005937118869/100000000000000 : ℝ)*(sp3) + (1479206961/50000000000000 : ℝ)*(sp4) + (589486307/25000000000000 : ℝ)*(sp7) + (99002088231063/25000000000000 : ℝ)*(f.failure) + (198585940430659/25000000000000 : ℝ)*(f.sum) + (77742591022027/100000000000000000000000000000 : ℝ)*base65 + (185596746922027/200000000000000000000000000000 : ℝ)*base67 + (1182785648322027/200000000000000000000000000000 : ℝ)*base69 + (391149238522027/200000000000000000000000000000 : ℝ)*base71 + (76978820622027/100000000000000000000000000000 : ℝ)*base73 + (345288372522027/200000000000000000000000000000 : ℝ)*base75 + (1205869224322027/200000000000000000000000000000 : ℝ)*base77 + (2851773277973/200000000000000000000000000000 : ℝ)*base80 + (500524550522027/100000000000000000000000000000 : ℝ)*base81 + (24141269/2500000000000000000000 : ℝ)*base90 + (24141269/2500000000000000000000 : ℝ)*base92 + (24141269/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32124039975857486004639/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35100187/50000000000000 : ℝ)*(base1) + (324291429/20000000000000 : ℝ)*(base19) + (1615092953/100000000000000 : ℝ)*(base23) + (172701031/100000000000000 : ℝ)*(upper3) + (195031401/100000000000000 : ℝ)*(upper5) + (62812694006041/10000000000000 : ℝ)*(major0) + (62812694006041/10000000000000 : ℝ)*(major1) + (62812694006041/10000000000000 : ℝ)*(major2) + (1655626033/50000000000000 : ℝ)*(sp1) + (1681018651/50000000000000 : ℝ)*(sp2) + (167664227305833/20000000000000 : ℝ)*(sp4) + (41915806680979/5000000000000 : ℝ)*(sp5) + (838316089198537/100000000000000 : ℝ)*(sp6) + (417932529431379/100000000000000 : ℝ)*(sp7) + (417932599631753/100000000000000 : ℝ)*(f.failure) + (104790133291099/12500000000000 : ℝ)*(f.sum) + (12346426871787/10000000000000000000000000000 : ℝ)*base65 + (120917239131787/20000000000000000000000000000 : ℝ)*base67 + (71581032191787/20000000000000000000000000000 : ℝ)*base69 + (94583385531787/20000000000000000000000000000 : ℝ)*base71 + (1738118008213/10000000000000000000000000000 : ℝ)*base74 + (225658146411787/20000000000000000000000000000 : ℝ)*base75 + (91034306971787/20000000000000000000000000000 : ℝ)*base77 + (45241105891787/20000000000000000000000000000 : ℝ)*base79 + (37867494718213/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (54593739/10000000000000000000000 : ℝ)*base90 + (54593739/10000000000000000000000 : ℝ)*base92 + (54593739/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1184_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (117/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5531/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1184_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1184_s1_0 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-83208477/400000000 : ℝ)*x 0 + (5690433071/10000000000 : ℝ)*x 1 + (1002186979/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83208477/400000000 : ℝ)^8377 ≤ (312891771629/2500000000000 : ℝ)^6329 := by
    have hnat : (83208477 : ℕ)^8377*2500000000000^6329 ≤ 312891771629^6329*400000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83208477 400000000 312891771629 2500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5690433071/10000000000 : ℝ)^8377 ≤ (47414681392103/100000000000000 : ℝ)^6329 := by
    have hnat : (5690433071 : ℕ)^8377*100000000000000^6329 ≤ 47414681392103^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690433071 10000000000 47414681392103 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002186979/2000000000 : ℝ)^8377 ≤ (1252176491647/3125000000000 : ℝ)^6329 := by
    have hnat : (1002186979 : ℕ)^8377*3125000000000^6329 ≤ 1252176491647^6329*2000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002186979 2000000000 1252176491647 3125000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83208477/400000000 : ℝ), (5690433071/10000000000 : ℝ), (1002186979/2000000000 : ℝ)] ![(312891771629/2500000000000 : ℝ), (47414681392103/100000000000000 : ℝ), (1252176491647/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83208477/400000000 : ℝ)|^8377 ≤ (312891771629/2500000000000 : ℝ)^6329
        have hw : |(-83208477/400000000 : ℝ)|=(83208477/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5690433071/10000000000 : ℝ)|^8377 ≤ (47414681392103/100000000000000 : ℝ)^6329
        have hw : |(5690433071/10000000000 : ℝ)|=(5690433071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002186979/2000000000 : ℝ)|^8377 ≤ (1252176491647/3125000000000 : ℝ)^6329
        have hw : |(1002186979/2000000000 : ℝ)|=(1002186979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s1_1 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5416821363/10000000000 : ℝ)*x 0 + (-2446129241/10000000000 : ℝ)*x 1 + (1252733781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416821363/10000000000 : ℝ)^8377 ≤ (44420858472411/100000000000000 : ℝ)^6329 := by
    have hnat : (5416821363 : ℕ)^8377*100000000000000^6329 ≤ 44420858472411^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416821363 10000000000 44420858472411 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2446129241/10000000000 : ℝ)^8377 ≤ (1550949136249/10000000000000 : ℝ)^6329 := by
    have hnat : (2446129241 : ℕ)^8377*10000000000000^6329 ≤ 1550949136249^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446129241 10000000000 1550949136249 10000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252733781/2500000000 : ℝ)^8377 ≤ (20034825078221/50000000000000 : ℝ)^6329 := by
    have hnat : (1252733781 : ℕ)^8377*50000000000000^6329 ≤ 20034825078221^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252733781 2500000000 20034825078221 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416821363/10000000000 : ℝ), (-2446129241/10000000000 : ℝ), (1252733781/2500000000 : ℝ)] ![(44420858472411/100000000000000 : ℝ), (1550949136249/10000000000000 : ℝ), (20034825078221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416821363/10000000000 : ℝ)|^8377 ≤ (44420858472411/100000000000000 : ℝ)^6329
        have hw : |(5416821363/10000000000 : ℝ)|=(5416821363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2446129241/10000000000 : ℝ)|^8377 ≤ (1550949136249/10000000000000 : ℝ)^6329
        have hw : |(-2446129241/10000000000 : ℝ)|=(2446129241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252733781/2500000000 : ℝ)|^8377 ≤ (20034825078221/50000000000000 : ℝ)^6329
        have hw : |(1252733781/2500000000 : ℝ)|=(1252733781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s1_2 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1354205133/2500000000 : ℝ)*x 0 + (2505467841/5000000000 : ℝ)*x 1 + (-2446129611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354205133/2500000000 : ℝ)^8377 ≤ (11105212363153/25000000000000 : ℝ)^6329 := by
    have hnat : (1354205133 : ℕ)^8377*25000000000000^6329 ≤ 11105212363153^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354205133 2500000000 11105212363153 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2505467841/5000000000 : ℝ)^8377 ≤ (40069656062319/100000000000000 : ℝ)^6329 := by
    have hnat : (2505467841 : ℕ)^8377*100000000000000^6329 ≤ 40069656062319^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2505467841 5000000000 40069656062319 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2446129611/10000000000 : ℝ)^8377 ≤ (7754747233787/50000000000000 : ℝ)^6329 := by
    have hnat : (2446129611 : ℕ)^8377*50000000000000^6329 ≤ 7754747233787^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446129611 10000000000 7754747233787 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354205133/2500000000 : ℝ), (2505467841/5000000000 : ℝ), (-2446129611/10000000000 : ℝ)] ![(11105212363153/25000000000000 : ℝ), (40069656062319/100000000000000 : ℝ), (7754747233787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354205133/2500000000 : ℝ)|^8377 ≤ (11105212363153/25000000000000 : ℝ)^6329
        have hw : |(1354205133/2500000000 : ℝ)|=(1354205133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2505467841/5000000000 : ℝ)|^8377 ≤ (40069656062319/100000000000000 : ℝ)^6329
        have hw : |(2505467841/5000000000 : ℝ)|=(2505467841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2446129611/10000000000 : ℝ)|^8377 ≤ (7754747233787/50000000000000 : ℝ)^6329
        have hw : |(-2446129611/10000000000 : ℝ)|=(2446129611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s1_3 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2156928989/5000000000 : ℝ)*x 0 + (1842427457/5000000000 : ℝ)*x 1 + (315490289/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156928989/5000000000 : ℝ)^8377 ≤ (16431686845583/50000000000000 : ℝ)^6329 := by
    have hnat : (2156928989 : ℕ)^8377*50000000000000^6329 ≤ 16431686845583^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156928989 5000000000 16431686845583 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842427457/5000000000 : ℝ)^8377 ≤ (26675860875261/100000000000000 : ℝ)^6329 := by
    have hnat : (1842427457 : ℕ)^8377*100000000000000^6329 ≤ 26675860875261^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842427457 5000000000 26675860875261 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315490289/625000000 : ℝ)^8377 ≤ (5057595676687/12500000000000 : ℝ)^6329 := by
    have hnat : (315490289 : ℕ)^8377*12500000000000^6329 ≤ 5057595676687^6329*625000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315490289 625000000 5057595676687 12500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156928989/5000000000 : ℝ), (1842427457/5000000000 : ℝ), (315490289/625000000 : ℝ)] ![(16431686845583/50000000000000 : ℝ), (26675860875261/100000000000000 : ℝ), (5057595676687/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156928989/5000000000 : ℝ)|^8377 ≤ (16431686845583/50000000000000 : ℝ)^6329
        have hw : |(2156928989/5000000000 : ℝ)|=(2156928989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1842427457/5000000000 : ℝ)|^8377 ≤ (26675860875261/100000000000000 : ℝ)^6329
        have hw : |(1842427457/5000000000 : ℝ)|=(1842427457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315490289/625000000 : ℝ)|^8377 ≤ (5057595676687/12500000000000 : ℝ)^6329
        have hw : |(315490289/625000000 : ℝ)|=(315490289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s1_4 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-208096189/1000000000 : ℝ)*x 0 + (627508137/1250000000 : ℝ)*x 1 + (2840562169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208096189/1000000000 : ℝ)^8377 ≤ (12521643504597/100000000000000 : ℝ)^6329 := by
    have hnat : (208096189 : ℕ)^8377*100000000000000^6329 ≤ 12521643504597^6329*1000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208096189 1000000000 12521643504597 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627508137/1250000000 : ℝ)^8377 ≤ (40166310334571/100000000000000 : ℝ)^6329 := by
    have hnat : (627508137 : ℕ)^8377*100000000000000^6329 ≤ 40166310334571^6329*1250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627508137 1250000000 40166310334571 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2840562169/5000000000 : ℝ)^8377 ≤ (9462409230211/20000000000000 : ℝ)^6329 := by
    have hnat : (2840562169 : ℕ)^8377*20000000000000^6329 ≤ 9462409230211^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840562169 5000000000 9462409230211 20000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208096189/1000000000 : ℝ), (627508137/1250000000 : ℝ), (2840562169/5000000000 : ℝ)] ![(12521643504597/100000000000000 : ℝ), (40166310334571/100000000000000 : ℝ), (9462409230211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208096189/1000000000 : ℝ)|^8377 ≤ (12521643504597/100000000000000 : ℝ)^6329
        have hw : |(-208096189/1000000000 : ℝ)|=(208096189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(627508137/1250000000 : ℝ)|^8377 ≤ (40166310334571/100000000000000 : ℝ)^6329
        have hw : |(627508137/1250000000 : ℝ)|=(627508137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2840562169/5000000000 : ℝ)|^8377 ≤ (9462409230211/20000000000000 : ℝ)^6329
        have hw : |(2840562169/5000000000 : ℝ)|=(2840562169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s1_5 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621123851/5000000000 : ℝ)*x 0 + (-1775938769/10000000000 : ℝ)*x 1 + (5681125831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621123851/5000000000 : ℝ)^8377 ≤ (42535962781159/100000000000000 : ℝ)^6329 := by
    have hnat : (2621123851 : ℕ)^8377*100000000000000^6329 ≤ 42535962781159^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621123851 5000000000 42535962781159 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1775938769/10000000000 : ℝ)^8377 ≤ (2030394919291/20000000000000 : ℝ)^6329 := by
    have hnat : (1775938769 : ℕ)^8377*20000000000000^6329 ≤ 2030394919291^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775938769 10000000000 2030394919291 20000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5681125831/10000000000 : ℝ)^8377 ≤ (9462412521611/20000000000000 : ℝ)^6329 := by
    have hnat : (5681125831 : ℕ)^8377*20000000000000^6329 ≤ 9462412521611^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681125831 10000000000 9462412521611 20000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621123851/5000000000 : ℝ), (-1775938769/10000000000 : ℝ), (5681125831/10000000000 : ℝ)] ![(42535962781159/100000000000000 : ℝ), (2030394919291/20000000000000 : ℝ), (9462412521611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621123851/5000000000 : ℝ)|^8377 ≤ (42535962781159/100000000000000 : ℝ)^6329
        have hw : |(2621123851/5000000000 : ℝ)|=(2621123851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1775938769/10000000000 : ℝ)|^8377 ≤ (2030394919291/20000000000000 : ℝ)^6329
        have hw : |(-1775938769/10000000000 : ℝ)|=(1775938769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5681125831/10000000000 : ℝ)|^8377 ≤ (9462412521611/20000000000000 : ℝ)^6329
        have hw : |(5681125831/10000000000 : ℝ)|=(5681125831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s1_6 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621123703/5000000000 : ℝ)*x 0 + (355070419/625000000 : ℝ)*x 1 + (-443984479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621123703/5000000000 : ℝ)^8377 ≤ (1329248737569/3125000000000 : ℝ)^6329 := by
    have hnat : (2621123703 : ℕ)^8377*3125000000000^6329 ≤ 1329248737569^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621123703 5000000000 1329248737569 3125000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355070419/625000000 : ℝ)^8377 ≤ (47312072230937/100000000000000 : ℝ)^6329 := by
    have hnat : (355070419 : ℕ)^8377*100000000000000^6329 ≤ 47312072230937^6329*625000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355070419 625000000 47312072230937 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443984479/2500000000 : ℝ)^8377 ≤ (5075984071257/50000000000000 : ℝ)^6329 := by
    have hnat : (443984479 : ℕ)^8377*50000000000000^6329 ≤ 5075984071257^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443984479 2500000000 5075984071257 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621123703/5000000000 : ℝ), (355070419/625000000 : ℝ), (-443984479/2500000000 : ℝ)] ![(1329248737569/3125000000000 : ℝ), (47312072230937/100000000000000 : ℝ), (5075984071257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621123703/5000000000 : ℝ)|^8377 ≤ (1329248737569/3125000000000 : ℝ)^6329
        have hw : |(2621123703/5000000000 : ℝ)|=(2621123703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(355070419/625000000 : ℝ)|^8377 ≤ (47312072230937/100000000000000 : ℝ)^6329
        have hw : |(355070419/625000000 : ℝ)|=(355070419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-443984479/2500000000 : ℝ)|^8377 ≤ (5075984071257/50000000000000 : ℝ)^6329
        have hw : |(-443984479/2500000000 : ℝ)|=(443984479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s1_7 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2157679889/5000000000 : ℝ)*x 0 + (502953119/1000000000 : ℝ)*x 1 + (3703524071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157679889/5000000000 : ℝ)^8377 ≤ (32878517540547/100000000000000 : ℝ)^6329 := by
    have hnat : (2157679889 : ℕ)^8377*100000000000000^6329 ≤ 32878517540547^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157679889 5000000000 32878517540547 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502953119/1000000000 : ℝ)^8377 ≤ (40266589161551/100000000000000 : ℝ)^6329 := by
    have hnat : (502953119 : ℕ)^8377*100000000000000^6329 ≤ 40266589161551^6329*1000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502953119 1000000000 40266589161551 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3703524071/10000000000 : ℝ)^8377 ≤ (2685489327387/10000000000000 : ℝ)^6329 := by
    have hnat : (3703524071 : ℕ)^8377*10000000000000^6329 ≤ 2685489327387^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3703524071 10000000000 2685489327387 10000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157679889/5000000000 : ℝ), (502953119/1000000000 : ℝ), (3703524071/10000000000 : ℝ)] ![(32878517540547/100000000000000 : ℝ), (40266589161551/100000000000000 : ℝ), (2685489327387/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157679889/5000000000 : ℝ)|^8377 ≤ (32878517540547/100000000000000 : ℝ)^6329
        have hw : |(2157679889/5000000000 : ℝ)|=(2157679889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502953119/1000000000 : ℝ)|^8377 ≤ (40266589161551/100000000000000 : ℝ)^6329
        have hw : |(502953119/1000000000 : ℝ)|=(502953119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3703524071/10000000000 : ℝ)|^8377 ≤ (2685489327387/10000000000000 : ℝ)^6329
        have hw : |(3703524071/10000000000 : ℝ)|=(3703524071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1184_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5531/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (117/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5881/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (81/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5531/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (117/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5531/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (117/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5531/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (117/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5531/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (117/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5531/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (117/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5531/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (117/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (117/20000 : ℝ) ^ (1047/256 : ℝ) ≤ (73793205181/100000000000000000000 : ℝ) := by
    have hpowers : (117/20000 : ℝ)^1047 ≤ (73793205181/100000000000000000000 : ℝ)^256 := by
      have hnat : (117 : ℕ)^1047*100000000000000000000^256 ≤ 73793205181^256*20000^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117 20000 73793205181 100000000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (117/20000 : ℝ)) (X := (73793205181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hpowhi : (5531/20000 : ℝ) ^ (1047/256 : ℝ) ≤ (16285141085984217/3125000000000000000 : ℝ) := by
    have hpowers : (5531/20000 : ℝ)^1047 ≤ (16285141085984217/3125000000000000000 : ℝ)^256 := by
      have hnat : (5531 : ℕ)^1047*3125000000000000000^256 ≤ 16285141085984217^256*20000^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5531 20000 16285141085984217 3125000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5531/20000 : ℝ)) (X := (16285141085984217/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000073793205181/50000000000000000000 : ℝ) ≤ (312500000112769/312500000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (50000000073793205181/50000000000000000000 : ℝ)^256 ≤ (312500000112769/312500000000000 : ℝ)^1047 := by
      have hnat : (50000000073793205181 : ℕ)^256*312500000000000^1047 ≤ 312500000112769^1047*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000073793205181 50000000000000000000 312500000112769 312500000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312500000112769/312500000000000 : ℝ)) (X := (50000000073793205181/50000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (804168996708357601/800000000000000000 : ℝ) ≤ (2002543382532893/2000000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (804168996708357601/800000000000000000 : ℝ)^256 ≤ (2002543382532893/2000000000000000 : ℝ)^1047 := by
      have hnat : (804168996708357601 : ℕ)^256*2000000000000000^1047 ≤ 2002543382532893^1047*800000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        804168996708357601 800000000000000000 2002543382532893 2000000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002543382532893/2000000000000000 : ℝ)) (X := (804168996708357601/800000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (1578785141085984217/1562500000000000000 : ℝ) ≤ (5012716910860161/5000000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (1578785141085984217/1562500000000000000 : ℝ)^256 ≤ (5012716910860161/5000000000000000 : ℝ)^1047 := by
      have hnat : (1578785141085984217 : ℕ)^256*5000000000000000^1047 ≤ 5012716910860161^1047*1562500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1578785141085984217 1562500000000000000 5012716910860161 5000000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012716910860161/5000000000000000 : ℝ)) (X := (1578785141085984217/1562500000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(73793205181/100000000000000000000 : ℝ) ≤ ((27068512131408966587/27070000000000000000 : ℝ)+2*(12716909055857/2707000000000000 : ℝ)*(117/20000 : ℝ))^(1047/256 : ℝ) := by
    rw [show (27068512131408966587/27070000000000000000 : ℝ)+2*(12716909055857/2707000000000000 : ℝ)*(117/20000 : ℝ)=(312500000112769/312500000000000 : ℝ) by norm_num, show 1+2*(73793205181/100000000000000000000 : ℝ)=(50000000073793205181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16285141085984217/3125000000000000000 : ℝ)+(73793205181/100000000000000000000 : ℝ) ≤ ((27068512131408966587/27070000000000000000 : ℝ)+(12716909055857/2707000000000000 : ℝ)*((5531/20000 : ℝ)+(117/20000 : ℝ)))^(1047/256 : ℝ) := by
    rw [show (27068512131408966587/27070000000000000000 : ℝ)+(12716909055857/2707000000000000 : ℝ)*((5531/20000 : ℝ)+(117/20000 : ℝ))=(2002543382532893/2000000000000000 : ℝ) by norm_num, show 1+(16285141085984217/3125000000000000000 : ℝ)+(73793205181/100000000000000000000 : ℝ)=(804168996708357601/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16285141085984217/3125000000000000000 : ℝ) ≤ ((27068512131408966587/27070000000000000000 : ℝ)+2*(12716909055857/2707000000000000 : ℝ)*(5531/20000 : ℝ))^(1047/256 : ℝ) := by
    rw [show (27068512131408966587/27070000000000000000 : ℝ)+2*(12716909055857/2707000000000000 : ℝ)*(5531/20000 : ℝ)=(5012716910860161/5000000000000000 : ℝ) by norm_num, show 1+2*(16285141085984217/3125000000000000000 : ℝ)=(1578785141085984217/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27068512131408966587/27070000000000000000 : ℝ)*(X 1 0+X 2 0)+(12716909055857/2707000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (117/20000 : ℝ)) (hi := (5531/20000 : ℝ)) (c := (27068512131408966587/27070000000000000000 : ℝ)) (alpha := (12716909055857/2707000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27068512131408966587/27070000000000000000 : ℝ)*(X 0 1+X 2 1)+(12716909055857/2707000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (117/20000 : ℝ)) (hi := (5531/20000 : ℝ)) (c := (27068512131408966587/27070000000000000000 : ℝ)) (alpha := (12716909055857/2707000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27068512131408966587/27070000000000000000 : ℝ)*(X 0 2+X 1 2)+(12716909055857/2707000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (117/20000 : ℝ)) (hi := (5531/20000 : ℝ)) (c := (27068512131408966587/27070000000000000000 : ℝ)) (alpha := (12716909055857/2707000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-83208477/400000000 : ℝ)*X 0 0+(5690433071/10000000000 : ℝ)*X 0 1+(1002186979/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5416821363/10000000000 : ℝ)*X 1 0+(-2446129241/10000000000 : ℝ)*X 1 1+(1252733781/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1354205133/2500000000 : ℝ)*X 2 0+(2505467841/5000000000 : ℝ)*X 2 1+(-2446129611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156928989/5000000000 : ℝ)*X 0 0+(1842427457/5000000000 : ℝ)*X 0 1+(315490289/625000000 : ℝ)*X 0 2+(2156928989/5000000000 : ℝ)*X 1 0+(1842427457/5000000000 : ℝ)*X 1 1+(315490289/625000000 : ℝ)*X 1 2+(2156928989/5000000000 : ℝ)*X 2 0+(1842427457/5000000000 : ℝ)*X 2 1+(315490289/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208096189/1000000000 : ℝ)*X 0 0+(627508137/1250000000 : ℝ)*X 0 1+(2840562169/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2621123851/5000000000 : ℝ)*X 1 0+(-1775938769/10000000000 : ℝ)*X 1 1+(5681125831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2621123703/5000000000 : ℝ)*X 2 0+(355070419/625000000 : ℝ)*X 2 1+(-443984479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2157679889/5000000000 : ℝ)*X 0 0+(502953119/1000000000 : ℝ)*X 0 1+(3703524071/10000000000 : ℝ)*X 0 2+(2157679889/5000000000 : ℝ)*X 1 0+(502953119/1000000000 : ℝ)*X 1 1+(3703524071/10000000000 : ℝ)*X 1 2+(2157679889/5000000000 : ℝ)*X 2 0+(502953119/1000000000 : ℝ)*X 2 1+(3703524071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5028039188675834830857140319/676750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8168473/25000000000000 : ℝ)*(base1) + (893274777/50000000000000 : ℝ)*(base19) + (1560775613/100000000000000 : ℝ)*(base23) + (291476209/100000000000000 : ℝ)*(upper3) + (97683307/100000000000000 : ℝ)*(upper5) + (551346691392721/50000000000000 : ℝ)*(major0) + (551346691392721/50000000000000 : ℝ)*(major1) + (551346691392721/50000000000000 : ℝ)*(major2) + (367921414550779/25000000000000 : ℝ)*(sp0) + (1471693047929441/100000000000000 : ℝ)*(sp1) + (735846636851691/50000000000000 : ℝ)*(sp2) + (73368606822213/10000000000000 : ℝ)*(sp3) + (920894977/10000000000000 : ℝ)*(sp4) + (2791269851/50000000000000 : ℝ)*(sp7) + (183422920858931/25000000000000 : ℝ)*(f.failure) + (294338966895799/20000000000000 : ℝ)*(f.sum) + (78496186009903/67675000000000000000000000000 : ℝ)*base66 + (6420322013206983227/1353500000000000000000000000000000 : ℝ)*base67 + (3001514081205983227/1353500000000000000000000000000000 : ℝ)*base69 + (8844827290923516773/1353500000000000000000000000000000 : ℝ)*base72 + (101251417699643/16918750000000000000000000000 : ℝ)*base73 + (4826098938691983227/1353500000000000000000000000000000 : ℝ)*base75 + (3931610300267016773/1353500000000000000000000000000000 : ℝ)*base78 + (692310868618983227/1353500000000000000000000000000000 : ℝ)*base79 + (132547227893897/67675000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (25708247/2500000000000000000000 : ℝ)*base89 + (25708247/2500000000000000000000 : ℝ)*base91 + (25708247/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100212733891580460277288461/13535000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2510650057/100000000000000 : ℝ)*(base19) + (1450126141/50000000000000 : ℝ)*(base23) + (171626299/100000000000000 : ℝ)*(upper2) + (2275763/500000000000 : ℝ)*(upper3) + (257323349/100000000000000 : ℝ)*(upper5) + (22668654423299/2000000000000 : ℝ)*(major0) + (22668654423299/2000000000000 : ℝ)*(major1) + (22668654423299/2000000000000 : ℝ)*(major2) + (12757783081/100000000000000 : ℝ)*(sp1) + (17190880489/100000000000000 : ℝ)*(sp2) + (1512720685157559/100000000000000 : ℝ)*(sp4) + (1512705416724421/100000000000000 : ℝ)*(sp5) + (378175148506197/25000000000000 : ℝ)*(sp6) + (94268063796667/12500000000000 : ℝ)*(sp7) + (94268063796667/12500000000000 : ℝ)*(f.failure) + (1512720685157559/100000000000000 : ℝ)*(f.sum) + (7577045182643/2707000000000000000000000000 : ℝ)*base66 + (185656349481180513/54140000000000000000000000000000 : ℝ)*base67 + (334848253224020513/54140000000000000000000000000000 : ℝ)*base69 + (185382463396320513/54140000000000000000000000000000 : ℝ)*base71 + (1975037730747/2707000000000000000000000000 : ℝ)*base74 + (404803361868600513/54140000000000000000000000000000 : ℝ)*base75 + (27431597096019487/54140000000000000000000000000000 : ℝ)*base78 + (398102435715140513/54140000000000000000000000000000 : ℝ)*base79 + (609094952053/135350000000000000000000000 : ℝ)*base81 + (3758721/1250000000000000000000 : ℝ)*base90 + (3758721/1250000000000000000000 : ℝ)*base92 + (3758721/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1184_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5531/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (117/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5881/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (81/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1184_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1184_s2_0 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131218061/10000000000 : ℝ)*x 0 + (5503009621/10000000000 : ℝ)*x 1 + (2582942259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131218061/10000000000 : ℝ)^8377 ≤ (6461728526697/50000000000000 : ℝ)^6329 := by
    have hnat : (2131218061 : ℕ)^8377*50000000000000^6329 ≤ 6461728526697^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131218061 10000000000 6461728526697 50000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503009621/10000000000 : ℝ)^8377 ≤ (45358758554813/100000000000000 : ℝ)^6329 := by
    have hnat : (5503009621 : ℕ)^8377*100000000000000^6329 ≤ 45358758554813^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503009621 10000000000 45358758554813 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2582942259/5000000000 : ℝ)^8377 ≤ (41717784374989/100000000000000 : ℝ)^6329 := by
    have hnat : (2582942259 : ℕ)^8377*100000000000000^6329 ≤ 41717784374989^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582942259 5000000000 41717784374989 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131218061/10000000000 : ℝ), (5503009621/10000000000 : ℝ), (2582942259/5000000000 : ℝ)] ![(6461728526697/50000000000000 : ℝ), (45358758554813/100000000000000 : ℝ), (41717784374989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131218061/10000000000 : ℝ)|^8377 ≤ (6461728526697/50000000000000 : ℝ)^6329
        have hw : |(-2131218061/10000000000 : ℝ)|=(2131218061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503009621/10000000000 : ℝ)|^8377 ≤ (45358758554813/100000000000000 : ℝ)^6329
        have hw : |(5503009621/10000000000 : ℝ)|=(5503009621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2582942259/5000000000 : ℝ)|^8377 ≤ (41717784374989/100000000000000 : ℝ)^6329
        have hw : |(2582942259/5000000000 : ℝ)|=(2582942259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s2_1 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686041207/5000000000 : ℝ)*x 0 + (-1153104267/5000000000 : ℝ)*x 1 + (5165888177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686041207/5000000000 : ℝ)^8377 ≤ (1757436211921/4000000000000 : ℝ)^6329 := by
    have hnat : (2686041207 : ℕ)^8377*4000000000000^6329 ≤ 1757436211921^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686041207 5000000000 1757436211921 4000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1153104267/5000000000 : ℝ)^8377 ≤ (896641950107/6250000000000 : ℝ)^6329 := by
    have hnat : (1153104267 : ℕ)^8377*6250000000000^6329 ≤ 896641950107^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153104267 5000000000 896641950107 6250000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5165888177/10000000000 : ℝ)^8377 ≤ (10429455871351/25000000000000 : ℝ)^6329 := by
    have hnat : (5165888177 : ℕ)^8377*25000000000000^6329 ≤ 10429455871351^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5165888177 10000000000 10429455871351 25000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686041207/5000000000 : ℝ), (-1153104267/5000000000 : ℝ), (5165888177/10000000000 : ℝ)] ![(1757436211921/4000000000000 : ℝ), (896641950107/6250000000000 : ℝ), (10429455871351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686041207/5000000000 : ℝ)|^8377 ≤ (1757436211921/4000000000000 : ℝ)^6329
        have hw : |(2686041207/5000000000 : ℝ)|=(2686041207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1153104267/5000000000 : ℝ)|^8377 ≤ (896641950107/6250000000000 : ℝ)^6329
        have hw : |(-1153104267/5000000000 : ℝ)|=(1153104267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5165888177/10000000000 : ℝ)|^8377 ≤ (10429455871351/25000000000000 : ℝ)^6329
        have hw : |(5165888177/10000000000 : ℝ)|=(5165888177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s2_2 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5372083717/10000000000 : ℝ)*x 0 + (1291471577/2500000000 : ℝ)*x 1 + (-2306209247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372083717/10000000000 : ℝ)^8377 ≤ (1098397985077/2500000000000 : ℝ)^6329 := by
    have hnat : (5372083717 : ℕ)^8377*2500000000000^6329 ≤ 1098397985077^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372083717 10000000000 1098397985077 2500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291471577/2500000000 : ℝ)^8377 ≤ (41717803507987/100000000000000 : ℝ)^6329 := by
    have hnat : (1291471577 : ℕ)^8377*100000000000000^6329 ≤ 41717803507987^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291471577 2500000000 41717803507987 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2306209247/10000000000 : ℝ)^8377 ≤ (573851082893/4000000000000 : ℝ)^6329 := by
    have hnat : (2306209247 : ℕ)^8377*4000000000000^6329 ≤ 573851082893^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306209247 10000000000 573851082893 4000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372083717/10000000000 : ℝ), (1291471577/2500000000 : ℝ), (-2306209247/10000000000 : ℝ)] ![(1098397985077/2500000000000 : ℝ), (41717803507987/100000000000000 : ℝ), (573851082893/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372083717/10000000000 : ℝ)|^8377 ≤ (1098397985077/2500000000000 : ℝ)^6329
        have hw : |(5372083717/10000000000 : ℝ)|=(5372083717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1291471577/2500000000 : ℝ)|^8377 ≤ (41717803507987/100000000000000 : ℝ)^6329
        have hw : |(1291471577/2500000000 : ℝ)|=(1291471577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2306209247/10000000000 : ℝ)|^8377 ≤ (573851082893/4000000000000 : ℝ)^6329
        have hw : |(-2306209247/10000000000 : ℝ)|=(2306209247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s2_3 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543619283/1250000000 : ℝ)*x 0 + (4023741019/10000000000 : ℝ)*x 1 + (4699967993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543619283/1250000000 : ℝ)^8377 ≤ (33217722625989/100000000000000 : ℝ)^6329 := by
    have hnat : (543619283 : ℕ)^8377*100000000000000^6329 ≤ 33217722625989^6329*1250000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543619283 1250000000 33217722625989 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4023741019/10000000000 : ℝ)^8377 ≤ (29970384726687/100000000000000 : ℝ)^6329 := by
    have hnat : (4023741019 : ℕ)^8377*100000000000000^6329 ≤ 29970384726687^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023741019 10000000000 29970384726687 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4699967993/10000000000 : ℝ)^8377 ≤ (368118926353/1000000000000 : ℝ)^6329 := by
    have hnat : (4699967993 : ℕ)^8377*1000000000000^6329 ≤ 368118926353^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4699967993 10000000000 368118926353 1000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543619283/1250000000 : ℝ), (4023741019/10000000000 : ℝ), (4699967993/10000000000 : ℝ)] ![(33217722625989/100000000000000 : ℝ), (29970384726687/100000000000000 : ℝ), (368118926353/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543619283/1250000000 : ℝ)|^8377 ≤ (33217722625989/100000000000000 : ℝ)^6329
        have hw : |(543619283/1250000000 : ℝ)|=(543619283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4023741019/10000000000 : ℝ)|^8377 ≤ (29970384726687/100000000000000 : ℝ)^6329
        have hw : |(4023741019/10000000000 : ℝ)|=(4023741019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4699967993/10000000000 : ℝ)|^8377 ≤ (368118926353/1000000000000 : ℝ)^6329
        have hw : |(4699967993/10000000000 : ℝ)|=(4699967993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s2_4 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-85252351/400000000 : ℝ)*x 0 + (5168142849/10000000000 : ℝ)*x 1 + (5500729973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85252351/400000000 : ℝ)^8377 ≤ (12924185137489/100000000000000 : ℝ)^6329 := by
    have hnat : (85252351 : ℕ)^8377*100000000000000^6329 ≤ 12924185137489^6329*400000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85252351 400000000 12924185137489 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5168142849/10000000000 : ℝ)^8377 ≤ (2608870311671/6250000000000 : ℝ)^6329 := by
    have hnat : (5168142849 : ℕ)^8377*6250000000000^6329 ≤ 2608870311671^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168142849 10000000000 2608870311671 6250000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5500729973/10000000000 : ℝ)^8377 ≤ (45333889860261/100000000000000 : ℝ)^6329 := by
    have hnat : (5500729973 : ℕ)^8377*100000000000000^6329 ≤ 45333889860261^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500729973 10000000000 45333889860261 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85252351/400000000 : ℝ), (5168142849/10000000000 : ℝ), (5500729973/10000000000 : ℝ)] ![(12924185137489/100000000000000 : ℝ), (2608870311671/6250000000000 : ℝ), (45333889860261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85252351/400000000 : ℝ)|^8377 ≤ (12924185137489/100000000000000 : ℝ)^6329
        have hw : |(-85252351/400000000 : ℝ)|=(85252351/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5168142849/10000000000 : ℝ)|^8377 ≤ (2608870311671/6250000000000 : ℝ)^6329
        have hw : |(5168142849/10000000000 : ℝ)|=(5168142849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5500729973/10000000000 : ℝ)|^8377 ≤ (45333889860261/100000000000000 : ℝ)^6329
        have hw : |(5500729973/10000000000 : ℝ)|=(5500729973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s2_5 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643154253/5000000000 : ℝ)*x 0 + (-1971365261/10000000000 : ℝ)*x 1 + (5500729981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643154253/5000000000 : ℝ)^8377 ≤ (43009804875331/100000000000000 : ℝ)^6329 := by
    have hnat : (2643154253 : ℕ)^8377*100000000000000^6329 ≤ 43009804875331^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643154253 5000000000 43009804875331 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1971365261/10000000000 : ℝ)^8377 ≤ (11656305157343/100000000000000 : ℝ)^6329 := by
    have hnat : (1971365261 : ℕ)^8377*100000000000000^6329 ≤ 11656305157343^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971365261 10000000000 11656305157343 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5500729981/10000000000 : ℝ)^8377 ≤ (5666736243441/12500000000000 : ℝ)^6329 := by
    have hnat : (5500729981 : ℕ)^8377*12500000000000^6329 ≤ 5666736243441^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500729981 10000000000 5666736243441 12500000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643154253/5000000000 : ℝ), (-1971365261/10000000000 : ℝ), (5500729981/10000000000 : ℝ)] ![(43009804875331/100000000000000 : ℝ), (11656305157343/100000000000000 : ℝ), (5666736243441/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643154253/5000000000 : ℝ)|^8377 ≤ (43009804875331/100000000000000 : ℝ)^6329
        have hw : |(2643154253/5000000000 : ℝ)|=(2643154253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1971365261/10000000000 : ℝ)|^8377 ≤ (11656305157343/100000000000000 : ℝ)^6329
        have hw : |(-1971365261/10000000000 : ℝ)|=(1971365261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5500729981/10000000000 : ℝ)|^8377 ≤ (5666736243441/12500000000000 : ℝ)^6329
        have hw : |(5500729981/10000000000 : ℝ)|=(5500729981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s2_6 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5286308659/10000000000 : ℝ)*x 0 + (2750364993/5000000000 : ℝ)*x 1 + (-492841261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286308659/10000000000 : ℝ)^8377 ≤ (43009806522961/100000000000000 : ℝ)^6329 := by
    have hnat : (5286308659 : ℕ)^8377*100000000000000^6329 ≤ 43009806522961^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286308659 10000000000 43009806522961 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750364993/5000000000 : ℝ)^8377 ≤ (45333890002069/100000000000000 : ℝ)^6329 := by
    have hnat : (2750364993 : ℕ)^8377*100000000000000^6329 ≤ 45333890002069^6329*5000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750364993 5000000000 45333890002069 100000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492841261/2500000000 : ℝ)^8377 ≤ (45532435387/390625000000 : ℝ)^6329 := by
    have hnat : (492841261 : ℕ)^8377*390625000000^6329 ≤ 45532435387^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492841261 2500000000 45532435387 390625000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286308659/10000000000 : ℝ), (2750364993/5000000000 : ℝ), (-492841261/2500000000 : ℝ)] ![(43009806522961/100000000000000 : ℝ), (45333890002069/100000000000000 : ℝ), (45532435387/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286308659/10000000000 : ℝ)|^8377 ≤ (43009806522961/100000000000000 : ℝ)^6329
        have hw : |(5286308659/10000000000 : ℝ)|=(5286308659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750364993/5000000000 : ℝ)|^8377 ≤ (45333890002069/100000000000000 : ℝ)^6329
        have hw : |(2750364993/5000000000 : ℝ)|=(2750364993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492841261/2500000000 : ℝ)|^8377 ≤ (45532435387/390625000000 : ℝ)^6329
        have hw : |(-492841261/2500000000 : ℝ)|=(492841261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1184_s2_7 (p : ℝ) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087284559/2500000000 : ℝ)*x 0 + (4695440693/10000000000 : ℝ)*x 1 + (251769467/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087284559/2500000000 : ℝ)^8377 ≤ (6643916508231/20000000000000 : ℝ)^6329 := by
    have hnat : (1087284559 : ℕ)^8377*20000000000000^6329 ≤ 6643916508231^6329*2500000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087284559 2500000000 6643916508231 20000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4695440693/10000000000 : ℝ)^8377 ≤ (1838248306381/5000000000000 : ℝ)^6329 := by
    have hnat : (4695440693 : ℕ)^8377*5000000000000^6329 ≤ 1838248306381^6329*10000000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4695440693 10000000000 1838248306381 5000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251769467/625000000 : ℝ)^8377 ≤ (6003090264431/20000000000000 : ℝ)^6329 := by
    have hnat : (251769467 : ℕ)^8377*20000000000000^6329 ≤ 6003090264431^6329*625000000^8377 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251769467 625000000 6003090264431 20000000000000 8377 6329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8377/2048 : ℝ)) 8377 6329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087284559/2500000000 : ℝ), (4695440693/10000000000 : ℝ), (251769467/625000000 : ℝ)] ![(6643916508231/20000000000000 : ℝ), (1838248306381/5000000000000 : ℝ), (6003090264431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087284559/2500000000 : ℝ)|^8377 ≤ (6643916508231/20000000000000 : ℝ)^6329
        have hw : |(1087284559/2500000000 : ℝ)|=(1087284559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4695440693/10000000000 : ℝ)|^8377 ≤ (1838248306381/5000000000000 : ℝ)^6329
        have hw : |(4695440693/10000000000 : ℝ)|=(4695440693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251769467/625000000 : ℝ)|^8377 ≤ (6003090264431/20000000000000 : ℝ)^6329
        have hw : |(251769467/625000000 : ℝ)|=(251769467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1184_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (81/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5881/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1157/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16381/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (81/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5881/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (81/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5881/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (81/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5881/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (81/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5881/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (81/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5881/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (81/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5881/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5881/100000 : ℝ) ^ (1047/256 : ℝ) ≤ (231839592981991/25000000000000000000 : ℝ) := by
    have hpowers : (5881/100000 : ℝ)^1047 ≤ (231839592981991/25000000000000000000 : ℝ)^256 := by
      have hnat : (5881 : ℕ)^1047*25000000000000000000^256 ≤ 231839592981991^256*100000^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5881 100000 231839592981991 25000000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5881/100000 : ℝ)) (X := (231839592981991/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hpowhi : (81/400 : ℝ) ^ (1047/256 : ℝ) ≤ (18209446572722543/12500000000000000000 : ℝ) := by
    have hpowers : (81/400 : ℝ)^1047 ≤ (18209446572722543/12500000000000000000 : ℝ)^256 := by
      have hnat : (81 : ℕ)^1047*12500000000000000000^256 ≤ 18209446572722543^256*400^1047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81 400 18209446572722543 12500000000000000000 1047 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81/400 : ℝ)) (X := (18209446572722543/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500231839592981991/12500000000000000000 : ℝ) ≤ (1250005668626551/1250000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (12500231839592981991/12500000000000000000 : ℝ)^256 ≤ (1250005668626551/1250000000000000 : ℝ)^1047 := by
      have hnat : (12500231839592981991 : ℕ)^256*1250000000000000^1047 ≤ 1250005668626551^1047*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500231839592981991 12500000000000000000 1250005668626551 1250000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250005668626551/1250000000000000 : ℝ)) (X := (12500231839592981991/12500000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25036650732738427077/25000000000000000000 : ℝ) ≤ (2500895644324977/2500000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (25036650732738427077/25000000000000000000 : ℝ)^256 ≤ (2500895644324977/2500000000000000 : ℝ)^1047 := by
      have hnat : (25036650732738427077 : ℕ)^256*2500000000000000^1047 ≤ 2500895644324977^1047*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25036650732738427077 25000000000000000000 2500895644324977 2500000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500895644324977/2500000000000000 : ℝ)) (X := (25036650732738427077/25000000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6268209446572722543/6250000000000000000 : ℝ) ≤ (625444987849213/625000000000000 : ℝ) ^ (1047/256 : ℝ) := by
    have hpowers : (6268209446572722543/6250000000000000000 : ℝ)^256 ≤ (625444987849213/625000000000000 : ℝ)^1047 := by
      have hnat : (6268209446572722543 : ℕ)^256*625000000000000^1047 ≤ 625444987849213^1047*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6268209446572722543 6250000000000000000 625444987849213 625000000000000 256 1047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625444987849213/625000000000000 : ℝ)) (X := (6268209446572722543/6250000000000000000 : ℝ)) (by norm_num) 1047 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(231839592981991/25000000000000000000 : ℝ) ≤ ((4489032710651303611/4490312500000000000 : ℝ)+2*(282978263/114952000000 : ℝ)*(5881/100000 : ℝ))^(1047/256 : ℝ) := by
    rw [show (4489032710651303611/4490312500000000000 : ℝ)+2*(282978263/114952000000 : ℝ)*(5881/100000 : ℝ)=(1250005668626551/1250000000000000 : ℝ) by norm_num, show 1+2*(231839592981991/25000000000000000000 : ℝ)=(12500231839592981991/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18209446572722543/12500000000000000000 : ℝ)+(231839592981991/25000000000000000000 : ℝ) ≤ ((4489032710651303611/4490312500000000000 : ℝ)+(282978263/114952000000 : ℝ)*((81/400 : ℝ)+(5881/100000 : ℝ)))^(1047/256 : ℝ) := by
    rw [show (4489032710651303611/4490312500000000000 : ℝ)+(282978263/114952000000 : ℝ)*((81/400 : ℝ)+(5881/100000 : ℝ))=(2500895644324977/2500000000000000 : ℝ) by norm_num, show 1+(18209446572722543/12500000000000000000 : ℝ)+(231839592981991/25000000000000000000 : ℝ)=(25036650732738427077/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18209446572722543/12500000000000000000 : ℝ) ≤ ((4489032710651303611/4490312500000000000 : ℝ)+2*(282978263/114952000000 : ℝ)*(81/400 : ℝ))^(1047/256 : ℝ) := by
    rw [show (4489032710651303611/4490312500000000000 : ℝ)+2*(282978263/114952000000 : ℝ)*(81/400 : ℝ)=(625444987849213/625000000000000 : ℝ) by norm_num, show 1+2*(18209446572722543/12500000000000000000 : ℝ)=(6268209446572722543/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4489032710651303611/4490312500000000000 : ℝ)*(X 1 0+X 2 0)+(282978263/114952000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (5881/100000 : ℝ)) (hi := (81/400 : ℝ)) (c := (4489032710651303611/4490312500000000000 : ℝ)) (alpha := (282978263/114952000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4489032710651303611/4490312500000000000 : ℝ)*(X 0 1+X 2 1)+(282978263/114952000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (5881/100000 : ℝ)) (hi := (81/400 : ℝ)) (c := (4489032710651303611/4490312500000000000 : ℝ)) (alpha := (282978263/114952000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4489032710651303611/4490312500000000000 : ℝ)*(X 0 2+X 1 2)+(282978263/114952000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1047/256 : ℝ)) (lo := (5881/100000 : ℝ)) (hi := (81/400 : ℝ)) (c := (4489032710651303611/4490312500000000000 : ℝ)) (alpha := (282978263/114952000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2131218061/10000000000 : ℝ)*X 0 0+(5503009621/10000000000 : ℝ)*X 0 1+(2582942259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686041207/5000000000 : ℝ)*X 1 0+(-1153104267/5000000000 : ℝ)*X 1 1+(5165888177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5372083717/10000000000 : ℝ)*X 2 0+(1291471577/2500000000 : ℝ)*X 2 1+(-2306209247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543619283/1250000000 : ℝ)*X 0 0+(4023741019/10000000000 : ℝ)*X 0 1+(4699967993/10000000000 : ℝ)*X 0 2+(543619283/1250000000 : ℝ)*X 1 0+(4023741019/10000000000 : ℝ)*X 1 1+(4699967993/10000000000 : ℝ)*X 1 2+(543619283/1250000000 : ℝ)*X 2 0+(4023741019/10000000000 : ℝ)*X 2 1+(4699967993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-85252351/400000000 : ℝ)*X 0 0+(5168142849/10000000000 : ℝ)*X 0 1+(5500729973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643154253/5000000000 : ℝ)*X 1 0+(-1971365261/10000000000 : ℝ)*X 1 1+(5500729981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5286308659/10000000000 : ℝ)*X 2 0+(2750364993/5000000000 : ℝ)*X 2 1+(-492841261/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087284559/2500000000 : ℝ)*X 0 0+(4695440693/10000000000 : ℝ)*X 0 1+(251769467/625000000 : ℝ)*X 0 2+(1087284559/2500000000 : ℝ)*X 1 0+(4695440693/10000000000 : ℝ)*X 1 1+(251769467/625000000 : ℝ)*X 1 2+(1087284559/2500000000 : ℝ)*X 2 0+(4695440693/10000000000 : ℝ)*X 2 1+(251769467/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1184_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13853613613772306418027/2873800000000000000000000000 : ℝ) := by norm_num
    linear_combination (32676583/10000000000000 : ℝ)*(base19) + (115302871/12500000000000 : ℝ)*(base23) + (62873867/50000000000000 : ℝ)*(upper2) + (205086627/50000000000000 : ℝ)*(upper3) + (48066523/25000000000000 : ℝ)*(upper4) + (2222561168115101/100000000000000 : ℝ)*(major0) + (2222561168115101/100000000000000 : ℝ)*(major1) + (2222561168115101/100000000000000 : ℝ)*(major2) + (1483143354951311/50000000000000 : ℝ)*(sp0) + (296631126513539/10000000000000 : ℝ)*(sp1) + (741577667369563/25000000000000 : ℝ)*(sp2) + (739399721236223/50000000000000 : ℝ)*(sp3) + (12440999299/50000000000000 : ℝ)*(sp4) + (11141167853/100000000000000 : ℝ)*(sp7) + (14788105836403/1000000000000 : ℝ)*(f.failure) + (148315579595061/5000000000000 : ℝ)*(f.sum) + (210201157803/44903125000000000000000000 : ℝ)*base65 + (1173817454673898461/449031250000000000000000000000000 : ℝ)*base67 + (332214488185882789/449031250000000000000000000000000 : ℝ)*base70 + (1686786390254382789/449031250000000000000000000000000 : ℝ)*base72 + (63156234844933/14369000000000000000000000000 : ℝ)*base73 + (1883620030169742211/449031250000000000000000000000000 : ℝ)*base75 + (4372086012943867211/449031250000000000000000000000000 : ℝ)*base77 + (2234204745875726539/449031250000000000000000000000000 : ℝ)*base80 + (97429644523/57476000000000000000000000 : ℝ)*base82 + (148311/100000000000000000000 : ℝ)*base89 + (148311/100000000000000000000 : ℝ)*base91 + (148311/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1560347766929823242328922083/224515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (418147567/25000000000000 : ℝ)*(base19) + (1822546411/100000000000000 : ℝ)*(base23) + (6239111/100000000000000 : ℝ)*(upper2) + (207162109/100000000000000 : ℝ)*(upper3) + (146341459/100000000000000 : ℝ)*(upper5) + (1126422794819063/50000000000000 : ℝ)*(major0) + (1126422794819063/50000000000000 : ℝ)*(major1) + (1126422794819063/50000000000000 : ℝ)*(major2) + (8179785091/50000000000000 : ℝ)*(sp1) + (4877636319/25000000000000 : ℝ)*(sp2) + (3006730222007683/100000000000000 : ℝ)*(sp4) + (1503356094923617/50000000000000 : ℝ)*(sp5) + (751677222228999/25000000000000 : ℝ)*(sp6) + (93685045350451/6250000000000 : ℝ)*(sp7) + (93685045350451/6250000000000 : ℝ)*(f.failure) + (3006730222007683/100000000000000 : ℝ)*(f.sum) + (56344714757219/14369000000000000000000000000 : ℝ)*base66 + (390668996660848941/112257812500000000000000000000000 : ℝ)*base68 + (51872072848807309/112257812500000000000000000000000 : ℝ)*base69 + (1840717927428526007/224515625000000000000000000000000 : ℝ)*base72 + (12720546581403/7184500000000000000000000000 : ℝ)*base73 + (2535409682194901007/224515625000000000000000000000000 : ℝ)*base76 + (1956013100459401007/224515625000000000000000000000000 : ℝ)*base78 + (158208663511223993/224515625000000000000000000000000 : ℝ)*base79 + (4734415444559/3592250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2970487/625000000000000000000 : ℝ)*base89 + (2970487/625000000000000000000 : ℝ)*base91 + (2970487/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1184_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (81/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5881/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1157/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16381/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1184_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1184_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1157/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16381/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1184_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1184_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1184_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1047/256 : ℝ) ≤ p) (hpb : p ≤ (8377/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150293837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1157/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16381/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1184_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
