-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1682_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:32:28.599698+00:00
-- url     : https://prove2.me/submissions/2fc45520-01ba-44ab-9db1-d69476bcfe19

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
theorem support_rectangle_w1682_s3_0 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-760022003/5000000000 : ℝ)*x 0 + (5488713359/10000000000 : ℝ)*x 1 + (5133771387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760022003/5000000000 : ℝ)^5079 ≤ (2361522850979/25000000000000 : ℝ)^4055 := by
    have hnat : (760022003 : ℕ)^5079*25000000000000^4055 ≤ 2361522850979^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760022003 5000000000 2361522850979 25000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488713359/10000000000 : ℝ)^5079 ≤ (9434298923929/20000000000000 : ℝ)^4055 := by
    have hnat : (5488713359 : ℕ)^5079*20000000000000^4055 ≤ 9434298923929^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488713359 10000000000 9434298923929 20000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133771387/10000000000 : ℝ)^5079 ≤ (8676482793363/20000000000000 : ℝ)^4055 := by
    have hnat : (5133771387 : ℕ)^5079*20000000000000^4055 ≤ 8676482793363^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133771387 10000000000 8676482793363 20000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-760022003/5000000000 : ℝ), (5488713359/10000000000 : ℝ), (5133771387/10000000000 : ℝ)] ![(2361522850979/25000000000000 : ℝ), (9434298923929/20000000000000 : ℝ), (8676482793363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-760022003/5000000000 : ℝ)|^5079 ≤ (2361522850979/25000000000000 : ℝ)^4055
        have hw : |(-760022003/5000000000 : ℝ)|=(760022003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488713359/10000000000 : ℝ)|^5079 ≤ (9434298923929/20000000000000 : ℝ)^4055
        have hw : |(5488713359/10000000000 : ℝ)|=(5488713359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133771387/10000000000 : ℝ)|^5079 ≤ (8676482793363/20000000000000 : ℝ)^4055
        have hw : |(5133771387/10000000000 : ℝ)|=(5133771387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s3_1 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676441167/5000000000 : ℝ)*x 0 + (-340911439/2000000000 : ℝ)*x 1 + (2566885637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676441167/5000000000 : ℝ)^5079 ≤ (22856965079501/50000000000000 : ℝ)^4055 := by
    have hnat : (2676441167 : ℕ)^5079*50000000000000^4055 ≤ 22856965079501^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676441167 5000000000 22856965079501 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340911439/2000000000 : ℝ)^5079 ≤ (10903657065191/100000000000000 : ℝ)^4055 := by
    have hnat : (340911439 : ℕ)^5079*100000000000000^4055 ≤ 10903657065191^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340911439 2000000000 10903657065191 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566885637/5000000000 : ℝ)^5079 ≤ (43382412770783/100000000000000 : ℝ)^4055 := by
    have hnat : (2566885637 : ℕ)^5079*100000000000000^4055 ≤ 43382412770783^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566885637 5000000000 43382412770783 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676441167/5000000000 : ℝ), (-340911439/2000000000 : ℝ), (2566885637/5000000000 : ℝ)] ![(22856965079501/50000000000000 : ℝ), (10903657065191/100000000000000 : ℝ), (43382412770783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676441167/5000000000 : ℝ)|^5079 ≤ (22856965079501/50000000000000 : ℝ)^4055
        have hw : |(2676441167/5000000000 : ℝ)|=(2676441167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-340911439/2000000000 : ℝ)|^5079 ≤ (10903657065191/100000000000000 : ℝ)^4055
        have hw : |(-340911439/2000000000 : ℝ)|=(340911439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566885637/5000000000 : ℝ)|^5079 ≤ (43382412770783/100000000000000 : ℝ)^4055
        have hw : |(2566885637/5000000000 : ℝ)|=(2566885637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s3_2 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676441171/5000000000 : ℝ)*x 0 + (205350851/400000000 : ℝ)*x 1 + (-852278591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676441171/5000000000 : ℝ)^5079 ≤ (1828557209783/4000000000000 : ℝ)^4055 := by
    have hnat : (2676441171 : ℕ)^5079*4000000000000^4055 ≤ 1828557209783^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676441171 5000000000 1828557209783 4000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205350851/400000000 : ℝ)^5079 ≤ (43382412781367/100000000000000 : ℝ)^4055 := by
    have hnat : (205350851 : ℕ)^5079*100000000000000^4055 ≤ 43382412781367^4055*400000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205350851 400000000 43382412781367 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (852278591/5000000000 : ℝ)^5079 ≤ (5451828480517/50000000000000 : ℝ)^4055 := by
    have hnat : (852278591 : ℕ)^5079*50000000000000^4055 ≤ 5451828480517^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852278591 5000000000 5451828480517 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676441171/5000000000 : ℝ), (205350851/400000000 : ℝ), (-852278591/5000000000 : ℝ)] ![(1828557209783/4000000000000 : ℝ), (43382412781367/100000000000000 : ℝ), (5451828480517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676441171/5000000000 : ℝ)|^5079 ≤ (1828557209783/4000000000000 : ℝ)^4055
        have hw : |(2676441171/5000000000 : ℝ)|=(2676441171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205350851/400000000 : ℝ)|^5079 ≤ (43382412781367/100000000000000 : ℝ)^4055
        have hw : |(205350851/400000000 : ℝ)|=(205350851/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-852278591/5000000000 : ℝ)|^5079 ≤ (5451828480517/50000000000000 : ℝ)^4055
        have hw : |(-852278591/5000000000 : ℝ)|=(852278591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s3_3 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207117863/500000000 : ℝ)*x 0 + (1839840349/5000000000 : ℝ)*x 1 + (4643269161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207117863/500000000 : ℝ)^5079 ≤ (828956896179/2500000000000 : ℝ)^4055 := by
    have hnat : (207117863 : ℕ)^5079*2500000000000^4055 ≤ 828956896179^4055*500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207117863 500000000 828956896179 2500000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1839840349/5000000000 : ℝ)^5079 ≤ (28586773964917/100000000000000 : ℝ)^4055 := by
    have hnat : (1839840349 : ℕ)^5079*100000000000000^4055 ≤ 28586773964917^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839840349 5000000000 28586773964917 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4643269161/10000000000 : ℝ)^5079 ≤ (9563737543363/25000000000000 : ℝ)^4055 := by
    have hnat : (4643269161 : ℕ)^5079*25000000000000^4055 ≤ 9563737543363^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4643269161 10000000000 9563737543363 25000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207117863/500000000 : ℝ), (1839840349/5000000000 : ℝ), (4643269161/10000000000 : ℝ)] ![(828956896179/2500000000000 : ℝ), (28586773964917/100000000000000 : ℝ), (9563737543363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207117863/500000000 : ℝ)|^5079 ≤ (828956896179/2500000000000 : ℝ)^4055
        have hw : |(207117863/500000000 : ℝ)|=(207117863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1839840349/5000000000 : ℝ)|^5079 ≤ (28586773964917/100000000000000 : ℝ)^4055
        have hw : |(1839840349/5000000000 : ℝ)|=(1839840349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4643269161/10000000000 : ℝ)|^5079 ≤ (9563737543363/25000000000000 : ℝ)^4055
        have hw : |(4643269161/10000000000 : ℝ)|=(4643269161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s3_4 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-760105497/5000000000 : ℝ)*x 0 + (1284401901/2500000000 : ℝ)*x 1 + (548481991/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760105497/5000000000 : ℝ)^5079 ≤ (9447391198203/100000000000000 : ℝ)^4055 := by
    have hnat : (760105497 : ℕ)^5079*100000000000000^4055 ≤ 9447391198203^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760105497 5000000000 9447391198203 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284401901/2500000000 : ℝ)^5079 ≤ (21711510846659/50000000000000 : ℝ)^4055 := by
    have hnat : (1284401901 : ℕ)^5079*50000000000000^4055 ≤ 21711510846659^4055*2500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284401901 2500000000 21711510846659 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548481991/1000000000 : ℝ)^5079 ≤ (23564793546779/50000000000000 : ℝ)^4055 := by
    have hnat : (548481991 : ℕ)^5079*50000000000000^4055 ≤ 23564793546779^4055*1000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548481991 1000000000 23564793546779 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-760105497/5000000000 : ℝ), (1284401901/2500000000 : ℝ), (548481991/1000000000 : ℝ)] ![(9447391198203/100000000000000 : ℝ), (21711510846659/50000000000000 : ℝ), (23564793546779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-760105497/5000000000 : ℝ)|^5079 ≤ (9447391198203/100000000000000 : ℝ)^4055
        have hw : |(-760105497/5000000000 : ℝ)|=(760105497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284401901/2500000000 : ℝ)|^5079 ≤ (21711510846659/50000000000000 : ℝ)^4055
        have hw : |(1284401901/2500000000 : ℝ)|=(1284401901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548481991/1000000000 : ℝ)|^5079 ≤ (23564793546779/50000000000000 : ℝ)^4055
        have hw : |(548481991/1000000000 : ℝ)|=(548481991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s3_5 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328629939/625000000 : ℝ)*x 0 + (-270701749/2000000000 : ℝ)*x 1 + (1096963957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328629939/625000000 : ℝ)^5079 ≤ (22351064557221/50000000000000 : ℝ)^4055 := by
    have hnat : (328629939 : ℕ)^5079*50000000000000^4055 ≤ 22351064557221^4055*625000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328629939 625000000 22351064557221 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270701749/2000000000 : ℝ)^5079 ≤ (1633657024857/20000000000000 : ℝ)^4055 := by
    have hnat : (270701749 : ℕ)^5079*20000000000000^4055 ≤ 1633657024857^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270701749 2000000000 1633657024857 20000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096963957/2000000000 : ℝ)^5079 ≤ (47129585748229/100000000000000 : ℝ)^4055 := by
    have hnat : (1096963957 : ℕ)^5079*100000000000000^4055 ≤ 47129585748229^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096963957 2000000000 47129585748229 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328629939/625000000 : ℝ), (-270701749/2000000000 : ℝ), (1096963957/2000000000 : ℝ)] ![(22351064557221/50000000000000 : ℝ), (1633657024857/20000000000000 : ℝ), (47129585748229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328629939/625000000 : ℝ)|^5079 ≤ (22351064557221/50000000000000 : ℝ)^4055
        have hw : |(328629939/625000000 : ℝ)|=(328629939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-270701749/2000000000 : ℝ)|^5079 ≤ (1633657024857/20000000000000 : ℝ)^4055
        have hw : |(-270701749/2000000000 : ℝ)|=(270701749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096963957/2000000000 : ℝ)|^5079 ≤ (47129585748229/100000000000000 : ℝ)^4055
        have hw : |(1096963957/2000000000 : ℝ)|=(1096963957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s3_6 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051615817/2000000000 : ℝ)*x 0 + (5484819819/10000000000 : ℝ)*x 1 + (-1353508611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051615817/2000000000 : ℝ)^5079 ≤ (11175532441/25000000000 : ℝ)^4055 := by
    have hnat : (1051615817 : ℕ)^5079*25000000000^4055 ≤ 11175532441^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051615817 2000000000 11175532441 25000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5484819819/10000000000 : ℝ)^5079 ≤ (47129586114159/100000000000000 : ℝ)^4055 := by
    have hnat : (5484819819 : ℕ)^5079*100000000000000^4055 ≤ 47129586114159^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484819819 10000000000 47129586114159 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353508611/10000000000 : ℝ)^5079 ≤ (2042071027849/25000000000000 : ℝ)^4055 := by
    have hnat : (1353508611 : ℕ)^5079*25000000000000^4055 ≤ 2042071027849^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353508611 10000000000 2042071027849 25000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051615817/2000000000 : ℝ), (5484819819/10000000000 : ℝ), (-1353508611/10000000000 : ℝ)] ![(11175532441/25000000000 : ℝ), (47129586114159/100000000000000 : ℝ), (2042071027849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051615817/2000000000 : ℝ)|^5079 ≤ (11175532441/25000000000 : ℝ)^4055
        have hw : |(1051615817/2000000000 : ℝ)|=(1051615817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5484819819/10000000000 : ℝ)|^5079 ≤ (47129586114159/100000000000000 : ℝ)^4055
        have hw : |(5484819819/10000000000 : ℝ)|=(5484819819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1353508611/10000000000 : ℝ)|^5079 ≤ (2042071027849/25000000000000 : ℝ)^4055
        have hw : |(-1353508611/10000000000 : ℝ)|=(1353508611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s3_7 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4142811217/10000000000 : ℝ)*x 0 + (2316427191/5000000000 : ℝ)*x 1 + (57660169/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4142811217/10000000000 : ℝ)^5079 ≤ (33162827325379/100000000000000 : ℝ)^4055 := by
    have hnat : (4142811217 : ℕ)^5079*100000000000000^4055 ≤ 33162827325379^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142811217 10000000000 33162827325379 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2316427191/5000000000 : ℝ)^5079 ≤ (38147507176891/100000000000000 : ℝ)^4055 := by
    have hnat : (2316427191 : ℕ)^5079*100000000000000^4055 ≤ 38147507176891^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316427191 5000000000 38147507176891 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57660169/156250000 : ℝ)^5079 ≤ (14344832742203/50000000000000 : ℝ)^4055 := by
    have hnat : (57660169 : ℕ)^5079*50000000000000^4055 ≤ 14344832742203^4055*156250000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57660169 156250000 14344832742203 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4142811217/10000000000 : ℝ), (2316427191/5000000000 : ℝ), (57660169/156250000 : ℝ)] ![(33162827325379/100000000000000 : ℝ), (38147507176891/100000000000000 : ℝ), (14344832742203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4142811217/10000000000 : ℝ)|^5079 ≤ (33162827325379/100000000000000 : ℝ)^4055
        have hw : |(4142811217/10000000000 : ℝ)|=(4142811217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2316427191/5000000000 : ℝ)|^5079 ≤ (38147507176891/100000000000000 : ℝ)^4055
        have hw : |(2316427191/5000000000 : ℝ)|=(2316427191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(57660169/156250000 : ℝ)|^5079 ≤ (14344832742203/50000000000000 : ℝ)^4055
        have hw : |(57660169/156250000 : ℝ)|=(57660169/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1682_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (23217349/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8661/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9721/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9747/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4323/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8661/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9721/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8661/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9721/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8661/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9721/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8661/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9721/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8661/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9721/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8661/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9721/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9721/100000 : ℝ) ^ (5071/1024 : ℝ) ≤ (485248646915979/50000000000000000000 : ℝ) := by
    have hpowers : (9721/100000 : ℝ)^5071 ≤ (485248646915979/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9721 : ℕ)^5071*50000000000000000000^1024 ≤ 485248646915979^1024*100000^5071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9721 100000 485248646915979 50000000000000000000 5071 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9721/100000 : ℝ)) (X := (485248646915979/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8661/50000 : ℝ) ^ (5071/1024 : ℝ) ≤ (16959945216294133/100000000000000000000 : ℝ) := by
    have hpowers : (8661/50000 : ℝ)^5071 ≤ (16959945216294133/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8661 : ℕ)^5071*100000000000000000000^1024 ≤ 16959945216294133^1024*50000^5071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8661 50000 16959945216294133 100000000000000000000 5071 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8661/50000 : ℝ)) (X := (16959945216294133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000485248646915979/25000000000000000000 : ℝ) ≤ (10000039194696583/10000000000000000 : ℝ) ^ (5071/1024 : ℝ) := by
    have hpowers : (25000485248646915979/25000000000000000000 : ℝ)^1024 ≤ (10000039194696583/10000000000000000 : ℝ)^5071 := by
      have hnat : (25000485248646915979 : ℕ)^1024*10000000000000000^5071 ≤ 10000039194696583^5071*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000485248646915979 25000000000000000000 10000039194696583 10000000000000000 1024 5071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000039194696583/10000000000000000 : ℝ)) (X := (25000485248646915979/25000000000000000000 : ℝ)) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017930442510126091/100000000000000000000 : ℝ) ≤ (10000362048108569/10000000000000000 : ℝ) ^ (5071/1024 : ℝ) := by
    have hpowers : (100017930442510126091/100000000000000000000 : ℝ)^1024 ≤ (10000362048108569/10000000000000000 : ℝ)^5071 := by
      have hnat : (100017930442510126091 : ℕ)^1024*10000000000000000^5071 ≤ 10000362048108569^5071*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017930442510126091 100000000000000000000 10000362048108569 10000000000000000 1024 5071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000362048108569/10000000000000000 : ℝ)) (X := (100017930442510126091/100000000000000000000 : ℝ)) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016959945216294133/50000000000000000000 : ℝ) ≤ (2000136980304111/2000000000000000 : ℝ) ^ (5071/1024 : ℝ) := by
    have hpowers : (50016959945216294133/50000000000000000000 : ℝ)^1024 ≤ (2000136980304111/2000000000000000 : ℝ)^5071 := by
      have hnat : (50016959945216294133 : ℕ)^1024*2000000000000000^5071 ≤ 2000136980304111^5071*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016959945216294133 50000000000000000000 2000136980304111 2000000000000000 1024 5071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000136980304111/2000000000000000 : ℝ)) (X := (50016959945216294133/50000000000000000000 : ℝ)) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(485248646915979/50000000000000000000 : ℝ) ≤ ((76004021002852895571/76010000000000000000 : ℝ)+2*(161426705993/380050000000000 : ℝ)*(9721/100000 : ℝ))^(5071/1024 : ℝ) := by
    rw [show (76004021002852895571/76010000000000000000 : ℝ)+2*(161426705993/380050000000000 : ℝ)*(9721/100000 : ℝ)=(10000039194696583/10000000000000000 : ℝ) by norm_num, show 1+2*(485248646915979/50000000000000000000 : ℝ)=(25000485248646915979/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16959945216294133/100000000000000000000 : ℝ)+(485248646915979/50000000000000000000 : ℝ) ≤ ((76004021002852895571/76010000000000000000 : ℝ)+(161426705993/380050000000000 : ℝ)*((8661/50000 : ℝ)+(9721/100000 : ℝ)))^(5071/1024 : ℝ) := by
    rw [show (76004021002852895571/76010000000000000000 : ℝ)+(161426705993/380050000000000 : ℝ)*((8661/50000 : ℝ)+(9721/100000 : ℝ))=(10000362048108569/10000000000000000 : ℝ) by norm_num, show 1+(16959945216294133/100000000000000000000 : ℝ)+(485248646915979/50000000000000000000 : ℝ)=(100017930442510126091/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16959945216294133/100000000000000000000 : ℝ) ≤ ((76004021002852895571/76010000000000000000 : ℝ)+2*(161426705993/380050000000000 : ℝ)*(8661/50000 : ℝ))^(5071/1024 : ℝ) := by
    rw [show (76004021002852895571/76010000000000000000 : ℝ)+2*(161426705993/380050000000000 : ℝ)*(8661/50000 : ℝ)=(2000136980304111/2000000000000000 : ℝ) by norm_num, show 1+2*(16959945216294133/100000000000000000000 : ℝ)=(50016959945216294133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (76004021002852895571/76010000000000000000 : ℝ)*(X 1 0+X 2 0)+(161426705993/380050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5071/1024 : ℝ)) (lo := (9721/100000 : ℝ)) (hi := (8661/50000 : ℝ)) (c := (76004021002852895571/76010000000000000000 : ℝ)) (alpha := (161426705993/380050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (76004021002852895571/76010000000000000000 : ℝ)*(X 0 1+X 2 1)+(161426705993/380050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5071/1024 : ℝ)) (lo := (9721/100000 : ℝ)) (hi := (8661/50000 : ℝ)) (c := (76004021002852895571/76010000000000000000 : ℝ)) (alpha := (161426705993/380050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (76004021002852895571/76010000000000000000 : ℝ)*(X 0 2+X 1 2)+(161426705993/380050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5071/1024 : ℝ)) (lo := (9721/100000 : ℝ)) (hi := (8661/50000 : ℝ)) (c := (76004021002852895571/76010000000000000000 : ℝ)) (alpha := (161426705993/380050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-760022003/5000000000 : ℝ)*X 0 0+(5488713359/10000000000 : ℝ)*X 0 1+(5133771387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676441167/5000000000 : ℝ)*X 1 0+(-340911439/2000000000 : ℝ)*X 1 1+(2566885637/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676441171/5000000000 : ℝ)*X 2 0+(205350851/400000000 : ℝ)*X 2 1+(-852278591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((207117863/500000000 : ℝ)*X 0 0+(1839840349/5000000000 : ℝ)*X 0 1+(4643269161/10000000000 : ℝ)*X 0 2+(207117863/500000000 : ℝ)*X 1 0+(1839840349/5000000000 : ℝ)*X 1 1+(4643269161/10000000000 : ℝ)*X 1 2+(207117863/500000000 : ℝ)*X 2 0+(1839840349/5000000000 : ℝ)*X 2 1+(4643269161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-760105497/5000000000 : ℝ)*X 0 0+(1284401901/2500000000 : ℝ)*X 0 1+(548481991/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328629939/625000000 : ℝ)*X 1 0+(-270701749/2000000000 : ℝ)*X 1 1+(1096963957/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051615817/2000000000 : ℝ)*X 2 0+(5484819819/10000000000 : ℝ)*X 2 1+(-1353508611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4142811217/10000000000 : ℝ)*X 0 0+(2316427191/5000000000 : ℝ)*X 0 1+(57660169/156250000 : ℝ)*X 0 2+(4142811217/10000000000 : ℝ)*X 1 0+(2316427191/5000000000 : ℝ)*X 1 1+(57660169/156250000 : ℝ)*X 1 2+(4142811217/10000000000 : ℝ)*X 2 0+(2316427191/5000000000 : ℝ)*X 2 1+(57660169/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19339792446959908378224423759/3800500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39854689/5000000000000 : ℝ)*(base19) + (152147027/20000000000000 : ℝ)*(base23) + (10858127/50000000000000 : ℝ)*(lower2) + (123529687/100000000000000 : ℝ)*(upper3) + (20391579/20000000000000 : ℝ)*(upper5) + (1927584153192743/100000000000000 : ℝ)*(major0) + (1927584153192743/100000000000000 : ℝ)*(major1) + (1927584153192743/100000000000000 : ℝ)*(major2) + (1408684264278697/50000000000000 : ℝ)*(sp0) + (35217179437419/1250000000000 : ℝ)*(sp1) + (563474878270433/20000000000000 : ℝ)*(sp2) + (51889503986441/5000000000000 : ℝ)*(sp3) + (6623529907/100000000000000 : ℝ)*(sp4) + (1452472189/50000000000000 : ℝ)*(sp7) + (518896492336599/50000000000000 : ℝ)*(f.failure) + (28173751520873/1000000000000 : ℝ)*(f.sum) + (70878530175461/19002500000000000000000000000 : ℝ)*base66 + (15921154055743841253/7601000000000000000000000000000000 : ℝ)*base67 + (76074100764142158747/7601000000000000000000000000000000 : ℝ)*base70 + (10041405878732158747/7601000000000000000000000000000000 : ℝ)*base72 + (73432895683909/19002500000000000000000000000 : ℝ)*base73 + (10200875177974158747/7601000000000000000000000000000000 : ℝ)*base76 + (37705205473482158747/7601000000000000000000000000000000 : ℝ)*base78 + (45447838267042841253/7601000000000000000000000000000000 : ℝ)*base79 + (22205125799199/4750625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (706051/625000000000000000000 : ℝ)*base89 + (706051/625000000000000000000 : ℝ)*base91 + (706051/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10383824704287262613583999711/1900250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84740399/12500000000000 : ℝ)*(base19) + (46443323/5000000000000 : ℝ)*(base23) + (152683809/100000000000000 : ℝ)*(lower1) + (29352441/25000000000000 : ℝ)*(upper3) + (89499251/100000000000000 : ℝ)*(lower4) + (15083971/12500000000000 : ℝ)*(upper5) + (985241689596553/50000000000000 : ℝ)*(major0) + (985241689596553/50000000000000 : ℝ)*(major1) + (985241689596553/50000000000000 : ℝ)*(major2) + (1312203783/50000000000000 : ℝ)*(sp2) + (14400385280407/500000000000 : ℝ)*(sp4) + (22500596704361/781250000000 : ℝ)*(sp5) + (1440036751403687/50000000000000 : ℝ)*(sp6) + (530444760078203/50000000000000 : ℝ)*(sp7) + (530444760078203/50000000000000 : ℝ)*(f.failure) + (14400385280407/500000000000 : ℝ)*(f.sum) + (27798408210003/19002500000000000000000000000 : ℝ)*base65 + (3124180736689633237/3800500000000000000000000000000000 : ℝ)*base68 + (13549887435808366763/3800500000000000000000000000000000 : ℝ)*base69 + (44025968486509366763/3800500000000000000000000000000000 : ℝ)*base71 + (696490912173/296914062500000000000000000 : ℝ)*base74 + (69292922363831633237/3800500000000000000000000000000000 : ℝ)*base76 + (24918789908824366763/3800500000000000000000000000000000 : ℝ)*base77 + (3735545587332366763/3800500000000000000000000000000000 : ℝ)*base79 + (34390446377333/19002500000000000000000000000 : ℝ)*base81 + (6156153/625000000000000000000 : ℝ)*base90 + (6156153/625000000000000000000 : ℝ)*base92 + (6156153/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1682_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (23217349/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8661/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9721/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9747/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4323/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1682_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1682_s4_0 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1520063601/10000000000 : ℝ)*x 0 + (2744318967/5000000000 : ℝ)*x 1 + (1026766737/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1520063601/10000000000 : ℝ)^5079 ≤ (9446243924799/100000000000000 : ℝ)^4055 := by
    have hnat : (1520063601 : ℕ)^5079*100000000000000^4055 ≤ 9446243924799^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1520063601 10000000000 9446243924799 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744318967/5000000000 : ℝ)^5079 ≤ (23585341351911/50000000000000 : ℝ)^4055 := by
    have hnat : (2744318967 : ℕ)^5079*50000000000000^4055 ≤ 23585341351911^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744318967 5000000000 23585341351911 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026766737/2000000000 : ℝ)^5079 ≤ (21691536676097/50000000000000 : ℝ)^4055 := by
    have hnat : (1026766737 : ℕ)^5079*50000000000000^4055 ≤ 21691536676097^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026766737 2000000000 21691536676097 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1520063601/10000000000 : ℝ), (2744318967/5000000000 : ℝ), (1026766737/2000000000 : ℝ)] ![(9446243924799/100000000000000 : ℝ), (23585341351911/50000000000000 : ℝ), (21691536676097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1520063601/10000000000 : ℝ)|^5079 ≤ (9446243924799/100000000000000 : ℝ)^4055
        have hw : |(-1520063601/10000000000 : ℝ)|=(1520063601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744318967/5000000000 : ℝ)|^5079 ≤ (23585341351911/50000000000000 : ℝ)^4055
        have hw : |(2744318967/5000000000 : ℝ)|=(2744318967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026766737/2000000000 : ℝ)|^5079 ≤ (21691536676097/50000000000000 : ℝ)^4055
        have hw : |(1026766737/2000000000 : ℝ)|=(1026766737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s4_1 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352862073/10000000000 : ℝ)*x 0 + (-340900553/2000000000 : ℝ)*x 1 + (5133832951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352862073/10000000000 : ℝ)^5079 ≤ (2857107089629/6250000000000 : ℝ)^4055 := by
    have hnat : (5352862073 : ℕ)^5079*6250000000000^4055 ≤ 2857107089629^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352862073 10000000000 2857107089629 6250000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340900553/2000000000 : ℝ)^5079 ≤ (10903220966741/100000000000000 : ℝ)^4055 := by
    have hnat : (340900553 : ℕ)^5079*100000000000000^4055 ≤ 10903220966741^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340900553 2000000000 10903220966741 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133832951/10000000000 : ℝ)^5079 ≤ (43383065583251/100000000000000 : ℝ)^4055 := by
    have hnat : (5133832951 : ℕ)^5079*100000000000000^4055 ≤ 43383065583251^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133832951 10000000000 43383065583251 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352862073/10000000000 : ℝ), (-340900553/2000000000 : ℝ), (5133832951/10000000000 : ℝ)] ![(2857107089629/6250000000000 : ℝ), (10903220966741/100000000000000 : ℝ), (43383065583251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352862073/10000000000 : ℝ)|^5079 ≤ (2857107089629/6250000000000 : ℝ)^4055
        have hw : |(5352862073/10000000000 : ℝ)|=(5352862073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-340900553/2000000000 : ℝ)|^5079 ≤ (10903220966741/100000000000000 : ℝ)^4055
        have hw : |(-340900553/2000000000 : ℝ)|=(340900553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133832951/10000000000 : ℝ)|^5079 ≤ (43383065583251/100000000000000 : ℝ)^4055
        have hw : |(5133832951/10000000000 : ℝ)|=(5133832951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s4_2 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352861289/10000000000 : ℝ)*x 0 + (1283458417/2500000000 : ℝ)*x 1 + (-340900573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352861289/10000000000 : ℝ)^5079 ≤ (45713705047891/100000000000000 : ℝ)^4055 := by
    have hnat : (5352861289 : ℕ)^5079*100000000000000^4055 ≤ 45713705047891^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352861289 10000000000 45713705047891 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283458417/2500000000 : ℝ)^5079 ≤ (2169153658613/5000000000000 : ℝ)^4055 := by
    have hnat : (1283458417 : ℕ)^5079*5000000000000^4055 ≤ 2169153658613^4055*2500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283458417 2500000000 2169153658613 5000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340900573/2000000000 : ℝ)^5079 ≤ (2725805441987/25000000000000 : ℝ)^4055 := by
    have hnat : (340900573 : ℕ)^5079*25000000000000^4055 ≤ 2725805441987^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340900573 2000000000 2725805441987 25000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352861289/10000000000 : ℝ), (1283458417/2500000000 : ℝ), (-340900573/2000000000 : ℝ)] ![(45713705047891/100000000000000 : ℝ), (2169153658613/5000000000000 : ℝ), (2725805441987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352861289/10000000000 : ℝ)|^5079 ≤ (45713705047891/100000000000000 : ℝ)^4055
        have hw : |(5352861289/10000000000 : ℝ)|=(5352861289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283458417/2500000000 : ℝ)|^5079 ≤ (2169153658613/5000000000000 : ℝ)^4055
        have hw : |(1283458417/2500000000 : ℝ)|=(1283458417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-340900573/2000000000 : ℝ)|^5079 ≤ (2725805441987/25000000000000 : ℝ)^4055
        have hw : |(-340900573/2000000000 : ℝ)|=(340900573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s4_3 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4142370877/10000000000 : ℝ)*x 0 + (919966581/2500000000 : ℝ)*x 1 + (4643080891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4142370877/10000000000 : ℝ)^5079 ≤ (33158412372529/100000000000000 : ℝ)^4055 := by
    have hnat : (4142370877 : ℕ)^5079*100000000000000^4055 ≤ 33158412372529^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142370877 10000000000 33158412372529 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (919966581/2500000000 : ℝ)^5079 ≤ (28588580240203/100000000000000 : ℝ)^4055 := by
    have hnat : (919966581 : ℕ)^5079*100000000000000^4055 ≤ 28588580240203^4055*2500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919966581 2500000000 28588580240203 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4643080891/10000000000 : ℝ)^5079 ≤ (1530120294591/4000000000000 : ℝ)^4055 := by
    have hnat : (4643080891 : ℕ)^5079*4000000000000^4055 ≤ 1530120294591^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4643080891 10000000000 1530120294591 4000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4142370877/10000000000 : ℝ), (919966581/2500000000 : ℝ), (4643080891/10000000000 : ℝ)] ![(33158412372529/100000000000000 : ℝ), (28588580240203/100000000000000 : ℝ), (1530120294591/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4142370877/10000000000 : ℝ)|^5079 ≤ (33158412372529/100000000000000 : ℝ)^4055
        have hw : |(4142370877/10000000000 : ℝ)|=(4142370877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(919966581/2500000000 : ℝ)|^5079 ≤ (28588580240203/100000000000000 : ℝ)^4055
        have hw : |(919966581/2500000000 : ℝ)|=(919966581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4643080891/10000000000 : ℝ)|^5079 ≤ (1530120294591/4000000000000 : ℝ)^4055
        have hw : |(4643080891/10000000000 : ℝ)|=(4643080891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s4_4 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-760115279/5000000000 : ℝ)*x 0 + (1027533361/2000000000 : ℝ)*x 1 + (5484747529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760115279/5000000000 : ℝ)^5079 ≤ (9447543482017/100000000000000 : ℝ)^4055 := by
    have hnat : (760115279 : ℕ)^5079*100000000000000^4055 ≤ 9447543482017^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760115279 5000000000 9447543482017 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027533361/2000000000 : ℝ)^5079 ≤ (5427956052131/12500000000000 : ℝ)^4055 := by
    have hnat : (1027533361 : ℕ)^5079*12500000000000^4055 ≤ 5427956052131^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027533361 2000000000 5427956052131 12500000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484747529/10000000000 : ℝ)^5079 ≤ (11782202021141/25000000000000 : ℝ)^4055 := by
    have hnat : (5484747529 : ℕ)^5079*25000000000000^4055 ≤ 11782202021141^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484747529 10000000000 11782202021141 25000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-760115279/5000000000 : ℝ), (1027533361/2000000000 : ℝ), (5484747529/10000000000 : ℝ)] ![(9447543482017/100000000000000 : ℝ), (5427956052131/12500000000000 : ℝ), (11782202021141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-760115279/5000000000 : ℝ)|^5079 ≤ (9447543482017/100000000000000 : ℝ)^4055
        have hw : |(-760115279/5000000000 : ℝ)|=(760115279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027533361/2000000000 : ℝ)|^5079 ≤ (5427956052131/12500000000000 : ℝ)^4055
        have hw : |(1027533361/2000000000 : ℝ)|=(1027533361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484747529/10000000000 : ℝ)|^5079 ≤ (11782202021141/25000000000000 : ℝ)^4055
        have hw : |(5484747529/10000000000 : ℝ)|=(5484747529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s4_5 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258095407/10000000000 : ℝ)*x 0 + (-1353588543/10000000000 : ℝ)*x 1 + (5484747531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258095407/10000000000 : ℝ)^5079 ≤ (44702303568893/100000000000000 : ℝ)^4055 := by
    have hnat : (5258095407 : ℕ)^5079*100000000000000^4055 ≤ 44702303568893^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258095407 10000000000 44702303568893 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353588543/10000000000 : ℝ)^5079 ≤ (8168888311901/100000000000000 : ℝ)^4055 := by
    have hnat : (1353588543 : ℕ)^5079*100000000000000^4055 ≤ 8168888311901^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353588543 10000000000 8168888311901 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484747531/10000000000 : ℝ)^5079 ≤ (47128808106089/100000000000000 : ℝ)^4055 := by
    have hnat : (5484747531 : ℕ)^5079*100000000000000^4055 ≤ 47128808106089^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484747531 10000000000 47128808106089 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258095407/10000000000 : ℝ), (-1353588543/10000000000 : ℝ), (5484747531/10000000000 : ℝ)] ![(44702303568893/100000000000000 : ℝ), (8168888311901/100000000000000 : ℝ), (47128808106089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258095407/10000000000 : ℝ)|^5079 ≤ (44702303568893/100000000000000 : ℝ)^4055
        have hw : |(5258095407/10000000000 : ℝ)|=(5258095407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1353588543/10000000000 : ℝ)|^5079 ≤ (8168888311901/100000000000000 : ℝ)^4055
        have hw : |(-1353588543/10000000000 : ℝ)|=(1353588543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484747531/10000000000 : ℝ)|^5079 ≤ (47128808106089/100000000000000 : ℝ)^4055
        have hw : |(5484747531/10000000000 : ℝ)|=(5484747531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s4_6 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629047703/5000000000 : ℝ)*x 0 + (1371186883/2500000000 : ℝ)*x 1 + (-1353588543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629047703/5000000000 : ℝ)^5079 ≤ (8940460711649/20000000000000 : ℝ)^4055 := by
    have hnat : (2629047703 : ℕ)^5079*20000000000000^4055 ≤ 8940460711649^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629047703 5000000000 8940460711649 20000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371186883/2500000000 : ℝ)^5079 ≤ (11782202029213/25000000000000 : ℝ)^4055 := by
    have hnat : (1371186883 : ℕ)^5079*25000000000000^4055 ≤ 11782202029213^4055*2500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371186883 2500000000 11782202029213 25000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353588543/10000000000 : ℝ)^5079 ≤ (8168888311901/100000000000000 : ℝ)^4055 := by
    have hnat : (1353588543 : ℕ)^5079*100000000000000^4055 ≤ 8168888311901^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353588543 10000000000 8168888311901 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629047703/5000000000 : ℝ), (1371186883/2500000000 : ℝ), (-1353588543/10000000000 : ℝ)] ![(8940460711649/20000000000000 : ℝ), (11782202029213/25000000000000 : ℝ), (8168888311901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629047703/5000000000 : ℝ)|^5079 ≤ (8940460711649/20000000000000 : ℝ)^4055
        have hw : |(2629047703/5000000000 : ℝ)|=(2629047703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371186883/2500000000 : ℝ)|^5079 ≤ (11782202029213/25000000000000 : ℝ)^4055
        have hw : |(1371186883/2500000000 : ℝ)|=(1371186883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1353588543/10000000000 : ℝ)|^5079 ≤ (8168888311901/100000000000000 : ℝ)^4055
        have hw : |(-1353588543/10000000000 : ℝ)|=(1353588543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_s4_7 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4142823917/10000000000 : ℝ)*x 0 + (4632674559/10000000000 : ℝ)*x 1 + (115325881/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4142823917/10000000000 : ℝ)^5079 ≤ (33162954660337/100000000000000 : ℝ)^4055 := by
    have hnat : (4142823917 : ℕ)^5079*100000000000000^4055 ≤ 33162954660337^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142823917 10000000000 33162954660337 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4632674559/10000000000 : ℝ)^5079 ≤ (7629130517323/20000000000000 : ℝ)^4055 := by
    have hnat : (4632674559 : ℕ)^5079*20000000000000^4055 ≤ 7629130517323^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4632674559 10000000000 7629130517323 20000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115325881/312500000 : ℝ)^5079 ≤ (28691392731403/100000000000000 : ℝ)^4055 := by
    have hnat : (115325881 : ℕ)^5079*100000000000000^4055 ≤ 28691392731403^4055*312500000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115325881 312500000 28691392731403 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4142823917/10000000000 : ℝ), (4632674559/10000000000 : ℝ), (115325881/312500000 : ℝ)] ![(33162954660337/100000000000000 : ℝ), (7629130517323/20000000000000 : ℝ), (28691392731403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4142823917/10000000000 : ℝ)|^5079 ≤ (33162954660337/100000000000000 : ℝ)^4055
        have hw : |(4142823917/10000000000 : ℝ)|=(4142823917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4632674559/10000000000 : ℝ)|^5079 ≤ (7629130517323/20000000000000 : ℝ)^4055
        have hw : |(4632674559/10000000000 : ℝ)|=(4632674559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(115325881/312500000 : ℝ)|^5079 ≤ (28691392731403/100000000000000 : ℝ)^4055
        have hw : |(115325881/312500000 : ℝ)|=(115325881/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1682_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (23217349/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4323/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9747/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2437/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17291/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4323/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9747/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4323/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9747/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4323/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9747/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4323/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9747/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4323/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9747/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4323/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9747/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9747/100000 : ℝ) ^ (5071/1024 : ℝ) ≤ (491709884642599/50000000000000000000 : ℝ) := by
    have hpowers : (9747/100000 : ℝ)^5071 ≤ (491709884642599/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9747 : ℕ)^5071*50000000000000000000^1024 ≤ 491709884642599^1024*100000^5071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9747 100000 491709884642599 50000000000000000000 5071 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9747/100000 : ℝ)) (X := (491709884642599/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4323/25000 : ℝ) ^ (5071/1024 : ℝ) ≤ (4203745735401097/25000000000000000000 : ℝ) := by
    have hpowers : (4323/25000 : ℝ)^5071 ≤ (4203745735401097/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4323 : ℕ)^5071*25000000000000000000^1024 ≤ 4203745735401097^1024*25000^5071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4323 25000 4203745735401097 25000000000000000000 5071 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4323/25000 : ℝ)) (X := (4203745735401097/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000491709884642599/25000000000000000000 : ℝ) ≤ (10000039716582149/10000000000000000 : ℝ) ^ (5071/1024 : ℝ) := by
    have hpowers : (25000491709884642599/25000000000000000000 : ℝ)^1024 ≤ (10000039716582149/10000000000000000 : ℝ)^5071 := by
      have hnat : (25000491709884642599 : ℕ)^1024*10000000000000000^5071 ≤ 10000039716582149^5071*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000491709884642599 25000000000000000000 10000039716582149 10000000000000000 1024 5071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000039716582149/10000000000000000 : ℝ)) (X := (25000491709884642599/25000000000000000000 : ℝ)) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50008899201355444793/50000000000000000000 : ℝ) ≤ (1250044922771901/1250000000000000 : ℝ) ^ (5071/1024 : ℝ) := by
    have hpowers : (50008899201355444793/50000000000000000000 : ℝ)^1024 ≤ (1250044922771901/1250000000000000 : ℝ)^5071 := by
      have hnat : (50008899201355444793 : ℕ)^1024*1250000000000000^5071 ≤ 1250044922771901^5071*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008899201355444793 50000000000000000000 1250044922771901 1250000000000000 1024 5071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250044922771901/1250000000000000 : ℝ)) (X := (50008899201355444793/50000000000000000000 : ℝ)) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504203745735401097/12500000000000000000 : ℝ) ≤ (10000679047768267/10000000000000000 : ℝ) ^ (5071/1024 : ℝ) := by
    have hpowers : (12504203745735401097/12500000000000000000 : ℝ)^1024 ≤ (10000679047768267/10000000000000000 : ℝ)^5071 := by
      have hnat : (12504203745735401097 : ℕ)^1024*10000000000000000^5071 ≤ 10000679047768267^5071*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504203745735401097 12500000000000000000 10000679047768267 10000000000000000 1024 5071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000679047768267/10000000000000000 : ℝ)) (X := (12504203745735401097/12500000000000000000 : ℝ)) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(491709884642599/50000000000000000000 : ℝ) ≤ ((25148022700180407353/25150000000000000000 : ℝ)+2*(319665593059/754500000000000 : ℝ)*(9747/100000 : ℝ))^(5071/1024 : ℝ) := by
    rw [show (25148022700180407353/25150000000000000000 : ℝ)+2*(319665593059/754500000000000 : ℝ)*(9747/100000 : ℝ)=(10000039716582149/10000000000000000 : ℝ) by norm_num, show 1+2*(491709884642599/50000000000000000000 : ℝ)=(25000491709884642599/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4203745735401097/25000000000000000000 : ℝ)+(491709884642599/50000000000000000000 : ℝ) ≤ ((25148022700180407353/25150000000000000000 : ℝ)+(319665593059/754500000000000 : ℝ)*((4323/25000 : ℝ)+(9747/100000 : ℝ)))^(5071/1024 : ℝ) := by
    rw [show (25148022700180407353/25150000000000000000 : ℝ)+(319665593059/754500000000000 : ℝ)*((4323/25000 : ℝ)+(9747/100000 : ℝ))=(1250044922771901/1250000000000000 : ℝ) by norm_num, show 1+(4203745735401097/25000000000000000000 : ℝ)+(491709884642599/50000000000000000000 : ℝ)=(50008899201355444793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4203745735401097/25000000000000000000 : ℝ) ≤ ((25148022700180407353/25150000000000000000 : ℝ)+2*(319665593059/754500000000000 : ℝ)*(4323/25000 : ℝ))^(5071/1024 : ℝ) := by
    rw [show (25148022700180407353/25150000000000000000 : ℝ)+2*(319665593059/754500000000000 : ℝ)*(4323/25000 : ℝ)=(10000679047768267/10000000000000000 : ℝ) by norm_num, show 1+2*(4203745735401097/25000000000000000000 : ℝ)=(12504203745735401097/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25148022700180407353/25150000000000000000 : ℝ)*(X 1 0+X 2 0)+(319665593059/754500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5071/1024 : ℝ)) (lo := (9747/100000 : ℝ)) (hi := (4323/25000 : ℝ)) (c := (25148022700180407353/25150000000000000000 : ℝ)) (alpha := (319665593059/754500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25148022700180407353/25150000000000000000 : ℝ)*(X 0 1+X 2 1)+(319665593059/754500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5071/1024 : ℝ)) (lo := (9747/100000 : ℝ)) (hi := (4323/25000 : ℝ)) (c := (25148022700180407353/25150000000000000000 : ℝ)) (alpha := (319665593059/754500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25148022700180407353/25150000000000000000 : ℝ)*(X 0 2+X 1 2)+(319665593059/754500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5071/1024 : ℝ)) (lo := (9747/100000 : ℝ)) (hi := (4323/25000 : ℝ)) (c := (25148022700180407353/25150000000000000000 : ℝ)) (alpha := (319665593059/754500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1520063601/10000000000 : ℝ)*X 0 0+(2744318967/5000000000 : ℝ)*X 0 1+(1026766737/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352862073/10000000000 : ℝ)*X 1 0+(-340900553/2000000000 : ℝ)*X 1 1+(5133832951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352861289/10000000000 : ℝ)*X 2 0+(1283458417/2500000000 : ℝ)*X 2 1+(-340900573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4142370877/10000000000 : ℝ)*X 0 0+(919966581/2500000000 : ℝ)*X 0 1+(4643080891/10000000000 : ℝ)*X 0 2+(4142370877/10000000000 : ℝ)*X 1 0+(919966581/2500000000 : ℝ)*X 1 1+(4643080891/10000000000 : ℝ)*X 1 2+(4142370877/10000000000 : ℝ)*X 2 0+(919966581/2500000000 : ℝ)*X 2 1+(4643080891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-760115279/5000000000 : ℝ)*X 0 0+(1027533361/2000000000 : ℝ)*X 0 1+(5484747529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258095407/10000000000 : ℝ)*X 1 0+(-1353588543/10000000000 : ℝ)*X 1 1+(5484747531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2629047703/5000000000 : ℝ)*X 2 0+(1371186883/2500000000 : ℝ)*X 2 1+(-1353588543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4142823917/10000000000 : ℝ)*X 0 0+(4632674559/10000000000 : ℝ)*X 0 1+(115325881/312500000 : ℝ)*X 0 2+(4142823917/10000000000 : ℝ)*X 1 0+(4632674559/10000000000 : ℝ)*X 1 1+(115325881/312500000 : ℝ)*X 1 2+(4142823917/10000000000 : ℝ)*X 2 0+(4632674559/10000000000 : ℝ)*X 2 1+(115325881/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11523865063739468381883611551/1257500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (398387213/25000000000000 : ℝ)*(base19) + (1050596203/100000000000000 : ℝ)*(base23) + (8708339/12500000000000 : ℝ)*(lower2) + (149883297/50000000000000 : ℝ)*(upper3) + (86889961/100000000000000 : ℝ)*(upper5) + (1928336695326211/100000000000000 : ℝ)*(major0) + (1928336695326211/100000000000000 : ℝ)*(major1) + (1928336695326211/100000000000000 : ℝ)*(major2) + (1409233639420081/50000000000000 : ℝ)*(sp0) + (2818473345429041/100000000000000 : ℝ)*(sp1) + (281847388838169/10000000000000 : ℝ)*(sp2) + (519096842851481/50000000000000 : ℝ)*(sp3) + (1915034433/25000000000000 : ℝ)*(sp4) + (4460501311/100000000000000 : ℝ)*(sp7) + (1038198146204273/100000000000000 : ℝ)*(f.failure) + (1409237469488947/50000000000000 : ℝ)*(f.sum) + (29847813936137/18862500000000000000000000000 : ℝ)*base65 + (28787724702313988449/7545000000000000000000000000000000 : ℝ)*base67 + (43908274447801011551/7545000000000000000000000000000000 : ℝ)*base70 + (13729593328891011551/7545000000000000000000000000000000 : ℝ)*base72 + (216738573380749/37725000000000000000000000000 : ℝ)*base73 + (53233534209013988449/7545000000000000000000000000000000 : ℝ)*base75 + (33232475404843988449/7545000000000000000000000000000000 : ℝ)*base77 + (43451829431473988449/7545000000000000000000000000000000 : ℝ)*base79 + (48174556606451/37725000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5967723/1250000000000000000000 : ℝ)*base90 + (5967723/1250000000000000000000 : ℝ)*base92 + (5967723/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2376998733670212212119/196484375000000000000000000 : ℝ) := by norm_num
    linear_combination (869666519/50000000000000 : ℝ)*(base19) + (1878868301/100000000000000 : ℝ)*(base23) + (527136293/100000000000000 : ℝ)*(lower1) + (64698179/25000000000000 : ℝ)*(upper3) + (3912693/6250000000000 : ℝ)*(lower4) + (251794883/100000000000000 : ℝ)*(upper5) + (985611573892337/50000000000000 : ℝ)*(major0) + (985611573892337/50000000000000 : ℝ)*(major1) + (985611573892337/50000000000000 : ℝ)*(major2) + (291613359/25000000000000 : ℝ)*(sp2) + (1440579043890237/50000000000000 : ℝ)*(sp4) + (720289087111859/25000000000000 : ℝ)*(sp5) + (1440577521229369/50000000000000 : ℝ)*(sp6) + (1061287804533947/100000000000000 : ℝ)*(sp7) + (1061287804533947/100000000000000 : ℝ)*(f.failure) + (1440579043890237/50000000000000 : ℝ)*(f.sum) + (309196864863809/37725000000000000000000000000 : ℝ)*base66 + (20780216505196261883/3772500000000000000000000000000000 : ℝ)*base67 + (30297243244838761883/3772500000000000000000000000000000 : ℝ)*base69 + (25474847030233738117/3772500000000000000000000000000000 : ℝ)*base72 + (15392403900359/37725000000000000000000000000 : ℝ)*base74 + (46730913357486238117/3772500000000000000000000000000000 : ℝ)*base76 + (558503784283738117/3772500000000000000000000000000000 : ℝ)*base78 + (9645862726081261883/3772500000000000000000000000000000 : ℝ)*base79 + (9109227829877/4715625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4846503/1250000000000000000000 : ℝ)*base89 + (4846503/1250000000000000000000 : ℝ)*base91 + (4846503/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1682_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (23217349/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4323/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9747/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2437/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17291/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1682_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1682_box_0 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-294515903/2500000000 : ℝ)*x 0 + (10865107/20000000 : ℝ)*x 1 + (5432548991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (294515903/2500000000 : ℝ)^5079 ≤ (6864565921073/100000000000000 : ℝ)^4055 := by
    have hnat : (294515903 : ℕ)^5079*100000000000000^4055 ≤ 6864565921073^4055*2500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294515903 2500000000 6864565921073 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10865107/20000000 : ℝ)^5079 ≤ (46567741239253/100000000000000 : ℝ)^4055 := by
    have hnat : (10865107 : ℕ)^5079*100000000000000^4055 ≤ 46567741239253^4055*20000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10865107 20000000 46567741239253 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432548991/10000000000 : ℝ)^5079 ≤ (23283846413867/50000000000000 : ℝ)^4055 := by
    have hnat : (5432548991 : ℕ)^5079*50000000000000^4055 ≤ 23283846413867^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432548991 10000000000 23283846413867 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-294515903/2500000000 : ℝ), (10865107/20000000 : ℝ), (5432548991/10000000000 : ℝ)] ![(6864565921073/100000000000000 : ℝ), (46567741239253/100000000000000 : ℝ), (23283846413867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-294515903/2500000000 : ℝ)|^5079 ≤ (6864565921073/100000000000000 : ℝ)^4055
        have hw : |(-294515903/2500000000 : ℝ)|=(294515903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10865107/20000000 : ℝ)|^5079 ≤ (46567741239253/100000000000000 : ℝ)^4055
        have hw : |(10865107/20000000 : ℝ)|=(10865107/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432548991/10000000000 : ℝ)|^5079 ≤ (23283846413867/50000000000000 : ℝ)^4055
        have hw : |(5432548991/10000000000 : ℝ)|=(5432548991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_1 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613046811/5000000000 : ℝ)*x 0 + (-735796071/5000000000 : ℝ)*x 1 + (2716275591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613046811/5000000000 : ℝ)^5079 ≤ (354894356383/800000000000 : ℝ)^4055 := by
    have hnat : (2613046811 : ℕ)^5079*800000000000^4055 ≤ 354894356383^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613046811 5000000000 354894356383 800000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735796071/5000000000 : ℝ)^5079 ≤ (1814097818001/20000000000000 : ℝ)^4055 := by
    have hnat : (735796071 : ℕ)^5079*20000000000000^4055 ≤ 1814097818001^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735796071 5000000000 1814097818001 20000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716275591/5000000000 : ℝ)^5079 ≤ (9313543270343/20000000000000 : ℝ)^4055 := by
    have hnat : (2716275591 : ℕ)^5079*20000000000000^4055 ≤ 9313543270343^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716275591 5000000000 9313543270343 20000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613046811/5000000000 : ℝ), (-735796071/5000000000 : ℝ), (2716275591/5000000000 : ℝ)] ![(354894356383/800000000000 : ℝ), (1814097818001/20000000000000 : ℝ), (9313543270343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613046811/5000000000 : ℝ)|^5079 ≤ (354894356383/800000000000 : ℝ)^4055
        have hw : |(2613046811/5000000000 : ℝ)|=(2613046811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-735796071/5000000000 : ℝ)|^5079 ≤ (1814097818001/20000000000000 : ℝ)^4055
        have hw : |(-735796071/5000000000 : ℝ)|=(735796071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716275591/5000000000 : ℝ)|^5079 ≤ (9313543270343/20000000000000 : ℝ)^4055
        have hw : |(2716275591/5000000000 : ℝ)|=(2716275591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_2 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045219071/2000000000 : ℝ)*x 0 + (21220893/39062500 : ℝ)*x 1 + (-735796667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045219071/2000000000 : ℝ)^5079 ≤ (22180906486657/50000000000000 : ℝ)^4055 := by
    have hnat : (1045219071 : ℕ)^5079*50000000000000^4055 ≤ 22180906486657^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045219071 2000000000 22180906486657 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21220893/39062500 : ℝ)^5079 ≤ (46567688715601/100000000000000 : ℝ)^4055 := by
    have hnat : (21220893 : ℕ)^5079*100000000000000^4055 ≤ 46567688715601^4055*39062500^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21220893 39062500 46567688715601 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735796667/5000000000 : ℝ)^5079 ≤ (566906143283/6250000000000 : ℝ)^4055 := by
    have hnat : (735796667 : ℕ)^5079*6250000000000^4055 ≤ 566906143283^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735796667 5000000000 566906143283 6250000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045219071/2000000000 : ℝ), (21220893/39062500 : ℝ), (-735796667/5000000000 : ℝ)] ![(22180906486657/50000000000000 : ℝ), (46567688715601/100000000000000 : ℝ), (566906143283/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045219071/2000000000 : ℝ)|^5079 ≤ (22180906486657/50000000000000 : ℝ)^4055
        have hw : |(1045219071/2000000000 : ℝ)|=(1045219071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21220893/39062500 : ℝ)|^5079 ≤ (46567688715601/100000000000000 : ℝ)^4055
        have hw : |(21220893/39062500 : ℝ)|=(21220893/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-735796667/5000000000 : ℝ)|^5079 ≤ (566906143283/6250000000000 : ℝ)^4055
        have hw : |(-735796667/5000000000 : ℝ)|=(735796667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_3 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4527846709/10000000000 : ℝ)*x 0 + (158908169/400000000 : ℝ)*x 1 + (15518359/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4527846709/10000000000 : ℝ)^5079 ≤ (3706763062377/10000000000000 : ℝ)^4055 := by
    have hnat : (4527846709 : ℕ)^5079*10000000000000^4055 ≤ 3706763062377^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527846709 10000000000 3706763062377 10000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158908169/400000000 : ℝ)^5079 ≤ (31466206115801/100000000000000 : ℝ)^4055 := by
    have hnat : (158908169 : ℕ)^5079*100000000000000^4055 ≤ 31466206115801^4055*400000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158908169 400000000 31466206115801 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15518359/39062500 : ℝ)^5079 ≤ (31466163248147/100000000000000 : ℝ)^4055 := by
    have hnat : (15518359 : ℕ)^5079*100000000000000^4055 ≤ 31466163248147^4055*39062500^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15518359 39062500 31466163248147 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4527846709/10000000000 : ℝ), (158908169/400000000 : ℝ), (15518359/39062500 : ℝ)] ![(3706763062377/10000000000000 : ℝ), (31466206115801/100000000000000 : ℝ), (31466163248147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4527846709/10000000000 : ℝ)|^5079 ≤ (3706763062377/10000000000000 : ℝ)^4055
        have hw : |(4527846709/10000000000 : ℝ)|=(4527846709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158908169/400000000 : ℝ)|^5079 ≤ (31466206115801/100000000000000 : ℝ)^4055
        have hw : |(158908169/400000000 : ℝ)|=(158908169/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15518359/39062500 : ℝ)|^5079 ≤ (31466163248147/100000000000000 : ℝ)^4055
        have hw : |(15518359/39062500 : ℝ)|=(15518359/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_4 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-941574099/5000000000 : ℝ)*x 0 + (1035080489/2000000000 : ℝ)*x 1 + (5175401273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941574099/5000000000 : ℝ)^5079 ≤ (12353007859801/100000000000000 : ℝ)^4055 := by
    have hnat : (941574099 : ℕ)^5079*100000000000000^4055 ≤ 12353007859801^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941574099 5000000000 12353007859801 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035080489/2000000000 : ℝ)^5079 ≤ (21911751137507/50000000000000 : ℝ)^4055 := by
    have hnat : (1035080489 : ℕ)^5079*50000000000000^4055 ≤ 21911751137507^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035080489 2000000000 21911751137507 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175401273/10000000000 : ℝ)^5079 ≤ (2191174492241/5000000000000 : ℝ)^4055 := by
    have hnat : (5175401273 : ℕ)^5079*5000000000000^4055 ≤ 2191174492241^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175401273 10000000000 2191174492241 5000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-941574099/5000000000 : ℝ), (1035080489/2000000000 : ℝ), (5175401273/10000000000 : ℝ)] ![(12353007859801/100000000000000 : ℝ), (21911751137507/50000000000000 : ℝ), (2191174492241/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-941574099/5000000000 : ℝ)|^5079 ≤ (12353007859801/100000000000000 : ℝ)^4055
        have hw : |(-941574099/5000000000 : ℝ)|=(941574099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035080489/2000000000 : ℝ)|^5079 ≤ (21911751137507/50000000000000 : ℝ)^4055
        have hw : |(1035080489/2000000000 : ℝ)|=(1035080489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175401273/10000000000 : ℝ)|^5079 ≤ (2191174492241/5000000000000 : ℝ)^4055
        have hw : |(5175401273/10000000000 : ℝ)|=(5175401273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_5 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5401697901/10000000000 : ℝ)*x 0 + (-1583146791/10000000000 : ℝ)*x 1 + (323462619/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401697901/10000000000 : ℝ)^5079 ≤ (577958670053/1250000000000 : ℝ)^4055 := by
    have hnat : (5401697901 : ℕ)^5079*1250000000000^4055 ≤ 577958670053^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401697901 10000000000 577958670053 1250000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1583146791/10000000000 : ℝ)^5079 ≤ (4969904921539/50000000000000 : ℝ)^4055 := by
    have hnat : (1583146791 : ℕ)^5079*50000000000000^4055 ≤ 4969904921539^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583146791 10000000000 4969904921539 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323462619/625000000 : ℝ)^5079 ≤ (8764699307437/20000000000000 : ℝ)^4055 := by
    have hnat : (323462619 : ℕ)^5079*20000000000000^4055 ≤ 8764699307437^4055*625000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323462619 625000000 8764699307437 20000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401697901/10000000000 : ℝ), (-1583146791/10000000000 : ℝ), (323462619/625000000 : ℝ)] ![(577958670053/1250000000000 : ℝ), (4969904921539/50000000000000 : ℝ), (8764699307437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401697901/10000000000 : ℝ)|^5079 ≤ (577958670053/1250000000000 : ℝ)^4055
        have hw : |(5401697901/10000000000 : ℝ)|=(5401697901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1583146791/10000000000 : ℝ)|^5079 ≤ (4969904921539/50000000000000 : ℝ)^4055
        have hw : |(-1583146791/10000000000 : ℝ)|=(1583146791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323462619/625000000 : ℝ)|^5079 ≤ (8764699307437/20000000000000 : ℝ)^4055
        have hw : |(323462619/625000000 : ℝ)|=(323462619/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_6 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350424419/2500000000 : ℝ)*x 0 + (5175401977/10000000000 : ℝ)*x 1 + (-1583146999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350424419/2500000000 : ℝ)^5079 ≤ (1444896599749/3125000000000 : ℝ)^4055 := by
    have hnat : (1350424419 : ℕ)^5079*3125000000000^4055 ≤ 1444896599749^4055*2500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350424419 2500000000 1444896599749 3125000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175401977/10000000000 : ℝ)^5079 ≤ (43823497311421/100000000000000 : ℝ)^4055 := by
    have hnat : (5175401977 : ℕ)^5079*100000000000000^4055 ≤ 43823497311421^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175401977 10000000000 43823497311421 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583146999/10000000000 : ℝ)^5079 ≤ (9939811478793/100000000000000 : ℝ)^4055 := by
    have hnat : (1583146999 : ℕ)^5079*100000000000000^4055 ≤ 9939811478793^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583146999 10000000000 9939811478793 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350424419/2500000000 : ℝ), (5175401977/10000000000 : ℝ), (-1583146999/10000000000 : ℝ)] ![(1444896599749/3125000000000 : ℝ), (43823497311421/100000000000000 : ℝ), (9939811478793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350424419/2500000000 : ℝ)|^5079 ≤ (1444896599749/3125000000000 : ℝ)^4055
        have hw : |(1350424419/2500000000 : ℝ)|=(1350424419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175401977/10000000000 : ℝ)|^5079 ≤ (43823497311421/100000000000000 : ℝ)^4055
        have hw : |(5175401977/10000000000 : ℝ)|=(5175401977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1583146999/10000000000 : ℝ)|^5079 ≤ (9939811478793/100000000000000 : ℝ)^4055
        have hw : |(-1583146999/10000000000 : ℝ)|=(1583146999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_7 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (187138527/500000000 : ℝ)*x 0 + (4364364171/10000000000 : ℝ)*x 1 + (1091090777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187138527/500000000 : ℝ)^5079 ≤ (29202003245437/100000000000000 : ℝ)^4055 := by
    have hnat : (187138527 : ℕ)^5079*100000000000000^4055 ≤ 29202003245437^4055*500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187138527 500000000 29202003245437 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4364364171/10000000000 : ℝ)^5079 ≤ (17699501882751/50000000000000 : ℝ)^4055 := by
    have hnat : (4364364171 : ℕ)^5079*50000000000000^4055 ≤ 17699501882751^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364364171 10000000000 17699501882751 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091090777/2500000000 : ℝ)^5079 ≤ (1415959718653/4000000000000 : ℝ)^4055 := by
    have hnat : (1091090777 : ℕ)^5079*4000000000000^4055 ≤ 1415959718653^4055*2500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091090777 2500000000 1415959718653 4000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(187138527/500000000 : ℝ), (4364364171/10000000000 : ℝ), (1091090777/2500000000 : ℝ)] ![(29202003245437/100000000000000 : ℝ), (17699501882751/50000000000000 : ℝ), (1415959718653/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(187138527/500000000 : ℝ)|^5079 ≤ (29202003245437/100000000000000 : ℝ)^4055
        have hw : |(187138527/500000000 : ℝ)|=(187138527/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4364364171/10000000000 : ℝ)|^5079 ≤ (17699501882751/50000000000000 : ℝ)^4055
        have hw : |(4364364171/10000000000 : ℝ)|=(4364364171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091090777/2500000000 : ℝ)|^5079 ≤ (1415959718653/4000000000000 : ℝ)^4055
        have hw : |(1091090777/2500000000 : ℝ)|=(1091090777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_8 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-346406191/2000000000 : ℝ)*x 0 + (1246786869/2500000000 : ℝ)*x 1 + (13691153/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (346406191/2000000000 : ℝ)^5079 ≤ (2781056643613/25000000000000 : ℝ)^4055 := by
    have hnat : (346406191 : ℕ)^5079*25000000000000^4055 ≤ 2781056643613^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346406191 2000000000 2781056643613 25000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1246786869/2500000000 : ℝ)^5079 ≤ (2091806537681/5000000000000 : ℝ)^4055 := by
    have hnat : (1246786869 : ℕ)^5079*5000000000000^4055 ≤ 2091806537681^4055*2500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246786869 2500000000 2091806537681 5000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13691153/25000000 : ℝ)^5079 ≤ (734994416641/1562500000000 : ℝ)^4055 := by
    have hnat : (13691153 : ℕ)^5079*1562500000000^4055 ≤ 734994416641^4055*25000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13691153 25000000 734994416641 1562500000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-346406191/2000000000 : ℝ), (1246786869/2500000000 : ℝ), (13691153/25000000 : ℝ)] ![(2781056643613/25000000000000 : ℝ), (2091806537681/5000000000000 : ℝ), (734994416641/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-346406191/2000000000 : ℝ)|^5079 ≤ (2781056643613/25000000000000 : ℝ)^4055
        have hw : |(-346406191/2000000000 : ℝ)|=(346406191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1246786869/2500000000 : ℝ)|^5079 ≤ (2091806537681/5000000000000 : ℝ)^4055
        have hw : |(1246786869/2500000000 : ℝ)|=(1246786869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13691153/25000000 : ℝ)|^5079 ≤ (734994416641/1562500000000 : ℝ)^4055
        have hw : |(13691153/25000000 : ℝ)|=(13691153/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_9 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259805737/500000000 : ℝ)*x 0 + (-1417661/9765625 : ℝ)*x 1 + (1095292363/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259805737/500000000 : ℝ)^5079 ≤ (8808657421217/20000000000000 : ℝ)^4055 := by
    have hnat : (259805737 : ℕ)^5079*20000000000000^4055 ≤ 8808657421217^4055*500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259805737 500000000 8808657421217 20000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1417661/9765625 : ℝ)^5079 ≤ (8917063597761/100000000000000 : ℝ)^4055 := by
    have hnat : (1417661 : ℕ)^5079*100000000000000^4055 ≤ 8917063597761^4055*9765625^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417661 9765625 8917063597761 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095292363/2000000000 : ℝ)^5079 ≤ (9407929856299/20000000000000 : ℝ)^4055 := by
    have hnat : (1095292363 : ℕ)^5079*20000000000000^4055 ≤ 9407929856299^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095292363 2000000000 9407929856299 20000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259805737/500000000 : ℝ), (-1417661/9765625 : ℝ), (1095292363/2000000000 : ℝ)] ![(8808657421217/20000000000000 : ℝ), (8917063597761/100000000000000 : ℝ), (9407929856299/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259805737/500000000 : ℝ)|^5079 ≤ (8808657421217/20000000000000 : ℝ)^4055
        have hw : |(259805737/500000000 : ℝ)|=(259805737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1417661/9765625 : ℝ)|^5079 ≤ (8917063597761/100000000000000 : ℝ)^4055
        have hw : |(-1417661/9765625 : ℝ)|=(1417661/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095292363/2000000000 : ℝ)|^5079 ≤ (9407929856299/20000000000000 : ℝ)^4055
        have hw : |(1095292363/2000000000 : ℝ)|=(1095292363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_10 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103922297/200000000 : ℝ)*x 0 + (1095292457/2000000000 : ℝ)*x 1 + (-181460507/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103922297/200000000 : ℝ)^5079 ≤ (22021644136959/50000000000000 : ℝ)^4055 := by
    have hnat : (103922297 : ℕ)^5079*50000000000000^4055 ≤ 22021644136959^4055*200000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103922297 200000000 22021644136959 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095292457/2000000000 : ℝ)^5079 ≤ (23519827168993/50000000000000 : ℝ)^4055 := by
    have hnat : (1095292457 : ℕ)^5079*50000000000000^4055 ≤ 23519827168993^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095292457 2000000000 23519827168993 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181460507/1250000000 : ℝ)^5079 ≤ (8917057381229/100000000000000 : ℝ)^4055 := by
    have hnat : (181460507 : ℕ)^5079*100000000000000^4055 ≤ 8917057381229^4055*1250000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181460507 1250000000 8917057381229 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103922297/200000000 : ℝ), (1095292457/2000000000 : ℝ), (-181460507/1250000000 : ℝ)] ![(22021644136959/50000000000000 : ℝ), (23519827168993/50000000000000 : ℝ), (8917057381229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103922297/200000000 : ℝ)|^5079 ≤ (22021644136959/50000000000000 : ℝ)^4055
        have hw : |(103922297/200000000 : ℝ)|=(103922297/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095292457/2000000000 : ℝ)|^5079 ≤ (23519827168993/50000000000000 : ℝ)^4055
        have hw : |(1095292457/2000000000 : ℝ)|=(1095292457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-181460507/1250000000 : ℝ)|^5079 ≤ (8917057381229/100000000000000 : ℝ)^4055
        have hw : |(-181460507/1250000000 : ℝ)|=(181460507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_11 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4656859849/10000000000 : ℝ)*x 0 + (122051513/312500000 : ℝ)*x 1 + (976411659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4656859849/10000000000 : ℝ)^5079 ≤ (9598812160753/25000000000000 : ℝ)^4055 := by
    have hnat : (4656859849 : ℕ)^5079*25000000000000^4055 ≤ 9598812160753^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4656859849 10000000000 9598812160753 25000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122051513/312500000 : ℝ)^5079 ≤ (3080238446229/10000000000000 : ℝ)^4055 := by
    have hnat : (122051513 : ℕ)^5079*10000000000000^4055 ≤ 3080238446229^4055*312500000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122051513 312500000 3080238446229 10000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976411659/2500000000 : ℝ)^5079 ≤ (15401183439533/50000000000000 : ℝ)^4055 := by
    have hnat : (976411659 : ℕ)^5079*50000000000000^4055 ≤ 15401183439533^4055*2500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976411659 2500000000 15401183439533 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4656859849/10000000000 : ℝ), (122051513/312500000 : ℝ), (976411659/2500000000 : ℝ)] ![(9598812160753/25000000000000 : ℝ), (3080238446229/10000000000000 : ℝ), (15401183439533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4656859849/10000000000 : ℝ)|^5079 ≤ (9598812160753/25000000000000 : ℝ)^4055
        have hw : |(4656859849/10000000000 : ℝ)|=(4656859849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(122051513/312500000 : ℝ)|^5079 ≤ (3080238446229/10000000000000 : ℝ)^4055
        have hw : |(122051513/312500000 : ℝ)|=(122051513/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(976411659/2500000000 : ℝ)|^5079 ≤ (15401183439533/50000000000000 : ℝ)^4055
        have hw : |(976411659/2500000000 : ℝ)|=(976411659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_12 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1324665147/10000000000 : ℝ)*x 0 + (701408497/1250000000 : ℝ)*x 1 + (2575021611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324665147/10000000000 : ℝ)^5079 ≤ (7950849753067/100000000000000 : ℝ)^4055 := by
    have hnat : (1324665147 : ℕ)^5079*100000000000000^4055 ≤ 7950849753067^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324665147 10000000000 7950849753067 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (701408497/1250000000 : ℝ)^5079 ≤ (24247220230409/50000000000000 : ℝ)^4055 := by
    have hnat : (701408497 : ℕ)^5079*50000000000000^4055 ≤ 24247220230409^4055*1250000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701408497 1250000000 24247220230409 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575021611/5000000000 : ℝ)^5079 ≤ (43554709773909/100000000000000 : ℝ)^4055 := by
    have hnat : (2575021611 : ℕ)^5079*100000000000000^4055 ≤ 43554709773909^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575021611 5000000000 43554709773909 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1324665147/10000000000 : ℝ), (701408497/1250000000 : ℝ), (2575021611/5000000000 : ℝ)] ![(7950849753067/100000000000000 : ℝ), (24247220230409/50000000000000 : ℝ), (43554709773909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1324665147/10000000000 : ℝ)|^5079 ≤ (7950849753067/100000000000000 : ℝ)^4055
        have hw : |(-1324665147/10000000000 : ℝ)|=(1324665147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(701408497/1250000000 : ℝ)|^5079 ≤ (24247220230409/50000000000000 : ℝ)^4055
        have hw : |(701408497/1250000000 : ℝ)|=(701408497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575021611/5000000000 : ℝ)|^5079 ≤ (43554709773909/100000000000000 : ℝ)^4055
        have hw : |(2575021611/5000000000 : ℝ)|=(2575021611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_13 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083808217/2000000000 : ℝ)*x 0 + (-1593663237/10000000000 : ℝ)*x 1 + (5150043297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083808217/2000000000 : ℝ)^5079 ≤ (46422708853443/100000000000000 : ℝ)^4055 := by
    have hnat : (1083808217 : ℕ)^5079*100000000000000^4055 ≤ 46422708853443^4055*2000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083808217 2000000000 46422708853443 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1593663237/10000000000 : ℝ)^5079 ≤ (10022580565933/100000000000000 : ℝ)^4055 := by
    have hnat : (1593663237 : ℕ)^5079*100000000000000^4055 ≤ 10022580565933^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593663237 10000000000 10022580565933 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150043297/10000000000 : ℝ)^5079 ≤ (4355471056837/10000000000000 : ℝ)^4055 := by
    have hnat : (5150043297 : ℕ)^5079*10000000000000^4055 ≤ 4355471056837^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150043297 10000000000 4355471056837 10000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083808217/2000000000 : ℝ), (-1593663237/10000000000 : ℝ), (5150043297/10000000000 : ℝ)] ![(46422708853443/100000000000000 : ℝ), (10022580565933/100000000000000 : ℝ), (4355471056837/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083808217/2000000000 : ℝ)|^5079 ≤ (46422708853443/100000000000000 : ℝ)^4055
        have hw : |(1083808217/2000000000 : ℝ)|=(1083808217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1593663237/10000000000 : ℝ)|^5079 ≤ (10022580565933/100000000000000 : ℝ)^4055
        have hw : |(-1593663237/10000000000 : ℝ)|=(1593663237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150043297/10000000000 : ℝ)|^5079 ≤ (4355471056837/10000000000000 : ℝ)^4055
        have hw : |(5150043297/10000000000 : ℝ)|=(5150043297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_14 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1354760283/2500000000 : ℝ)*x 0 + (643755371/1250000000 : ℝ)*x 1 + (-796831807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354760283/2500000000 : ℝ)^5079 ≤ (11605677339437/25000000000000 : ℝ)^4055 := by
    have hnat : (1354760283 : ℕ)^5079*25000000000000^4055 ≤ 11605677339437^4055*2500000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354760283 2500000000 11605677339437 25000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643755371/1250000000 : ℝ)^5079 ≤ (10888676770833/25000000000000 : ℝ)^4055 := by
    have hnat : (643755371 : ℕ)^5079*25000000000000^4055 ≤ 10888676770833^4055*1250000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643755371 1250000000 10888676770833 25000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796831807/5000000000 : ℝ)^5079 ≤ (10022583535627/100000000000000 : ℝ)^4055 := by
    have hnat : (796831807 : ℕ)^5079*100000000000000^4055 ≤ 10022583535627^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796831807 5000000000 10022583535627 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354760283/2500000000 : ℝ), (643755371/1250000000 : ℝ), (-796831807/5000000000 : ℝ)] ![(11605677339437/25000000000000 : ℝ), (10888676770833/25000000000000 : ℝ), (10022583535627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354760283/2500000000 : ℝ)|^5079 ≤ (11605677339437/25000000000000 : ℝ)^4055
        have hw : |(1354760283/2500000000 : ℝ)|=(1354760283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643755371/1250000000 : ℝ)|^5079 ≤ (10888676770833/25000000000000 : ℝ)^4055
        have hw : |(643755371/1250000000 : ℝ)|=(643755371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-796831807/5000000000 : ℝ)|^5079 ≤ (10022583535627/100000000000000 : ℝ)^4055
        have hw : |(-796831807/5000000000 : ℝ)|=(796831807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1682_box_15 (p : ℝ) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3662369639/10000000000 : ℝ)*x 0 + (2201442939/5000000000 : ℝ)*x 1 + (440288591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3662369639/10000000000 : ℝ)^5079 ≤ (14209213042893/50000000000000 : ℝ)^4055 := by
    have hnat : (3662369639 : ℕ)^5079*50000000000000^4055 ≤ 14209213042893^4055*10000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3662369639 10000000000 14209213042893 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201442939/5000000000 : ℝ)^5079 ≤ (17895393393021/50000000000000 : ℝ)^4055 := by
    have hnat : (2201442939 : ℕ)^5079*50000000000000^4055 ≤ 17895393393021^4055*5000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201442939 5000000000 17895393393021 50000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440288591/1000000000 : ℝ)^5079 ≤ (35790787111857/100000000000000 : ℝ)^4055 := by
    have hnat : (440288591 : ℕ)^5079*100000000000000^4055 ≤ 35790787111857^4055*1000000000^5079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440288591 1000000000 35790787111857 100000000000000 5079 4055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5079/1024 : ℝ)) 5079 4055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3662369639/10000000000 : ℝ), (2201442939/5000000000 : ℝ), (440288591/1000000000 : ℝ)] ![(14209213042893/50000000000000 : ℝ), (17895393393021/50000000000000 : ℝ), (35790787111857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3662369639/10000000000 : ℝ)|^5079 ≤ (14209213042893/50000000000000 : ℝ)^4055
        have hw : |(3662369639/10000000000 : ℝ)|=(3662369639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2201442939/5000000000 : ℝ)|^5079 ≤ (17895393393021/50000000000000 : ℝ)^4055
        have hw : |(2201442939/5000000000 : ℝ)|=(2201442939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(440288591/1000000000 : ℝ)|^5079 ≤ (35790787111857/100000000000000 : ℝ)^4055
        have hw : |(440288591/1000000000 : ℝ)|=(440288591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1682_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (23217349/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17291/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2437/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66511/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57739/100000 : ℝ) ∧ (40259/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (22503/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17291/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2437/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17291/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2437/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17291/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2437/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17291/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2437/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17291/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2437/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17291/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2437/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2437/25000 : ℝ) ^ (5071/1024 : ℝ) ≤ (491959757839959/50000000000000000000 : ℝ) := by
    have hpowers : (2437/25000 : ℝ)^5071 ≤ (491959757839959/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2437 : ℕ)^5071*50000000000000000000^1024 ≤ 491959757839959^1024*25000^5071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2437 25000 491959757839959 50000000000000000000 5071 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2437/25000 : ℝ)) (X := (491959757839959/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17291/100000 : ℝ) ^ (5071/1024 : ℝ) ≤ (2101270994173911/12500000000000000000 : ℝ) := by
    have hpowers : (17291/100000 : ℝ)^5071 ≤ (2101270994173911/12500000000000000000 : ℝ)^1024 := by
      have hnat : (17291 : ℕ)^5071*12500000000000000000^1024 ≤ 2101270994173911^1024*100000^5071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17291 100000 2101270994173911 12500000000000000000 5071 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17291/100000 : ℝ)) (X := (2101270994173911/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000491959757839959/25000000000000000000 : ℝ) ≤ (5000019868382423/5000000000000000 : ℝ) ^ (5071/1024 : ℝ) := by
    have hpowers : (25000491959757839959/25000000000000000000 : ℝ)^1024 ≤ (5000019868382423/5000000000000000 : ℝ)^5071 := by
      have hnat : (25000491959757839959 : ℕ)^1024*5000000000000000^5071 ≤ 5000019868382423^5071*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000491959757839959 25000000000000000000 5000019868382423 5000000000000000 1024 5071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000019868382423/5000000000000000 : ℝ)) (X := (25000491959757839959/25000000000000000000 : ℝ)) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50008897043734535603/50000000000000000000 : ℝ) ≤ (12500449118811/12500000000000 : ℝ) ^ (5071/1024 : ℝ) := by
    have hpowers : (50008897043734535603/50000000000000000000 : ℝ)^1024 ≤ (12500449118811/12500000000000 : ℝ)^5071 := by
      have hnat : (50008897043734535603 : ℕ)^1024*12500000000000^5071 ≤ 12500449118811^5071*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008897043734535603 50000000000000000000 12500449118811 12500000000000 1024 5071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12500449118811/12500000000000 : ℝ)) (X := (50008897043734535603/50000000000000000000 : ℝ)) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252101270994173911/6250000000000000000 : ℝ) ≤ (5000339426666377/5000000000000000 : ℝ) ^ (5071/1024 : ℝ) := by
    have hpowers : (6252101270994173911/6250000000000000000 : ℝ)^1024 ≤ (5000339426666377/5000000000000000 : ℝ)^5071 := by
      have hnat : (6252101270994173911 : ℕ)^1024*5000000000000000^5071 ≤ 5000339426666377^5071*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252101270994173911 6250000000000000000 5000339426666377 5000000000000000 1024 5071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000339426666377/5000000000000000 : ℝ)) (X := (6252101270994173911/6250000000000000000 : ℝ)) (by norm_num) 5071 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(491959757839959/50000000000000000000 : ℝ) ≤ ((37712034813056633097/37715000000000000000 : ℝ)+2*(159779141977/377150000000000 : ℝ)*(2437/25000 : ℝ))^(5071/1024 : ℝ) := by
    rw [show (37712034813056633097/37715000000000000000 : ℝ)+2*(159779141977/377150000000000 : ℝ)*(2437/25000 : ℝ)=(5000019868382423/5000000000000000 : ℝ) by norm_num, show 1+2*(491959757839959/50000000000000000000 : ℝ)=(25000491959757839959/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2101270994173911/12500000000000000000 : ℝ)+(491959757839959/50000000000000000000 : ℝ) ≤ ((37712034813056633097/37715000000000000000 : ℝ)+(159779141977/377150000000000 : ℝ)*((17291/100000 : ℝ)+(2437/25000 : ℝ)))^(5071/1024 : ℝ) := by
    rw [show (37712034813056633097/37715000000000000000 : ℝ)+(159779141977/377150000000000 : ℝ)*((17291/100000 : ℝ)+(2437/25000 : ℝ))=(12500449118811/12500000000000 : ℝ) by norm_num, show 1+(2101270994173911/12500000000000000000 : ℝ)+(491959757839959/50000000000000000000 : ℝ)=(50008897043734535603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2101270994173911/12500000000000000000 : ℝ) ≤ ((37712034813056633097/37715000000000000000 : ℝ)+2*(159779141977/377150000000000 : ℝ)*(17291/100000 : ℝ))^(5071/1024 : ℝ) := by
    rw [show (37712034813056633097/37715000000000000000 : ℝ)+2*(159779141977/377150000000000 : ℝ)*(17291/100000 : ℝ)=(5000339426666377/5000000000000000 : ℝ) by norm_num, show 1+2*(2101270994173911/12500000000000000000 : ℝ)=(6252101270994173911/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37712034813056633097/37715000000000000000 : ℝ)*(X 1 0+X 2 0)+(159779141977/377150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5071/1024 : ℝ)) (lo := (2437/25000 : ℝ)) (hi := (17291/100000 : ℝ)) (c := (37712034813056633097/37715000000000000000 : ℝ)) (alpha := (159779141977/377150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37712034813056633097/37715000000000000000 : ℝ)*(X 0 1+X 2 1)+(159779141977/377150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5071/1024 : ℝ)) (lo := (2437/25000 : ℝ)) (hi := (17291/100000 : ℝ)) (c := (37712034813056633097/37715000000000000000 : ℝ)) (alpha := (159779141977/377150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37712034813056633097/37715000000000000000 : ℝ)*(X 0 2+X 1 2)+(159779141977/377150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5071/1024 : ℝ)) (lo := (2437/25000 : ℝ)) (hi := (17291/100000 : ℝ)) (c := (37712034813056633097/37715000000000000000 : ℝ)) (alpha := (159779141977/377150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-294515903/2500000000 : ℝ)*X 0 0+(10865107/20000000 : ℝ)*X 0 1+(5432548991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2613046811/5000000000 : ℝ)*X 1 0+(-735796071/5000000000 : ℝ)*X 1 1+(2716275591/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1045219071/2000000000 : ℝ)*X 2 0+(21220893/39062500 : ℝ)*X 2 1+(-735796667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4527846709/10000000000 : ℝ)*X 0 0+(158908169/400000000 : ℝ)*X 0 1+(15518359/39062500 : ℝ)*X 0 2+(4527846709/10000000000 : ℝ)*X 1 0+(158908169/400000000 : ℝ)*X 1 1+(15518359/39062500 : ℝ)*X 1 2+(4527846709/10000000000 : ℝ)*X 2 0+(158908169/400000000 : ℝ)*X 2 1+(15518359/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-941574099/5000000000 : ℝ)*X 0 0+(1035080489/2000000000 : ℝ)*X 0 1+(5175401273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5401697901/10000000000 : ℝ)*X 1 0+(-1583146791/10000000000 : ℝ)*X 1 1+(323462619/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1350424419/2500000000 : ℝ)*X 2 0+(5175401977/10000000000 : ℝ)*X 2 1+(-1583146999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((187138527/500000000 : ℝ)*X 0 0+(4364364171/10000000000 : ℝ)*X 0 1+(1091090777/2500000000 : ℝ)*X 0 2+(187138527/500000000 : ℝ)*X 1 0+(4364364171/10000000000 : ℝ)*X 1 1+(1091090777/2500000000 : ℝ)*X 1 2+(187138527/500000000 : ℝ)*X 2 0+(4364364171/10000000000 : ℝ)*X 2 1+(1091090777/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-346406191/2000000000 : ℝ)*X 0 0+(1246786869/2500000000 : ℝ)*X 0 1+(13691153/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((259805737/500000000 : ℝ)*X 1 0+(-1417661/9765625 : ℝ)*X 1 1+(1095292363/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((103922297/200000000 : ℝ)*X 2 0+(1095292457/2000000000 : ℝ)*X 2 1+(-181460507/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4656859849/10000000000 : ℝ)*X 0 0+(122051513/312500000 : ℝ)*X 0 1+(976411659/2500000000 : ℝ)*X 0 2+(4656859849/10000000000 : ℝ)*X 1 0+(122051513/312500000 : ℝ)*X 1 1+(976411659/2500000000 : ℝ)*X 1 2+(4656859849/10000000000 : ℝ)*X 2 0+(122051513/312500000 : ℝ)*X 2 1+(976411659/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1324665147/10000000000 : ℝ)*X 0 0+(701408497/1250000000 : ℝ)*X 0 1+(2575021611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1083808217/2000000000 : ℝ)*X 1 0+(-1593663237/10000000000 : ℝ)*X 1 1+(5150043297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1354760283/2500000000 : ℝ)*X 2 0+(643755371/1250000000 : ℝ)*X 2 1+(-796831807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3662369639/10000000000 : ℝ)*X 0 0+(2201442939/5000000000 : ℝ)*X 0 1+(440288591/1000000000 : ℝ)*X 0 2+(3662369639/10000000000 : ℝ)*X 1 0+(2201442939/5000000000 : ℝ)*X 1 1+(440288591/1000000000 : ℝ)*X 1 2+(3662369639/10000000000 : ℝ)*X 2 0+(2201442939/5000000000 : ℝ)*X 2 1+(440288591/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1682_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66511/100000 : ℝ) ≤ (-62708952280718311350788581174623/94287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15752243/100000000000000 : ℝ)*(lower0) + (119091927/100000000000000 : ℝ)*(upper3) + (8447667/100000000000000 : ℝ)*(lower4) + (128481582230747/10000000000000 : ℝ)*(major0) + (128481582230747/10000000000000 : ℝ)*(major1) + (128481582230747/10000000000000 : ℝ)*(major2) + (738884627/20000000000000 : ℝ)*(sp1) + (1740966661/100000000000000 : ℝ)*(sp2) + (237508156089101/12500000000000 : ℝ)*(sp4) + (950032368260203/50000000000000 : ℝ)*(sp5) + (23750833624711/1250000000000 : ℝ)*(sp6) + (691729725910079/100000000000000 : ℝ)*(sp7) + (3182230733/100000000000000 : ℝ)*(sp8) + (2899500487/100000000000000 : ℝ)*(sp15) + (345866312705283/50000000000000 : ℝ)*(f.failure) + (950034215471771/50000000000000 : ℝ)*(f.sum) + (8016402296223/3771500000000000000000000000 : ℝ)*base66 + (406894110832316541/377150000000000000000000000000000 : ℝ)*base68 + (410277268151766541/377150000000000000000000000000000 : ℝ)*base70 + (868941355024216541/377150000000000000000000000000000 : ℝ)*base72 + (32296666105721/7543000000000000000000000000 : ℝ)*base74 + (237913838383266541/377150000000000000000000000000000 : ℝ)*base76 + (64475568168933459/377150000000000000000000000000000 : ℝ)*base77 + (1866334184819316541/377150000000000000000000000000000 : ℝ)*base80 + (720312963367/1885750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2054767/625000000000000000000 : ℝ)*base89 + (2054767/625000000000000000000 : ℝ)*base91 + (2054767/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (57739/100000 : ℝ) ≤ (272214019152060794805232239179553/471437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4652531/4000000000000 : ℝ)*(upper3) + (10059051/5000000000000 : ℝ)*(upper4) + (351113921/100000000000000 : ℝ)*(lower5) + (690788204442483/50000000000000 : ℝ)*(major0) + (690788204442483/50000000000000 : ℝ)*(major1) + (690788204442483/50000000000000 : ℝ)*(major2) + (2000063074290919/100000000000000 : ℝ)*(sp0) + (2000068172252911/100000000000000 : ℝ)*(sp1) + (200007645406661/10000000000000 : ℝ)*(sp2) + (74382030329419/10000000000000 : ℝ)*(sp3) + (2487179341/25000000000000 : ℝ)*(sp5) + (333380733/20000000000000 : ℝ)*(sp6) + (1460426813/20000000000000 : ℝ)*(sp7) + (3761669839/25000000000000 : ℝ)*(sp8) + (371913802714127/50000000000000 : ℝ)*(f.failure) + (80003124838811/4000000000000 : ℝ)*(f.sum) + (118165302820433/18857500000000000000000000000 : ℝ)*base66 + (4056449496909009851/1885750000000000000000000000000000 : ℝ)*base67 + (9425007103386990149/1885750000000000000000000000000000 : ℝ)*base70 + (15047032626612240149/1885750000000000000000000000000000 : ℝ)*base72 + (111651662703579/37715000000000000000000000000 : ℝ)*base73 + (4202520403498740149/1885750000000000000000000000000000 : ℝ)*base76 + (8293959128315240149/1885750000000000000000000000000000 : ℝ)*base78 + (8985308173227740149/1885750000000000000000000000000000 : ℝ)*base80 + (175331922383511/37715000000000000000000000000 : ℝ)*base82 + (3710677/625000000000000000000 : ℝ)*base90 + (3710677/625000000000000000000 : ℝ)*base92 + (3710677/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (40259/50000 : ℝ) ≤ (759206376489454843506636678570063/942875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124761/50000000000000 : ℝ)*(upper0) + (2276367/10000000000000 : ℝ)*(upper2) + (16930133/20000000000000 : ℝ)*(upper3) + (216562087/100000000000000 : ℝ)*(upper4) + (708301420721093/50000000000000 : ℝ)*(major0) + (708301420721093/50000000000000 : ℝ)*(major1) + (708301420721093/50000000000000 : ℝ)*(major2) + (9345266827/100000000000000 : ℝ)*(sp1) + (3324393671/5000000000000 : ℝ)*(sp2) + (3737839441/25000000000000 : ℝ)*(sp3) + (2043680057988551/100000000000000 : ℝ)*(sp8) + (2043670712721723/100000000000000 : ℝ)*(sp9) + (204361357011513/10000000000000 : ℝ)*(sp10) + (762670552401831/100000000000000 : ℝ)*(sp11) + (152537100751919/20000000000000 : ℝ)*(f.failure) + (2043680057988551/100000000000000 : ℝ)*(f.sum) + (5003359935297/18857500000000000000000000000 : ℝ)*base65 + (8712740439568084979/1885750000000000000000000000000000 : ℝ)*base68 + (4495857404443084979/1885750000000000000000000000000000 : ℝ)*base70 + (5222750781134165021/1885750000000000000000000000000000 : ℝ)*base71 + (13873799008453/18857500000000000000000000000 : ℝ)*base74 + (1212814852327334979/1885750000000000000000000000000000 : ℝ)*base76 + (6886159472115334979/1885750000000000000000000000000000 : ℝ)*base78 + (3549303424741415021/1885750000000000000000000000000000 : ℝ)*base79 + (394833339663/294648437500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (842731/250000000000000000000 : ℝ)*base89 + (842731/250000000000000000000 : ℝ)*base91 + (842731/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-22503/25000 : ℝ) ≤ (-848673244043290502059129592057751/942875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78128009/100000000000000 : ℝ)*(upper3) + (97419/200000000000 : ℝ)*(lower4) + (8655733/25000000000000 : ℝ)*(upper5) + (731433627613939/50000000000000 : ℝ)*(major0) + (731433627613939/50000000000000 : ℝ)*(major1) + (731433627613939/50000000000000 : ℝ)*(major2) + (2102556537/100000000000000 : ℝ)*(sp4) + (26499328401/100000000000000 : ℝ)*(sp5) + (30229859521/50000000000000 : ℝ)*(sp6) + (3750533543/25000000000000 : ℝ)*(sp7) + (8469303182967/390625000000 : ℝ)*(sp12) + (271014652258461/12500000000000 : ℝ)*(sp13) + (2168083257677047/100000000000000 : ℝ)*(sp14) + (787578822223143/100000000000000 : ℝ)*(sp15) + (157518764871463/20000000000000 : ℝ)*(f.failure) + (216814371739609/10000000000000 : ℝ)*(f.sum) + (70032655842907/37715000000000000000000000000 : ℝ)*base65 + (2433341545891010917/1885750000000000000000000000000000 : ℝ)*base68 + (7058988084302989083/1885750000000000000000000000000000 : ℝ)*base69 + (4196671922167739083/1885750000000000000000000000000000 : ℝ)*base71 + (17860074767473/37715000000000000000000000000 : ℝ)*base74 + (7261349696793260917/1885750000000000000000000000000000 : ℝ)*base76 + (7259817160968510917/1885750000000000000000000000000000 : ℝ)*base78 + (2230400549755760917/1885750000000000000000000000000000 : ℝ)*base80 + (74199665216631/18857500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1611587/250000000000000000000 : ℝ)*base89 + (1611587/250000000000000000000 : ℝ)*base91 + (1611587/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1682_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (23217349/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17291/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2437/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66511/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57739/100000 : ℝ) else (40259/50000 : ℝ) ≤ X j i ∧ X j i ≤ (22503/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1682_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1682_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (23217349/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8661/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9721/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66511/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57739/100000 : ℝ) else (40259/50000 : ℝ) ≤ X j i ∧ X j i ≤ (22503/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1682_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1682_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1682_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5071/1024 : ℝ) ≤ p) (hpb : p ≤ (5079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (23217349/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8661/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9721/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66511/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57739/100000 : ℝ) else (40259/50000 : ℝ) ≤ X j i ∧ X j i ≤ (22503/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1682_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
