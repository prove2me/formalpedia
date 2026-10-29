-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1353_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:08:06.318489+00:00
-- url     : https://prove2.me/submissions/32d4091e-1550-44cb-8309-261c15922a75

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
theorem support_rectangle_w1353_s0_0 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-56333163/312500000 : ℝ)*x 0 + (2996089663/5000000000 : ℝ)*x 1 + (4813526799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56333163/312500000 : ℝ)^4313 ≤ (2643563850213/25000000000000 : ℝ)^3289 := by
    have hnat : (56333163 : ℕ)^4313*25000000000000^3289 ≤ 2643563850213^3289*312500000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56333163 312500000 2643563850213 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2996089663/5000000000 : ℝ)^4313 ≤ (10218046258599/20000000000000 : ℝ)^3289 := by
    have hnat : (2996089663 : ℕ)^4313*20000000000000^3289 ≤ 10218046258599^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996089663 5000000000 10218046258599 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4813526799/10000000000 : ℝ)^4313 ≤ (38335513295291/100000000000000 : ℝ)^3289 := by
    have hnat : (4813526799 : ℕ)^4313*100000000000000^3289 ≤ 38335513295291^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4813526799 10000000000 38335513295291 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56333163/312500000 : ℝ), (2996089663/5000000000 : ℝ), (4813526799/10000000000 : ℝ)] ![(2643563850213/25000000000000 : ℝ), (10218046258599/20000000000000 : ℝ), (38335513295291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56333163/312500000 : ℝ)|^4313 ≤ (2643563850213/25000000000000 : ℝ)^3289
        have hw : |(-56333163/312500000 : ℝ)|=(56333163/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2996089663/5000000000 : ℝ)|^4313 ≤ (10218046258599/20000000000000 : ℝ)^3289
        have hw : |(2996089663/5000000000 : ℝ)|=(2996089663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4813526799/10000000000 : ℝ)|^4313 ≤ (38335513295291/100000000000000 : ℝ)^3289
        have hw : |(4813526799/10000000000 : ℝ)|=(4813526799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s0_1 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5500581103/10000000000 : ℝ)*x 0 + (-2472068107/10000000000 : ℝ)*x 1 + (4813527259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5500581103/10000000000 : ℝ)^4313 ≤ (1826615558577/4000000000000 : ℝ)^3289 := by
    have hnat : (5500581103 : ℕ)^4313*4000000000000^3289 ≤ 1826615558577^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500581103 10000000000 1826615558577 4000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2472068107/10000000000 : ℝ)^4313 ≤ (7999546462003/50000000000000 : ℝ)^3289 := by
    have hnat : (2472068107 : ℕ)^4313*50000000000000^3289 ≤ 7999546462003^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472068107 10000000000 7999546462003 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4813527259/10000000000 : ℝ)^4313 ≤ (38335518099383/100000000000000 : ℝ)^3289 := by
    have hnat : (4813527259 : ℕ)^4313*100000000000000^3289 ≤ 38335518099383^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4813527259 10000000000 38335518099383 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5500581103/10000000000 : ℝ), (-2472068107/10000000000 : ℝ), (4813527259/10000000000 : ℝ)] ![(1826615558577/4000000000000 : ℝ), (7999546462003/50000000000000 : ℝ), (38335518099383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5500581103/10000000000 : ℝ)|^4313 ≤ (1826615558577/4000000000000 : ℝ)^3289
        have hw : |(5500581103/10000000000 : ℝ)|=(5500581103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2472068107/10000000000 : ℝ)|^4313 ≤ (7999546462003/50000000000000 : ℝ)^3289
        have hw : |(-2472068107/10000000000 : ℝ)|=(2472068107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4813527259/10000000000 : ℝ)|^4313 ≤ (38335518099383/100000000000000 : ℝ)^3289
        have hw : |(4813527259/10000000000 : ℝ)|=(4813527259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s0_2 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2750290461/5000000000 : ℝ)*x 0 + (481352687/1000000000 : ℝ)*x 1 + (-2472068817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750290461/5000000000 : ℝ)^4313 ≤ (22832693496971/50000000000000 : ℝ)^3289 := by
    have hnat : (2750290461 : ℕ)^4313*50000000000000^3289 ≤ 22832693496971^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750290461 5000000000 22832693496971 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481352687/1000000000 : ℝ)^4313 ≤ (4791939254599/12500000000000 : ℝ)^3289 := by
    have hnat : (481352687 : ℕ)^4313*12500000000000^3289 ≤ 4791939254599^3289*1000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481352687 1000000000 4791939254599 12500000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2472068817/10000000000 : ℝ)^4313 ≤ (639963957989/4000000000000 : ℝ)^3289 := by
    have hnat : (2472068817 : ℕ)^4313*4000000000000^3289 ≤ 639963957989^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472068817 10000000000 639963957989 4000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750290461/5000000000 : ℝ), (481352687/1000000000 : ℝ), (-2472068817/10000000000 : ℝ)] ![(22832693496971/50000000000000 : ℝ), (4791939254599/12500000000000 : ℝ), (639963957989/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750290461/5000000000 : ℝ)|^4313 ≤ (22832693496971/50000000000000 : ℝ)^3289
        have hw : |(2750290461/5000000000 : ℝ)|=(2750290461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481352687/1000000000 : ℝ)|^4313 ≤ (4791939254599/12500000000000 : ℝ)^3289
        have hw : |(481352687/1000000000 : ℝ)|=(481352687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2472068817/10000000000 : ℝ)|^4313 ≤ (639963957989/4000000000000 : ℝ)^3289
        have hw : |(-2472068817/10000000000 : ℝ)|=(2472068817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s0_3 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2088552359/5000000000 : ℝ)*x 0 + (776509517/2500000000 : ℝ)*x 1 + (5585031629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088552359/5000000000 : ℝ)^4313 ≤ (31830127819883/100000000000000 : ℝ)^3289 := by
    have hnat : (2088552359 : ℕ)^4313*100000000000000^3289 ≤ 31830127819883^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088552359 5000000000 31830127819883 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776509517/2500000000 : ℝ)^4313 ≤ (21582910422289/100000000000000 : ℝ)^3289 := by
    have hnat : (776509517 : ℕ)^4313*100000000000000^3289 ≤ 21582910422289^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776509517 2500000000 21582910422289 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5585031629/10000000000 : ℝ)^4313 ≤ (46586961739499/100000000000000 : ℝ)^3289 := by
    have hnat : (5585031629 : ℕ)^4313*100000000000000^3289 ≤ 46586961739499^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585031629 10000000000 46586961739499 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088552359/5000000000 : ℝ), (776509517/2500000000 : ℝ), (5585031629/10000000000 : ℝ)] ![(31830127819883/100000000000000 : ℝ), (21582910422289/100000000000000 : ℝ), (46586961739499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088552359/5000000000 : ℝ)|^4313 ≤ (31830127819883/100000000000000 : ℝ)^3289
        have hw : |(2088552359/5000000000 : ℝ)|=(2088552359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776509517/2500000000 : ℝ)|^4313 ≤ (21582910422289/100000000000000 : ℝ)^3289
        have hw : |(776509517/2500000000 : ℝ)|=(776509517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5585031629/10000000000 : ℝ)|^4313 ≤ (46586961739499/100000000000000 : ℝ)^3289
        have hw : |(5585031629/10000000000 : ℝ)|=(5585031629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s0_4 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-451765113/2500000000 : ℝ)*x 0 + (75685037/156250000 : ℝ)*x 1 + (2980390481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451765113/2500000000 : ℝ)^4313 ≤ (10608108106951/100000000000000 : ℝ)^3289 := by
    have hnat : (451765113 : ℕ)^4313*100000000000000^3289 ≤ 10608108106951^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451765113 2500000000 10608108106951 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75685037/156250000 : ℝ)^4313 ≤ (38652429293013/100000000000000 : ℝ)^3289 := by
    have hnat : (75685037 : ℕ)^4313*100000000000000^3289 ≤ 38652429293013^3289*156250000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75685037 156250000 38652429293013 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2980390481/5000000000 : ℝ)^4313 ≤ (10147892516323/20000000000000 : ℝ)^3289 := by
    have hnat : (2980390481 : ℕ)^4313*20000000000000^3289 ≤ 10147892516323^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980390481 5000000000 10147892516323 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-451765113/2500000000 : ℝ), (75685037/156250000 : ℝ), (2980390481/5000000000 : ℝ)] ![(10608108106951/100000000000000 : ℝ), (38652429293013/100000000000000 : ℝ), (10147892516323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-451765113/2500000000 : ℝ)|^4313 ≤ (10608108106951/100000000000000 : ℝ)^3289
        have hw : |(-451765113/2500000000 : ℝ)|=(451765113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(75685037/156250000 : ℝ)|^4313 ≤ (38652429293013/100000000000000 : ℝ)^3289
        have hw : |(75685037/156250000 : ℝ)|=(75685037/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2980390481/5000000000 : ℝ)|^4313 ≤ (10147892516323/20000000000000 : ℝ)^3289
        have hw : |(2980390481/5000000000 : ℝ)|=(2980390481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s0_5 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5179291197/10000000000 : ℝ)*x 0 + (-264963143/2000000000 : ℝ)*x 1 + (1192156109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179291197/10000000000 : ℝ)^4313 ≤ (42199860511867/100000000000000 : ℝ)^3289 := by
    have hnat : (5179291197 : ℕ)^4313*100000000000000^3289 ≤ 42199860511867^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179291197 10000000000 42199860511867 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264963143/2000000000 : ℝ)^4313 ≤ (7060681545081/100000000000000 : ℝ)^3289 := by
    have hnat : (264963143 : ℕ)^4313*100000000000000^3289 ≤ 7060681545081^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264963143 2000000000 7060681545081 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192156109/2000000000 : ℝ)^4313 ≤ (25369728963443/50000000000000 : ℝ)^3289 := by
    have hnat : (1192156109 : ℕ)^4313*50000000000000^3289 ≤ 25369728963443^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192156109 2000000000 25369728963443 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179291197/10000000000 : ℝ), (-264963143/2000000000 : ℝ), (1192156109/2000000000 : ℝ)] ![(42199860511867/100000000000000 : ℝ), (7060681545081/100000000000000 : ℝ), (25369728963443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179291197/10000000000 : ℝ)|^4313 ≤ (42199860511867/100000000000000 : ℝ)^3289
        have hw : |(5179291197/10000000000 : ℝ)|=(5179291197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264963143/2000000000 : ℝ)|^4313 ≤ (7060681545081/100000000000000 : ℝ)^3289
        have hw : |(-264963143/2000000000 : ℝ)|=(264963143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192156109/2000000000 : ℝ)|^4313 ≤ (25369728963443/50000000000000 : ℝ)^3289
        have hw : |(1192156109/2000000000 : ℝ)|=(1192156109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s0_6 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5179291111/10000000000 : ℝ)*x 0 + (2980390519/5000000000 : ℝ)*x 1 + (-1324815059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179291111/10000000000 : ℝ)^4313 ≤ (10549964898249/25000000000000 : ℝ)^3289 := by
    have hnat : (5179291111 : ℕ)^4313*25000000000000^3289 ≤ 10549964898249^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179291111 10000000000 10549964898249 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2980390519/5000000000 : ℝ)^4313 ≤ (50739463429959/100000000000000 : ℝ)^3289 := by
    have hnat : (2980390519 : ℕ)^4313*100000000000000^3289 ≤ 50739463429959^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980390519 5000000000 50739463429959 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324815059/10000000000 : ℝ)^4313 ≤ (1412135392077/20000000000000 : ℝ)^3289 := by
    have hnat : (1324815059 : ℕ)^4313*20000000000000^3289 ≤ 1412135392077^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324815059 10000000000 1412135392077 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179291111/10000000000 : ℝ), (2980390519/5000000000 : ℝ), (-1324815059/10000000000 : ℝ)] ![(10549964898249/25000000000000 : ℝ), (50739463429959/100000000000000 : ℝ), (1412135392077/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179291111/10000000000 : ℝ)|^4313 ≤ (10549964898249/25000000000000 : ℝ)^3289
        have hw : |(5179291111/10000000000 : ℝ)|=(5179291111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2980390519/5000000000 : ℝ)|^4313 ≤ (50739463429959/100000000000000 : ℝ)^3289
        have hw : |(2980390519/5000000000 : ℝ)|=(2980390519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1324815059/10000000000 : ℝ)|^4313 ≤ (1412135392077/20000000000000 : ℝ)^3289
        have hw : |(-1324815059/10000000000 : ℝ)|=(1324815059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s0_7 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093177209/5000000000 : ℝ)*x 0 + (5521271809/10000000000 : ℝ)*x 1 + (1586038079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093177209/5000000000 : ℝ)^4313 ≤ (6384517647769/20000000000000 : ℝ)^3289 := by
    have hnat : (2093177209 : ℕ)^4313*20000000000000^3289 ≤ 6384517647769^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093177209 5000000000 6384517647769 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5521271809/10000000000 : ℝ)^4313 ≤ (45890773179079/100000000000000 : ℝ)^3289 := by
    have hnat : (5521271809 : ℕ)^4313*100000000000000^3289 ≤ 45890773179079^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521271809 10000000000 45890773179079 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586038079/5000000000 : ℝ)^4313 ≤ (5546659641089/25000000000000 : ℝ)^3289 := by
    have hnat : (1586038079 : ℕ)^4313*25000000000000^3289 ≤ 5546659641089^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586038079 5000000000 5546659641089 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093177209/5000000000 : ℝ), (5521271809/10000000000 : ℝ), (1586038079/5000000000 : ℝ)] ![(6384517647769/20000000000000 : ℝ), (45890773179079/100000000000000 : ℝ), (5546659641089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093177209/5000000000 : ℝ)|^4313 ≤ (6384517647769/20000000000000 : ℝ)^3289
        have hw : |(2093177209/5000000000 : ℝ)|=(2093177209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5521271809/10000000000 : ℝ)|^4313 ≤ (45890773179079/100000000000000 : ℝ)^3289
        have hw : |(5521271809/10000000000 : ℝ)|=(5521271809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1586038079/5000000000 : ℝ)|^4313 ≤ (5546659641089/25000000000000 : ℝ)^3289
        have hw : |(1586038079/5000000000 : ℝ)|=(1586038079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1353_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (187/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3349/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (539/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^539 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^539*1^128 ≤ 0^128*1^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (539/128 : ℝ) ≤ (2110082786944001701/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^539 ≤ (2110082786944001701/100000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^539*100000000000000000000^128 ≤ 2110082786944001701^128*5^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2110082786944001701 100000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2110082786944001701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^539 := by
      have hnat : (1 : ℕ)^128*1^539 ≤ 1^539*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (102110082786944001701/100000000000000000000 : ℝ) ≤ (1004971137025627/1000000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (102110082786944001701/100000000000000000000 : ℝ)^128 ≤ (1004971137025627/1000000000000000 : ℝ)^539 := by
      have hnat : (102110082786944001701 : ℕ)^128*1000000000000000^539 ≤ 1004971137025627^539*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102110082786944001701 100000000000000000000 1004971137025627 1000000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004971137025627/1000000000000000 : ℝ)) (X := (102110082786944001701/100000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (52110082786944001701/50000000000000000000 : ℝ) ≤ (504971137025627/500000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (52110082786944001701/50000000000000000000 : ℝ)^128 ≤ (504971137025627/500000000000000 : ℝ)^539 := by
      have hnat : (52110082786944001701 : ℕ)^128*500000000000000^539 ≤ 504971137025627^539*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52110082786944001701 50000000000000000000 504971137025627 500000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (504971137025627/500000000000000 : ℝ)) (X := (52110082786944001701/50000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4971137025627/400000000000000 : ℝ)*(0 : ℝ))^(539/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(4971137025627/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2110082786944001701/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4971137025627/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(539/128 : ℝ) := by
    rw [show (1 : ℝ)+(4971137025627/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1004971137025627/1000000000000000 : ℝ) by norm_num, show 1+(2110082786944001701/100000000000000000000 : ℝ)+(0 : ℝ)=(102110082786944001701/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2110082786944001701/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4971137025627/400000000000000 : ℝ)*(2/5 : ℝ))^(539/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(4971137025627/400000000000000 : ℝ)*(2/5 : ℝ)=(504971137025627/500000000000000 : ℝ) by norm_num, show 1+2*(2110082786944001701/100000000000000000000 : ℝ)=(52110082786944001701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4971137025627/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4971137025627/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4971137025627/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4971137025627/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4971137025627/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4971137025627/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-56333163/312500000 : ℝ)*X 0 0+(2996089663/5000000000 : ℝ)*X 0 1+(4813526799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5500581103/10000000000 : ℝ)*X 1 0+(-2472068107/10000000000 : ℝ)*X 1 1+(4813527259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2750290461/5000000000 : ℝ)*X 2 0+(481352687/1000000000 : ℝ)*X 2 1+(-2472068817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2088552359/5000000000 : ℝ)*X 0 0+(776509517/2500000000 : ℝ)*X 0 1+(5585031629/10000000000 : ℝ)*X 0 2+(2088552359/5000000000 : ℝ)*X 1 0+(776509517/2500000000 : ℝ)*X 1 1+(5585031629/10000000000 : ℝ)*X 1 2+(2088552359/5000000000 : ℝ)*X 2 0+(776509517/2500000000 : ℝ)*X 2 1+(5585031629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-451765113/2500000000 : ℝ)*X 0 0+(75685037/156250000 : ℝ)*X 0 1+(2980390481/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5179291197/10000000000 : ℝ)*X 1 0+(-264963143/2000000000 : ℝ)*X 1 1+(1192156109/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5179291111/10000000000 : ℝ)*X 2 0+(2980390519/5000000000 : ℝ)*X 2 1+(-1324815059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2093177209/5000000000 : ℝ)*X 0 0+(5521271809/10000000000 : ℝ)*X 0 1+(1586038079/5000000000 : ℝ)*X 0 2+(2093177209/5000000000 : ℝ)*X 1 0+(5521271809/10000000000 : ℝ)*X 1 1+(1586038079/5000000000 : ℝ)*X 1 2+(2093177209/5000000000 : ℝ)*X 2 0+(5521271809/10000000000 : ℝ)*X 2 1+(1586038079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31978149051832556375019/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31935137/20000000000000 : ℝ)*(base1) + (1872948063/100000000000000 : ℝ)*(base19) + (1845029739/100000000000000 : ℝ)*(base23) + (74253321/25000000000000 : ℝ)*(upper3) + (26493099/25000000000000 : ℝ)*(upper5) + (125183374145367/20000000000000 : ℝ)*(major0) + (125183374145367/20000000000000 : ℝ)*(major1) + (125183374145367/20000000000000 : ℝ)*(major2) + (26513529485883/3125000000000 : ℝ)*(sp0) + (848436459424471/100000000000000 : ℝ)*(sp1) + (169687297468559/20000000000000 : ℝ)*(sp2) + (403391916718851/100000000000000 : ℝ)*(sp3) + (2774249981/50000000000000 : ℝ)*(sp4) + (3066202019/100000000000000 : ℝ)*(sp7) + (80679028519311/20000000000000 : ℝ)*(f.failure) + (424219166186267/50000000000000 : ℝ)*(f.sum) + (5427634960109/4000000000000000000000000000 : ℝ)*base65 + (83350720632109/8000000000000000000000000000 : ℝ)*base67 + (4642004168109/8000000000000000000000000000 : ℝ)*base69 + (25592058536109/8000000000000000000000000000 : ℝ)*base71 + (28688078952109/4000000000000000000000000000 : ℝ)*base73 + (19814947839891/8000000000000000000000000000 : ℝ)*base76 + (15889774720109/8000000000000000000000000000 : ℝ)*base77 + (10031871208109/8000000000000000000000000000 : ℝ)*base79 + (829608743891/4000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (6811647/2000000000000000000000 : ℝ)*base90 + (6811647/2000000000000000000000 : ℝ)*base92 + (6811647/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45930085173668561829093/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126665979/20000000000000 : ℝ)*(base19) + (870799233/100000000000000 : ℝ)*(base23) + (63503641/25000000000000 : ℝ)*(base39) + (957361/2000000000000 : ℝ)*(upper3) + (21505149/12500000000000 : ℝ)*(upper5) + (330245163747547/50000000000000 : ℝ)*(major0) + (330245163747547/50000000000000 : ℝ)*(major1) + (66049007348053/10000000000000 : ℝ)*(major2) + (743574509/50000000000000 : ℝ)*(sp1) + (389584371/25000000000000 : ℝ)*(sp2) + (895302969782267/100000000000000 : ℝ)*(sp4) + (447650424651677/50000000000000 : ℝ)*(sp5) + (447650397330057/50000000000000 : ℝ)*(sp6) + (425677278093067/100000000000000 : ℝ)*(sp7) + (425677278093067/100000000000000 : ℝ)*(f.failure) + (27978225743651/3125000000000 : ℝ)*(f.sum) + (8857540320469/5000000000000000000000000000 : ℝ)*base66 + (5117023718231/4000000000000000000000000000 : ℝ)*base67 + (3270348586969/20000000000000000000000000000 : ℝ)*base69 + (9387236837769/4000000000000000000000000000 : ℝ)*base72 + (9813180454531/5000000000000000000000000000 : ℝ)*base73 + (58355773826969/20000000000000000000000000000 : ℝ)*base75 + (15336640773031/20000000000000000000000000000 : ℝ)*base78 + (18712934913031/20000000000000000000000000000 : ℝ)*base80 + (10729263066969/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (76607941/10000000000000000000000 : ℝ)*base89 + (76607941/10000000000000000000000 : ℝ)*base91 + (76607941/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1353_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (187/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3349/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1353_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1353_s1_0 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99294621/500000000 : ℝ)*x 0 + (5637233181/10000000000 : ℝ)*x 1 + (2525559097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99294621/500000000 : ℝ)^4313 ≤ (12005511458017/100000000000000 : ℝ)^3289 := by
    have hnat : (99294621 : ℕ)^4313*100000000000000^3289 ≤ 12005511458017^3289*500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99294621 500000000 12005511458017 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5637233181/10000000000 : ℝ)^4313 ≤ (47158792933467/100000000000000 : ℝ)^3289 := by
    have hnat : (5637233181 : ℕ)^4313*100000000000000^3289 ≤ 47158792933467^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637233181 10000000000 47158792933467 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2525559097/5000000000 : ℝ)^4313 ≤ (40835695591089/100000000000000 : ℝ)^3289 := by
    have hnat : (2525559097 : ℕ)^4313*100000000000000^3289 ≤ 40835695591089^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525559097 5000000000 40835695591089 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99294621/500000000 : ℝ), (5637233181/10000000000 : ℝ), (2525559097/5000000000 : ℝ)] ![(12005511458017/100000000000000 : ℝ), (47158792933467/100000000000000 : ℝ), (40835695591089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99294621/500000000 : ℝ)|^4313 ≤ (12005511458017/100000000000000 : ℝ)^3289
        have hw : |(-99294621/500000000 : ℝ)|=(99294621/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5637233181/10000000000 : ℝ)|^4313 ≤ (47158792933467/100000000000000 : ℝ)^3289
        have hw : |(5637233181/10000000000 : ℝ)|=(5637233181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2525559097/5000000000 : ℝ)|^4313 ≤ (40835695591089/100000000000000 : ℝ)^3289
        have hw : |(2525559097/5000000000 : ℝ)|=(2525559097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s1_1 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080914357/2000000000 : ℝ)*x 0 + (-574591159/2500000000 : ℝ)*x 1 + (808179/1600000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080914357/2000000000 : ℝ)^4313 ≤ (11155755199387/25000000000000 : ℝ)^3289 := by
    have hnat : (1080914357 : ℕ)^4313*25000000000000^3289 ≤ 11155755199387^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080914357 2000000000 11155755199387 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574591159/2500000000 : ℝ)^4313 ≤ (14541277707571/100000000000000 : ℝ)^3289 := by
    have hnat : (574591159 : ℕ)^4313*100000000000000^3289 ≤ 14541277707571^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574591159 2500000000 14541277707571 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808179/1600000 : ℝ)^4313 ≤ (40835701485533/100000000000000 : ℝ)^3289 := by
    have hnat : (808179 : ℕ)^4313*100000000000000^3289 ≤ 40835701485533^3289*1600000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808179 1600000 40835701485533 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080914357/2000000000 : ℝ), (-574591159/2500000000 : ℝ), (808179/1600000 : ℝ)] ![(11155755199387/25000000000000 : ℝ), (14541277707571/100000000000000 : ℝ), (40835701485533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080914357/2000000000 : ℝ)|^4313 ≤ (11155755199387/25000000000000 : ℝ)^3289
        have hw : |(1080914357/2000000000 : ℝ)|=(1080914357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-574591159/2500000000 : ℝ)|^4313 ≤ (14541277707571/100000000000000 : ℝ)^3289
        have hw : |(-574591159/2500000000 : ℝ)|=(574591159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(808179/1600000 : ℝ)|^4313 ≤ (40835701485533/100000000000000 : ℝ)^3289
        have hw : |(808179/1600000 : ℝ)|=(808179/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s1_2 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270228589/500000000 : ℝ)*x 0 + (5051118293/10000000000 : ℝ)*x 1 + (-2298365227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270228589/500000000 : ℝ)^4313 ≤ (44623020743413/100000000000000 : ℝ)^3289 := by
    have hnat : (270228589 : ℕ)^4313*100000000000000^3289 ≤ 44623020743413^3289*500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270228589 500000000 44623020743413 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5051118293/10000000000 : ℝ)^4313 ≤ (40835696640639/100000000000000 : ℝ)^3289 := by
    have hnat : (5051118293 : ℕ)^4313*100000000000000^3289 ≤ 40835696640639^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5051118293 10000000000 40835696640639 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2298365227/10000000000 : ℝ)^4313 ≤ (14541282610851/100000000000000 : ℝ)^3289 := by
    have hnat : (2298365227 : ℕ)^4313*100000000000000^3289 ≤ 14541282610851^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298365227 10000000000 14541282610851 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270228589/500000000 : ℝ), (5051118293/10000000000 : ℝ), (-2298365227/10000000000 : ℝ)] ![(44623020743413/100000000000000 : ℝ), (40835696640639/100000000000000 : ℝ), (14541282610851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270228589/500000000 : ℝ)|^4313 ≤ (44623020743413/100000000000000 : ℝ)^3289
        have hw : |(270228589/500000000 : ℝ)|=(270228589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5051118293/10000000000 : ℝ)|^4313 ≤ (40835696640639/100000000000000 : ℝ)^3289
        have hw : |(5051118293/10000000000 : ℝ)|=(5051118293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2298365227/10000000000 : ℝ)|^4313 ≤ (14541282610851/100000000000000 : ℝ)^3289
        have hw : |(-2298365227/10000000000 : ℝ)|=(2298365227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s1_3 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4290344833/10000000000 : ℝ)*x 0 + (3714810671/10000000000 : ℝ)*x 1 + (12368877/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4290344833/10000000000 : ℝ)^4313 ≤ (32966437276033/100000000000000 : ℝ)^3289 := by
    have hnat : (4290344833 : ℕ)^4313*100000000000000^3289 ≤ 32966437276033^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290344833 10000000000 32966437276033 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3714810671/10000000000 : ℝ)^4313 ≤ (27292317408313/100000000000000 : ℝ)^3289 := by
    have hnat : (3714810671 : ℕ)^4313*100000000000000^3289 ≤ 27292317408313^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714810671 10000000000 27292317408313 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12368877/25000000 : ℝ)^4313 ≤ (19870622651127/50000000000000 : ℝ)^3289 := by
    have hnat : (12368877 : ℕ)^4313*50000000000000^3289 ≤ 19870622651127^3289*25000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12368877 25000000 19870622651127 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4290344833/10000000000 : ℝ), (3714810671/10000000000 : ℝ), (12368877/25000000 : ℝ)] ![(32966437276033/100000000000000 : ℝ), (27292317408313/100000000000000 : ℝ), (19870622651127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4290344833/10000000000 : ℝ)|^4313 ≤ (32966437276033/100000000000000 : ℝ)^3289
        have hw : |(4290344833/10000000000 : ℝ)|=(4290344833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3714810671/10000000000 : ℝ)|^4313 ≤ (27292317408313/100000000000000 : ℝ)^3289
        have hw : |(3714810671/10000000000 : ℝ)|=(3714810671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12368877/25000000 : ℝ)|^4313 ≤ (19870622651127/50000000000000 : ℝ)^3289
        have hw : |(12368877/25000000 : ℝ)|=(12368877/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s1_4 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-79456369/400000000 : ℝ)*x 0 + (5058410783/10000000000 : ℝ)*x 1 + (1407452263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79456369/400000000 : ℝ)^4313 ≤ (12009608636019/100000000000000 : ℝ)^3289 := by
    have hnat : (79456369 : ℕ)^4313*100000000000000^3289 ≤ 12009608636019^3289*400000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79456369 400000000 12009608636019 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5058410783/10000000000 : ℝ)^4313 ≤ (40913025467129/100000000000000 : ℝ)^3289 := by
    have hnat : (5058410783 : ℕ)^4313*100000000000000^3289 ≤ 40913025467129^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5058410783 10000000000 40913025467129 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1407452263/2500000000 : ℝ)^4313 ≤ (47077365883283/100000000000000 : ℝ)^3289 := by
    have hnat : (1407452263 : ℕ)^4313*100000000000000^3289 ≤ 47077365883283^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407452263 2500000000 47077365883283 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79456369/400000000 : ℝ), (5058410783/10000000000 : ℝ), (1407452263/2500000000 : ℝ)] ![(12009608636019/100000000000000 : ℝ), (40913025467129/100000000000000 : ℝ), (47077365883283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79456369/400000000 : ℝ)|^4313 ≤ (12009608636019/100000000000000 : ℝ)^3289
        have hw : |(-79456369/400000000 : ℝ)|=(79456369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5058410783/10000000000 : ℝ)|^4313 ≤ (40913025467129/100000000000000 : ℝ)^3289
        have hw : |(5058410783/10000000000 : ℝ)|=(5058410783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1407452263/2500000000 : ℝ)|^4313 ≤ (47077365883283/100000000000000 : ℝ)^3289
        have hw : |(1407452263/2500000000 : ℝ)|=(1407452263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s1_5 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626172147/5000000000 : ℝ)*x 0 + (-429918533/2500000000 : ℝ)*x 1 + (2814904553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626172147/5000000000 : ℝ)^4313 ≤ (21491054181231/50000000000000 : ℝ)^3289 := by
    have hnat : (2626172147 : ℕ)^4313*50000000000000^3289 ≤ 21491054181231^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626172147 5000000000 21491054181231 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429918533/2500000000 : ℝ)^4313 ≤ (2485131288089/25000000000000 : ℝ)^3289 := by
    have hnat : (429918533 : ℕ)^4313*25000000000000^3289 ≤ 2485131288089^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429918533 2500000000 2485131288089 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2814904553/5000000000 : ℝ)^4313 ≤ (47077366475427/100000000000000 : ℝ)^3289 := by
    have hnat : (2814904553 : ℕ)^4313*100000000000000^3289 ≤ 47077366475427^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814904553 5000000000 47077366475427 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626172147/5000000000 : ℝ), (-429918533/2500000000 : ℝ), (2814904553/5000000000 : ℝ)] ![(21491054181231/50000000000000 : ℝ), (2485131288089/25000000000000 : ℝ), (47077366475427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626172147/5000000000 : ℝ)|^4313 ≤ (21491054181231/50000000000000 : ℝ)^3289
        have hw : |(2626172147/5000000000 : ℝ)|=(2626172147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429918533/2500000000 : ℝ)|^4313 ≤ (2485131288089/25000000000000 : ℝ)^3289
        have hw : |(-429918533/2500000000 : ℝ)|=(429918533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2814904553/5000000000 : ℝ)|^4313 ≤ (47077366475427/100000000000000 : ℝ)^3289
        have hw : |(2814904553/5000000000 : ℝ)|=(2814904553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s1_6 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525234419/1000000000 : ℝ)*x 0 + (2814904591/5000000000 : ℝ)*x 1 + (-171967417/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525234419/1000000000 : ℝ)^4313 ≤ (10745526811603/25000000000000 : ℝ)^3289 := by
    have hnat : (525234419 : ℕ)^4313*25000000000000^3289 ≤ 10745526811603^3289*1000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525234419 1000000000 10745526811603 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2814904591/5000000000 : ℝ)^4313 ≤ (2942335456801/6250000000000 : ℝ)^3289 := by
    have hnat : (2814904591 : ℕ)^4313*6250000000000^3289 ≤ 2942335456801^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814904591 5000000000 2942335456801 6250000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171967417/1000000000 : ℝ)^4313 ≤ (4970262720201/50000000000000 : ℝ)^3289 := by
    have hnat : (171967417 : ℕ)^4313*50000000000000^3289 ≤ 4970262720201^3289*1000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171967417 1000000000 4970262720201 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525234419/1000000000 : ℝ), (2814904591/5000000000 : ℝ), (-171967417/1000000000 : ℝ)] ![(10745526811603/25000000000000 : ℝ), (2942335456801/6250000000000 : ℝ), (4970262720201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525234419/1000000000 : ℝ)|^4313 ≤ (10745526811603/25000000000000 : ℝ)^3289
        have hw : |(525234419/1000000000 : ℝ)|=(525234419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2814904591/5000000000 : ℝ)|^4313 ≤ (2942335456801/6250000000000 : ℝ)^3289
        have hw : |(2814904591/5000000000 : ℝ)|=(2814904591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-171967417/1000000000 : ℝ)|^4313 ≤ (4970262720201/50000000000000 : ℝ)^3289
        have hw : |(-171967417/1000000000 : ℝ)|=(171967417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s1_7 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291432271/10000000000 : ℝ)*x 0 + (4932213727/10000000000 : ℝ)*x 1 + (746084669/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291432271/10000000000 : ℝ)^4313 ≤ (206108718227/625000000000 : ℝ)^3289 := by
    have hnat : (4291432271 : ℕ)^4313*625000000000^3289 ≤ 206108718227^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291432271 10000000000 206108718227 625000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4932213727/10000000000 : ℝ)^4313 ≤ (39579772455299/100000000000000 : ℝ)^3289 := by
    have hnat : (4932213727 : ℕ)^4313*100000000000000^3289 ≤ 39579772455299^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4932213727 10000000000 39579772455299 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (746084669/2000000000 : ℝ)^4313 ≤ (27442832614537/100000000000000 : ℝ)^3289 := by
    have hnat : (746084669 : ℕ)^4313*100000000000000^3289 ≤ 27442832614537^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746084669 2000000000 27442832614537 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291432271/10000000000 : ℝ), (4932213727/10000000000 : ℝ), (746084669/2000000000 : ℝ)] ![(206108718227/625000000000 : ℝ), (39579772455299/100000000000000 : ℝ), (27442832614537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291432271/10000000000 : ℝ)|^4313 ≤ (206108718227/625000000000 : ℝ)^3289
        have hw : |(4291432271/10000000000 : ℝ)|=(4291432271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4932213727/10000000000 : ℝ)|^4313 ≤ (39579772455299/100000000000000 : ℝ)^3289
        have hw : |(4932213727/10000000000 : ℝ)|=(4932213727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(746084669/2000000000 : ℝ)|^4313 ≤ (27442832614537/100000000000000 : ℝ)^3289
        have hw : |(746084669/2000000000 : ℝ)|=(746084669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1353_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3349/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (187/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (6991/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19379/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3349/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (187/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3349/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (187/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3349/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (187/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3349/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (187/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3349/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (187/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3349/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (187/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (187/12500 : ℝ) ^ (539/128 : ℝ) ≤ (1032098178199/50000000000000000000 : ℝ) := by
    have hpowers : (187/12500 : ℝ)^539 ≤ (1032098178199/50000000000000000000 : ℝ)^128 := by
      have hnat : (187 : ℕ)^539*50000000000000000000^128 ≤ 1032098178199^128*12500^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        187 12500 1032098178199 50000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (187/12500 : ℝ)) (X := (1032098178199/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3349/12500 : ℝ) ^ (539/128 : ℝ) ≤ (195135091113891627/50000000000000000000 : ℝ) := by
    have hpowers : (3349/12500 : ℝ)^539 ≤ (195135091113891627/50000000000000000000 : ℝ)^128 := by
      have hnat : (3349 : ℕ)^539*50000000000000000000^128 ≤ 195135091113891627^128*12500^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3349 12500 195135091113891627 50000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3349/12500 : ℝ)) (X := (195135091113891627/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000001032098178199/25000000000000000000 : ℝ) ≤ (1250000012254969/1250000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (25000001032098178199/25000000000000000000 : ℝ)^128 ≤ (1250000012254969/1250000000000000 : ℝ)^539 := by
      have hnat : (25000001032098178199 : ℕ)^128*1250000000000000^539 ≤ 1250000012254969^539*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000001032098178199 25000000000000000000 1250000012254969 1250000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000012254969/1250000000000000 : ℝ)) (X := (25000001032098178199/25000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25097568061606034913/25000000000000000000 : ℝ) ≤ (1251156787727063/1250000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (25097568061606034913/25000000000000000000 : ℝ)^128 ≤ (1251156787727063/1250000000000000 : ℝ)^539 := by
      have hnat : (25097568061606034913 : ℕ)^128*1250000000000000^539 ≤ 1251156787727063^539*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25097568061606034913 25000000000000000000 1251156787727063 1250000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251156787727063/1250000000000000 : ℝ)) (X := (25097568061606034913/25000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25195135091113891627/25000000000000000000 : ℝ) ≤ (1252313563199157/1250000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (25195135091113891627/25000000000000000000 : ℝ)^128 ≤ (1252313563199157/1250000000000000 : ℝ)^539 := by
      have hnat : (25195135091113891627 : ℕ)^128*1250000000000000^539 ≤ 1252313563199157^539*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25195135091113891627 25000000000000000000 1252313563199157 1250000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252313563199157/1250000000000000 : ℝ)) (X := (25195135091113891627/25000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1032098178199/50000000000000000000 : ℝ) ≤ ((116237276609519083/116250000000000000 : ℝ)+2*(578387736047/158100000000000 : ℝ)*(187/12500 : ℝ))^(539/128 : ℝ) := by
    rw [show (116237276609519083/116250000000000000 : ℝ)+2*(578387736047/158100000000000 : ℝ)*(187/12500 : ℝ)=(1250000012254969/1250000000000000 : ℝ) by norm_num, show 1+2*(1032098178199/50000000000000000000 : ℝ)=(25000001032098178199/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(195135091113891627/50000000000000000000 : ℝ)+(1032098178199/50000000000000000000 : ℝ) ≤ ((116237276609519083/116250000000000000 : ℝ)+(578387736047/158100000000000 : ℝ)*((3349/12500 : ℝ)+(187/12500 : ℝ)))^(539/128 : ℝ) := by
    rw [show (116237276609519083/116250000000000000 : ℝ)+(578387736047/158100000000000 : ℝ)*((3349/12500 : ℝ)+(187/12500 : ℝ))=(1251156787727063/1250000000000000 : ℝ) by norm_num, show 1+(195135091113891627/50000000000000000000 : ℝ)+(1032098178199/50000000000000000000 : ℝ)=(25097568061606034913/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(195135091113891627/50000000000000000000 : ℝ) ≤ ((116237276609519083/116250000000000000 : ℝ)+2*(578387736047/158100000000000 : ℝ)*(3349/12500 : ℝ))^(539/128 : ℝ) := by
    rw [show (116237276609519083/116250000000000000 : ℝ)+2*(578387736047/158100000000000 : ℝ)*(3349/12500 : ℝ)=(1252313563199157/1250000000000000 : ℝ) by norm_num, show 1+2*(195135091113891627/50000000000000000000 : ℝ)=(25195135091113891627/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (116237276609519083/116250000000000000 : ℝ)*(X 1 0+X 2 0)+(578387736047/158100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (187/12500 : ℝ)) (hi := (3349/12500 : ℝ)) (c := (116237276609519083/116250000000000000 : ℝ)) (alpha := (578387736047/158100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (116237276609519083/116250000000000000 : ℝ)*(X 0 1+X 2 1)+(578387736047/158100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (187/12500 : ℝ)) (hi := (3349/12500 : ℝ)) (c := (116237276609519083/116250000000000000 : ℝ)) (alpha := (578387736047/158100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (116237276609519083/116250000000000000 : ℝ)*(X 0 2+X 1 2)+(578387736047/158100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (187/12500 : ℝ)) (hi := (3349/12500 : ℝ)) (c := (116237276609519083/116250000000000000 : ℝ)) (alpha := (578387736047/158100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-99294621/500000000 : ℝ)*X 0 0+(5637233181/10000000000 : ℝ)*X 0 1+(2525559097/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1080914357/2000000000 : ℝ)*X 1 0+(-574591159/2500000000 : ℝ)*X 1 1+(808179/1600000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((270228589/500000000 : ℝ)*X 2 0+(5051118293/10000000000 : ℝ)*X 2 1+(-2298365227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4290344833/10000000000 : ℝ)*X 0 0+(3714810671/10000000000 : ℝ)*X 0 1+(12368877/25000000 : ℝ)*X 0 2+(4290344833/10000000000 : ℝ)*X 1 0+(3714810671/10000000000 : ℝ)*X 1 1+(12368877/25000000 : ℝ)*X 1 2+(4290344833/10000000000 : ℝ)*X 2 0+(3714810671/10000000000 : ℝ)*X 2 1+(12368877/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-79456369/400000000 : ℝ)*X 0 0+(5058410783/10000000000 : ℝ)*X 0 1+(1407452263/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2626172147/5000000000 : ℝ)*X 1 0+(-429918533/2500000000 : ℝ)*X 1 1+(2814904553/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525234419/1000000000 : ℝ)*X 2 0+(2814904591/5000000000 : ℝ)*X 2 1+(-171967417/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4291432271/10000000000 : ℝ)*X 0 0+(4932213727/10000000000 : ℝ)*X 0 1+(746084669/2000000000 : ℝ)*X 0 2+(4291432271/10000000000 : ℝ)*X 1 0+(4932213727/10000000000 : ℝ)*X 1 1+(746084669/2000000000 : ℝ)*X 1 2+(4291432271/10000000000 : ℝ)*X 2 0+(4932213727/10000000000 : ℝ)*X 2 1+(746084669/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24420880702792045820307/2635000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39417013/100000000000000 : ℝ)*(base1) + (1526549293/100000000000000 : ℝ)*(base19) + (1524970843/100000000000000 : ℝ)*(base23) + (70671809/25000000000000 : ℝ)*(upper3) + (3688003/10000000000000 : ℝ)*(upper5) + (314672632834763/25000000000000 : ℝ)*(major0) + (314672632834763/25000000000000 : ℝ)*(major1) + (314672632834763/25000000000000 : ℝ)*(major2) + (53317560390557/3125000000000 : ℝ)*(sp0) + (106635614477321/6250000000000 : ℝ)*(sp1) + (341233966643117/20000000000000 : ℝ)*(sp2) + (162240904107179/20000000000000 : ℝ)*(sp3) + (4732552809/50000000000000 : ℝ)*(sp4) + (967121843/20000000000000 : ℝ)*(sp7) + (405604697781061/50000000000000 : ℝ)*(f.failure) + (426542839546607/25000000000000 : ℝ)*(f.sum) + (13175743286953/3952500000000000000000000000 : ℝ)*base66 + (60111738551395969/16468750000000000000000000000000 : ℝ)*base68 + (71553492197572781/16468750000000000000000000000000 : ℝ)*base69 + (10242036055895969/16468750000000000000000000000000 : ℝ)*base72 + (26973405712963/3952500000000000000000000000 : ℝ)*base74 + (24321575809177219/16468750000000000000000000000000 : ℝ)*base76 + (125404741269729031/16468750000000000000000000000000 : ℝ)*base77 + (31816504998322781/16468750000000000000000000000000 : ℝ)*base79 + (169589694733/247031250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (7941397/5000000000000000000000 : ℝ)*base90 + (7941397/5000000000000000000000 : ℝ)*base92 + (7941397/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71370308805076659458133/31250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26603971/100000000000000 : ℝ)*(base1) + (119215331/25000000000000 : ℝ)*(base19) + (87967599/20000000000000 : ℝ)*(base23) + (54686473/100000000000000 : ℝ)*(upper3) + (45901937/100000000000000 : ℝ)*(upper5) + (645546141243873/50000000000000 : ℝ)*(major0) + (645546141243873/50000000000000 : ℝ)*(major1) + (645546141243873/50000000000000 : ℝ)*(major2) + (1280339297/50000000000000 : ℝ)*(sp1) + (2478893553/100000000000000 : ℝ)*(sp2) + (1750092619933653/100000000000000 : ℝ)*(sp4) + (1750089555789763/100000000000000 : ℝ)*(sp5) + (875044837299067/50000000000000 : ℝ)*(sp6) + (1664183737827/200000000000 : ℝ)*(sp7) + (832091895517471/100000000000000 : ℝ)*(f.failure) + (875046296664841/50000000000000 : ℝ)*(f.sum) + (177540620541/85000000000000000000000000 : ℝ)*base66 + (11167133166180471/1062500000000000000000000000000 : ℝ)*base67 + (6938075405617971/1062500000000000000000000000000 : ℝ)*base69 + (11532318333617971/1062500000000000000000000000000 : ℝ)*base71 + (88850738333/42500000000000000000000000 : ℝ)*base74 + (10829808457242971/1062500000000000000000000000000 : ℝ)*base75 + (5237066196367971/1062500000000000000000000000000 : ℝ)*base77 + (2846110103305471/1062500000000000000000000000000 : ℝ)*base79 + (344613867731/85000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (64301967/10000000000000000000000 : ℝ)*base90 + (64301967/10000000000000000000000 : ℝ)*base92 + (64301967/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1353_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3349/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (187/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6991/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19379/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1353_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1353_s2_0 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-506274741/2500000000 : ℝ)*x 0 + (684596433/1250000000 : ℝ)*x 1 + (5186450229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (506274741/2500000000 : ℝ)^4313 ≤ (12317275337153/100000000000000 : ℝ)^3289 := by
    have hnat : (506274741 : ℕ)^4313*100000000000000^3289 ≤ 12317275337153^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506274741 2500000000 12317275337153 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684596433/1250000000 : ℝ)^4313 ≤ (9081271329123/20000000000000 : ℝ)^3289 := by
    have hnat : (684596433 : ℕ)^4313*20000000000000^3289 ≤ 9081271329123^3289*1250000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684596433 1250000000 9081271329123 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5186450229/10000000000 : ℝ)^4313 ≤ (4227636800709/10000000000000 : ℝ)^3289 := by
    have hnat : (5186450229 : ℕ)^4313*10000000000000^3289 ≤ 4227636800709^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186450229 10000000000 4227636800709 10000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-506274741/2500000000 : ℝ), (684596433/1250000000 : ℝ), (5186450229/10000000000 : ℝ)] ![(12317275337153/100000000000000 : ℝ), (9081271329123/20000000000000 : ℝ), (4227636800709/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-506274741/2500000000 : ℝ)|^4313 ≤ (12317275337153/100000000000000 : ℝ)^3289
        have hw : |(-506274741/2500000000 : ℝ)|=(506274741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684596433/1250000000 : ℝ)|^4313 ≤ (9081271329123/20000000000000 : ℝ)^3289
        have hw : |(684596433/1250000000 : ℝ)|=(684596433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5186450229/10000000000 : ℝ)|^4313 ≤ (4227636800709/10000000000000 : ℝ)^3289
        have hw : |(5186450229/10000000000 : ℝ)|=(5186450229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s2_1 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682591073/5000000000 : ℝ)*x 0 + (-1087510201/5000000000 : ℝ)*x 1 + (5186450611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682591073/5000000000 : ℝ)^4313 ≤ (44197028817841/100000000000000 : ℝ)^3289 := by
    have hnat : (2682591073 : ℕ)^4313*100000000000000^3289 ≤ 44197028817841^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682591073 5000000000 44197028817841 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087510201/5000000000 : ℝ)^4313 ≤ (541063963007/4000000000000 : ℝ)^3289 := by
    have hnat : (1087510201 : ℕ)^4313*4000000000000^3289 ≤ 541063963007^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087510201 5000000000 541063963007 4000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5186450611/10000000000 : ℝ)^4313 ≤ (8455274418069/20000000000000 : ℝ)^3289 := by
    have hnat : (5186450611 : ℕ)^4313*20000000000000^3289 ≤ 8455274418069^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186450611 10000000000 8455274418069 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682591073/5000000000 : ℝ), (-1087510201/5000000000 : ℝ), (5186450611/10000000000 : ℝ)] ![(44197028817841/100000000000000 : ℝ), (541063963007/4000000000000 : ℝ), (8455274418069/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682591073/5000000000 : ℝ)|^4313 ≤ (44197028817841/100000000000000 : ℝ)^3289
        have hw : |(2682591073/5000000000 : ℝ)|=(2682591073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087510201/5000000000 : ℝ)|^4313 ≤ (541063963007/4000000000000 : ℝ)^3289
        have hw : |(-1087510201/5000000000 : ℝ)|=(1087510201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5186450611/10000000000 : ℝ)|^4313 ≤ (8455274418069/20000000000000 : ℝ)^3289
        have hw : |(5186450611/10000000000 : ℝ)|=(5186450611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s2_2 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670647777/1250000000 : ℝ)*x 0 + (5186450529/10000000000 : ℝ)*x 1 + (-2175020417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670647777/1250000000 : ℝ)^4313 ≤ (345289293547/781250000000 : ℝ)^3289 := by
    have hnat : (670647777 : ℕ)^4313*781250000000^3289 ≤ 345289293547^3289*1250000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670647777 1250000000 345289293547 781250000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186450529/10000000000 : ℝ)^4313 ≤ (8455274242767/20000000000000 : ℝ)^3289 := by
    have hnat : (5186450529 : ℕ)^4313*20000000000000^3289 ≤ 8455274242767^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186450529 10000000000 8455274242767 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175020417/10000000000 : ℝ)^4313 ≤ (2705319839501/20000000000000 : ℝ)^3289 := by
    have hnat : (2175020417 : ℕ)^4313*20000000000000^3289 ≤ 2705319839501^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175020417 10000000000 2705319839501 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670647777/1250000000 : ℝ), (5186450529/10000000000 : ℝ), (-2175020417/10000000000 : ℝ)] ![(345289293547/781250000000 : ℝ), (8455274242767/20000000000000 : ℝ), (2705319839501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670647777/1250000000 : ℝ)|^4313 ≤ (345289293547/781250000000 : ℝ)^3289
        have hw : |(670647777/1250000000 : ℝ)|=(670647777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186450529/10000000000 : ℝ)|^4313 ≤ (8455274242767/20000000000000 : ℝ)^3289
        have hw : |(5186450529/10000000000 : ℝ)|=(5186450529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175020417/10000000000 : ℝ)|^4313 ≤ (2705319839501/20000000000000 : ℝ)^3289
        have hw : |(-2175020417/10000000000 : ℝ)|=(2175020417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s2_3 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158897889/5000000000 : ℝ)*x 0 + (4022501841/10000000000 : ℝ)*x 1 + (4633117583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158897889/5000000000 : ℝ)^4313 ≤ (6648662541509/20000000000000 : ℝ)^3289 := by
    have hnat : (2158897889 : ℕ)^4313*20000000000000^3289 ≤ 6648662541509^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158897889 5000000000 6648662541509 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4022501841/10000000000 : ℝ)^4313 ≤ (15147110349431/50000000000000 : ℝ)^3289 := by
    have hnat : (4022501841 : ℕ)^4313*50000000000000^3289 ≤ 15147110349431^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022501841 10000000000 15147110349431 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4633117583/10000000000 : ℝ)^4313 ≤ (18231233287109/50000000000000 : ℝ)^3289 := by
    have hnat : (4633117583 : ℕ)^4313*50000000000000^3289 ≤ 18231233287109^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4633117583 10000000000 18231233287109 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158897889/5000000000 : ℝ), (4022501841/10000000000 : ℝ), (4633117583/10000000000 : ℝ)] ![(6648662541509/20000000000000 : ℝ), (15147110349431/50000000000000 : ℝ), (18231233287109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158897889/5000000000 : ℝ)|^4313 ≤ (6648662541509/20000000000000 : ℝ)^3289
        have hw : |(2158897889/5000000000 : ℝ)|=(2158897889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4022501841/10000000000 : ℝ)|^4313 ≤ (15147110349431/50000000000000 : ℝ)^3289
        have hw : |(4022501841/10000000000 : ℝ)|=(4022501841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4633117583/10000000000 : ℝ)|^4313 ≤ (18231233287109/50000000000000 : ℝ)^3289
        have hw : |(4633117583/10000000000 : ℝ)|=(4633117583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s2_4 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025161787/10000000000 : ℝ)*x 0 + (518824947/1000000000 : ℝ)*x 1 + (2737478099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025161787/10000000000 : ℝ)^4313 ≤ (153972205181/1250000000000 : ℝ)^3289 := by
    have hnat : (2025161787 : ℕ)^4313*1250000000000^3289 ≤ 153972205181^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025161787 10000000000 153972205181 1250000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518824947/1000000000 : ℝ)^4313 ≤ (42295601396729/100000000000000 : ℝ)^3289 := by
    have hnat : (518824947 : ℕ)^4313*100000000000000^3289 ≤ 42295601396729^3289*1000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518824947 1000000000 42295601396729 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2737478099/5000000000 : ℝ)^4313 ≤ (5673327771853/12500000000000 : ℝ)^3289 := by
    have hnat : (2737478099 : ℕ)^4313*12500000000000^3289 ≤ 5673327771853^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737478099 5000000000 5673327771853 12500000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025161787/10000000000 : ℝ), (518824947/1000000000 : ℝ), (2737478099/5000000000 : ℝ)] ![(153972205181/1250000000000 : ℝ), (42295601396729/100000000000000 : ℝ), (5673327771853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025161787/10000000000 : ℝ)|^4313 ≤ (153972205181/1250000000000 : ℝ)^3289
        have hw : |(-2025161787/10000000000 : ℝ)|=(2025161787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518824947/1000000000 : ℝ)|^4313 ≤ (42295601396729/100000000000000 : ℝ)^3289
        have hw : |(518824947/1000000000 : ℝ)|=(518824947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2737478099/5000000000 : ℝ)|^4313 ≤ (5673327771853/12500000000000 : ℝ)^3289
        have hw : |(2737478099/5000000000 : ℝ)|=(2737478099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s2_5 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290263341/10000000000 : ℝ)*x 0 + (-47162863/250000000 : ℝ)*x 1 + (684369521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290263341/10000000000 : ℝ)^4313 ≤ (8677896702081/20000000000000 : ℝ)^3289 := by
    have hnat : (5290263341 : ℕ)^4313*20000000000000^3289 ≤ 8677896702081^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290263341 10000000000 8677896702081 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47162863/250000000 : ℝ)^4313 ≤ (5611947310757/50000000000000 : ℝ)^3289 := by
    have hnat : (47162863 : ℕ)^4313*50000000000000^3289 ≤ 5611947310757^3289*250000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47162863 250000000 5611947310757 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684369521/1250000000 : ℝ)^4313 ≤ (45386621848699/100000000000000 : ℝ)^3289 := by
    have hnat : (684369521 : ℕ)^4313*100000000000000^3289 ≤ 45386621848699^3289*1250000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684369521 1250000000 45386621848699 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290263341/10000000000 : ℝ), (-47162863/250000000 : ℝ), (684369521/1250000000 : ℝ)] ![(8677896702081/20000000000000 : ℝ), (5611947310757/50000000000000 : ℝ), (45386621848699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290263341/10000000000 : ℝ)|^4313 ≤ (8677896702081/20000000000000 : ℝ)^3289
        have hw : |(5290263341/10000000000 : ℝ)|=(5290263341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47162863/250000000 : ℝ)|^4313 ≤ (5611947310757/50000000000000 : ℝ)^3289
        have hw : |(-47162863/250000000 : ℝ)|=(47162863/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684369521/1250000000 : ℝ)|^4313 ≤ (45386621848699/100000000000000 : ℝ)^3289
        have hw : |(684369521/1250000000 : ℝ)|=(684369521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s2_6 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211610533/400000000 : ℝ)*x 0 + (1368739051/2500000000 : ℝ)*x 1 + (-1886514493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211610533/400000000 : ℝ)^4313 ≤ (542368541729/1250000000000 : ℝ)^3289 := by
    have hnat : (211610533 : ℕ)^4313*1250000000000^3289 ≤ 542368541729^3289*400000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211610533 400000000 542368541729 1250000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368739051/2500000000 : ℝ)^4313 ≤ (45386622240049/100000000000000 : ℝ)^3289 := by
    have hnat : (1368739051 : ℕ)^4313*100000000000000^3289 ≤ 45386622240049^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368739051 2500000000 45386622240049 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1886514493/10000000000 : ℝ)^4313 ≤ (11223894410863/100000000000000 : ℝ)^3289 := by
    have hnat : (1886514493 : ℕ)^4313*100000000000000^3289 ≤ 11223894410863^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886514493 10000000000 11223894410863 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211610533/400000000 : ℝ), (1368739051/2500000000 : ℝ), (-1886514493/10000000000 : ℝ)] ![(542368541729/1250000000000 : ℝ), (45386622240049/100000000000000 : ℝ), (11223894410863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211610533/400000000 : ℝ)|^4313 ≤ (542368541729/1250000000000 : ℝ)^3289
        have hw : |(211610533/400000000 : ℝ)|=(211610533/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368739051/2500000000 : ℝ)|^4313 ≤ (45386622240049/100000000000000 : ℝ)^3289
        have hw : |(1368739051/2500000000 : ℝ)|=(1368739051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1886514493/10000000000 : ℝ)|^4313 ≤ (11223894410863/100000000000000 : ℝ)^3289
        have hw : |(-1886514493/10000000000 : ℝ)|=(1886514493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s2_7 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079482059/2500000000 : ℝ)*x 0 + (1157333487/2500000000 : ℝ)*x 1 + (1006579799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079482059/2500000000 : ℝ)^4313 ≤ (3324465003589/10000000000000 : ℝ)^3289 := by
    have hnat : (1079482059 : ℕ)^4313*10000000000000^3289 ≤ 3324465003589^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079482059 2500000000 3324465003589 10000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1157333487/2500000000 : ℝ)^4313 ≤ (36423423651987/100000000000000 : ℝ)^3289 := by
    have hnat : (1157333487 : ℕ)^4313*100000000000000^3289 ≤ 36423423651987^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157333487 2500000000 36423423651987 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006579799/2500000000 : ℝ)^4313 ≤ (30331926294687/100000000000000 : ℝ)^3289 := by
    have hnat : (1006579799 : ℕ)^4313*100000000000000^3289 ≤ 30331926294687^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006579799 2500000000 30331926294687 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079482059/2500000000 : ℝ), (1157333487/2500000000 : ℝ), (1006579799/2500000000 : ℝ)] ![(3324465003589/10000000000000 : ℝ), (36423423651987/100000000000000 : ℝ), (30331926294687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079482059/2500000000 : ℝ)|^4313 ≤ (3324465003589/10000000000000 : ℝ)^3289
        have hw : |(1079482059/2500000000 : ℝ)|=(1079482059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1157333487/2500000000 : ℝ)|^4313 ≤ (36423423651987/100000000000000 : ℝ)^3289
        have hw : |(1157333487/2500000000 : ℝ)|=(1157333487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006579799/2500000000 : ℝ)|^4313 ≤ (30331926294687/100000000000000 : ℝ)^3289
        have hw : |(1006579799/2500000000 : ℝ)|=(1006579799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1353_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19379/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6991/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9923/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16061/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19379/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6991/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19379/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6991/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19379/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6991/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19379/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6991/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19379/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6991/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19379/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6991/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6991/100000 : ℝ) ^ (539/128 : ℝ) ≤ (340696150261333/25000000000000000000 : ℝ) := by
    have hpowers : (6991/100000 : ℝ)^539 ≤ (340696150261333/25000000000000000000 : ℝ)^128 := by
      have hnat : (6991 : ℕ)^539*25000000000000000000^128 ≤ 340696150261333^128*100000^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6991 100000 340696150261333 25000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6991/100000 : ℝ)) (X := (340696150261333/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hpowhi : (19379/100000 : ℝ) ^ (539/128 : ℝ) ≤ (99769296569754277/100000000000000000000 : ℝ) := by
    have hpowers : (19379/100000 : ℝ)^539 ≤ (99769296569754277/100000000000000000000 : ℝ)^128 := by
      have hnat : (19379 : ℕ)^539*100000000000000000000^128 ≤ 99769296569754277^128*100000^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19379 100000 99769296569754277 100000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19379/100000 : ℝ)) (X := (99769296569754277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500340696150261333/12500000000000000000 : ℝ) ≤ (2000012945055013/2000000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (12500340696150261333/12500000000000000000 : ℝ)^128 ≤ (2000012945055013/2000000000000000 : ℝ)^539 := by
      have hnat : (12500340696150261333 : ℕ)^128*2000000000000000^539 ≤ 2000012945055013^539*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500340696150261333 12500000000000000000 2000012945055013 2000000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000012945055013/2000000000000000 : ℝ)) (X := (12500340696150261333/12500000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100101132081170799609/100000000000000000000 : ℝ) ≤ (10002400726917449/10000000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (100101132081170799609/100000000000000000000 : ℝ)^128 ≤ (10002400726917449/10000000000000000 : ℝ)^539 := by
      have hnat : (100101132081170799609 : ℕ)^128*10000000000000000^539 ≤ 10002400726917449^539*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100101132081170799609 100000000000000000000 10002400726917449 10000000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002400726917449/10000000000000000 : ℝ)) (X := (100101132081170799609/100000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50099769296569754277/50000000000000000000 : ℝ) ≤ (10004736728559833/10000000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (50099769296569754277/50000000000000000000 : ℝ)^128 ≤ (10004736728559833/10000000000000000 : ℝ)^539 := by
      have hnat : (50099769296569754277 : ℕ)^128*10000000000000000^539 ≤ 10004736728559833^539*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50099769296569754277 50000000000000000000 10004736728559833 10000000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004736728559833/10000000000000000 : ℝ)) (X := (50099769296569754277/50000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(340696150261333/25000000000000000000 : ℝ) ≤ ((30962034960435923033/30970000000000000000 : ℝ)+2*(146000102649/77425000000000 : ℝ)*(6991/100000 : ℝ))^(539/128 : ℝ) := by
    rw [show (30962034960435923033/30970000000000000000 : ℝ)+2*(146000102649/77425000000000 : ℝ)*(6991/100000 : ℝ)=(2000012945055013/2000000000000000 : ℝ) by norm_num, show 1+2*(340696150261333/25000000000000000000 : ℝ)=(12500340696150261333/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(99769296569754277/100000000000000000000 : ℝ)+(340696150261333/25000000000000000000 : ℝ) ≤ ((30962034960435923033/30970000000000000000 : ℝ)+(146000102649/77425000000000 : ℝ)*((19379/100000 : ℝ)+(6991/100000 : ℝ)))^(539/128 : ℝ) := by
    rw [show (30962034960435923033/30970000000000000000 : ℝ)+(146000102649/77425000000000 : ℝ)*((19379/100000 : ℝ)+(6991/100000 : ℝ))=(10002400726917449/10000000000000000 : ℝ) by norm_num, show 1+(99769296569754277/100000000000000000000 : ℝ)+(340696150261333/25000000000000000000 : ℝ)=(100101132081170799609/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(99769296569754277/100000000000000000000 : ℝ) ≤ ((30962034960435923033/30970000000000000000 : ℝ)+2*(146000102649/77425000000000 : ℝ)*(19379/100000 : ℝ))^(539/128 : ℝ) := by
    rw [show (30962034960435923033/30970000000000000000 : ℝ)+2*(146000102649/77425000000000 : ℝ)*(19379/100000 : ℝ)=(10004736728559833/10000000000000000 : ℝ) by norm_num, show 1+2*(99769296569754277/100000000000000000000 : ℝ)=(50099769296569754277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30962034960435923033/30970000000000000000 : ℝ)*(X 1 0+X 2 0)+(146000102649/77425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (6991/100000 : ℝ)) (hi := (19379/100000 : ℝ)) (c := (30962034960435923033/30970000000000000000 : ℝ)) (alpha := (146000102649/77425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30962034960435923033/30970000000000000000 : ℝ)*(X 0 1+X 2 1)+(146000102649/77425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (6991/100000 : ℝ)) (hi := (19379/100000 : ℝ)) (c := (30962034960435923033/30970000000000000000 : ℝ)) (alpha := (146000102649/77425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30962034960435923033/30970000000000000000 : ℝ)*(X 0 2+X 1 2)+(146000102649/77425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (6991/100000 : ℝ)) (hi := (19379/100000 : ℝ)) (c := (30962034960435923033/30970000000000000000 : ℝ)) (alpha := (146000102649/77425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-506274741/2500000000 : ℝ)*X 0 0+(684596433/1250000000 : ℝ)*X 0 1+(5186450229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2682591073/5000000000 : ℝ)*X 1 0+(-1087510201/5000000000 : ℝ)*X 1 1+(5186450611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((670647777/1250000000 : ℝ)*X 2 0+(5186450529/10000000000 : ℝ)*X 2 1+(-2175020417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158897889/5000000000 : ℝ)*X 0 0+(4022501841/10000000000 : ℝ)*X 0 1+(4633117583/10000000000 : ℝ)*X 0 2+(2158897889/5000000000 : ℝ)*X 1 0+(4022501841/10000000000 : ℝ)*X 1 1+(4633117583/10000000000 : ℝ)*X 1 2+(2158897889/5000000000 : ℝ)*X 2 0+(4022501841/10000000000 : ℝ)*X 2 1+(4633117583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2025161787/10000000000 : ℝ)*X 0 0+(518824947/1000000000 : ℝ)*X 0 1+(2737478099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290263341/10000000000 : ℝ)*X 1 0+(-47162863/250000000 : ℝ)*X 1 1+(684369521/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211610533/400000000 : ℝ)*X 2 0+(1368739051/2500000000 : ℝ)*X 2 1+(-1886514493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079482059/2500000000 : ℝ)*X 0 0+(1157333487/2500000000 : ℝ)*X 0 1+(1006579799/2500000000 : ℝ)*X 0 2+(1079482059/2500000000 : ℝ)*X 1 0+(1157333487/2500000000 : ℝ)*X 1 1+(1006579799/2500000000 : ℝ)*X 1 2+(1079482059/2500000000 : ℝ)*X 2 0+(1157333487/2500000000 : ℝ)*X 2 1+(1006579799/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4643348595620712745372221729/774250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (976241243/100000000000000 : ℝ)*(base19) + (1004247417/100000000000000 : ℝ)*(base23) + (454281/5000000000000 : ℝ)*(lower2) + (65819619/50000000000000 : ℝ)*(upper3) + (57630633/50000000000000 : ℝ)*(upper5) + (1270549397485629/50000000000000 : ℝ)*(major0) + (1270549397485629/50000000000000 : ℝ)*(major1) + (1270549397485629/50000000000000 : ℝ)*(major2) + (1722238274143961/50000000000000 : ℝ)*(sp0) + (430561482247649/12500000000000 : ℝ)*(sp1) + (3444491829975019/100000000000000 : ℝ)*(sp2) + (818848835527991/50000000000000 : ℝ)*(sp3) + (8142967257/50000000000000 : ℝ)*(sp4) + (1721189179/25000000000000 : ℝ)*(sp7) + (818852277906349/50000000000000 : ℝ)*(f.failure) + (861123208555609/25000000000000 : ℝ)*(f.sum) + (9526628675729/7742500000000000000000000000 : ℝ)*base65 + (2984635337082992757/1548500000000000000000000000000000 : ℝ)*base67 + (67118629516007243/1548500000000000000000000000000000 : ℝ)*base70 + (24510098486761992757/1548500000000000000000000000000000 : ℝ)*base71 + (38797649293271/7742500000000000000000000000 : ℝ)*base74 + (2699034431986992757/1548500000000000000000000000000000 : ℝ)*base75 + (10974870471269992757/1548500000000000000000000000000000 : ℝ)*base77 + (5328749636072507243/1548500000000000000000000000000000 : ℝ)*base80 + (29602800260947/15485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3346173/5000000000000000000000 : ℝ)*base90 + (3346173/5000000000000000000000 : ℝ)*base92 + (3346173/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5158661975448604396544468853/774250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139092411/10000000000000 : ℝ)*(base19) + (1548120191/100000000000000 : ℝ)*(base23) + (40849903/25000000000000 : ℝ)*(upper3) + (16809059/25000000000000 : ℝ)*(lower4) + (5219863/5000000000000 : ℝ)*(upper5) + (1286554318647051/50000000000000 : ℝ)*(major0) + (1286554318647051/50000000000000 : ℝ)*(major1) + (1286554318647051/50000000000000 : ℝ)*(major2) + (7894752551/50000000000000 : ℝ)*(sp1) + (116624729/625000000000 : ℝ)*(sp2) + (1743941288390387/50000000000000 : ℝ)*(sp4) + (1743932698175781/50000000000000 : ℝ)*(sp5) + (435982796087993/12500000000000 : ℝ)*(sp6) + (1658334475714557/100000000000000 : ℝ)*(sp7) + (1658334475714557/100000000000000 : ℝ)*(f.failure) + (1743941288390387/50000000000000 : ℝ)*(f.sum) + (18308220981251/7742500000000000000000000000 : ℝ)*base65 + (16087824677592025683/1548500000000000000000000000000000 : ℝ)*base67 + (29400120289104025683/1548500000000000000000000000000000 : ℝ)*base69 + (22630611651347025683/1548500000000000000000000000000000 : ℝ)*base71 + (3633210753041/1935625000000000000000000000 : ℝ)*base74 + (24405720807533025683/1548500000000000000000000000000000 : ℝ)*base75 + (10301190622806025683/1548500000000000000000000000000000 : ℝ)*base77 + (7918803737826025683/1548500000000000000000000000000000 : ℝ)*base79 + (11541477127073/3871250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (22419789/10000000000000000000000 : ℝ)*base90 + (22419789/10000000000000000000000 : ℝ)*base92 + (22419789/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1353_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19379/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6991/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9923/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16061/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1353_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1353_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9923/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16061/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1353_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1353_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1353_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9923/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16061/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1353_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
