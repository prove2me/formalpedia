-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1108_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:05.673609+00:00
-- url     : https://prove2.me/submissions/20ad04ae-b31b-439c-bb58-784444ab685f

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
theorem support_rectangle_w1108_s0_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-14864207/78125000 : ℝ)*x 0 + (1212444373/2000000000 : ℝ)*x 1 + (4776157247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14864207/78125000 : ℝ)^8301 ≤ (5524500055133/50000000000000 : ℝ)^6253 := by
    have hnat : (14864207 : ℕ)^8301*50000000000000^6253 ≤ 5524500055133^6253*78125000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14864207 78125000 5524500055133 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212444373/2000000000 : ℝ)^8301 ≤ (12864082152187/25000000000000 : ℝ)^6253 := by
    have hnat : (1212444373 : ℕ)^8301*25000000000000^6253 ≤ 12864082152187^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212444373 2000000000 12864082152187 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4776157247/10000000000 : ℝ)^8301 ≤ (18747335632679/50000000000000 : ℝ)^6253 := by
    have hnat : (4776157247 : ℕ)^8301*50000000000000^6253 ≤ 18747335632679^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776157247 10000000000 18747335632679 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14864207/78125000 : ℝ), (1212444373/2000000000 : ℝ), (4776157247/10000000000 : ℝ)] ![(5524500055133/50000000000000 : ℝ), (12864082152187/25000000000000 : ℝ), (18747335632679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14864207/78125000 : ℝ)|^8301 ≤ (5524500055133/50000000000000 : ℝ)^6253
        have hw : |(-14864207/78125000 : ℝ)|=(14864207/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1212444373/2000000000 : ℝ)|^8301 ≤ (12864082152187/25000000000000 : ℝ)^6253
        have hw : |(1212444373/2000000000 : ℝ)|=(1212444373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4776157247/10000000000 : ℝ)|^8301 ≤ (18747335632679/50000000000000 : ℝ)^6253
        have hw : |(4776157247/10000000000 : ℝ)|=(4776157247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s0_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2759354281/5000000000 : ℝ)*x 0 + (-2641653491/10000000000 : ℝ)*x 1 + (2388078687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759354281/5000000000 : ℝ)^8301 ≤ (5677973455107/12500000000000 : ℝ)^6253 := by
    have hnat : (2759354281 : ℕ)^8301*12500000000000^6253 ≤ 5677973455107^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759354281 5000000000 5677973455107 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641653491/10000000000 : ℝ)^8301 ≤ (3416307950951/20000000000000 : ℝ)^6253 := by
    have hnat : (2641653491 : ℕ)^8301*20000000000000^6253 ≤ 3416307950951^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641653491 10000000000 3416307950951 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388078687/5000000000 : ℝ)^8301 ≤ (37494672588897/100000000000000 : ℝ)^6253 := by
    have hnat : (2388078687 : ℕ)^8301*100000000000000^6253 ≤ 37494672588897^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388078687 5000000000 37494672588897 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759354281/5000000000 : ℝ), (-2641653491/10000000000 : ℝ), (2388078687/5000000000 : ℝ)] ![(5677973455107/12500000000000 : ℝ), (3416307950951/20000000000000 : ℝ), (37494672588897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759354281/5000000000 : ℝ)|^8301 ≤ (5677973455107/12500000000000 : ℝ)^6253
        have hw : |(2759354281/5000000000 : ℝ)|=(2759354281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2641653491/10000000000 : ℝ)|^8301 ≤ (3416307950951/20000000000000 : ℝ)^6253
        have hw : |(-2641653491/10000000000 : ℝ)|=(2641653491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2388078687/5000000000 : ℝ)|^8301 ≤ (37494672588897/100000000000000 : ℝ)^6253
        have hw : |(2388078687/5000000000 : ℝ)|=(2388078687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s0_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1103741757/2000000000 : ℝ)*x 0 + (955231429/2000000000 : ℝ)*x 1 + (-528330697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103741757/2000000000 : ℝ)^8301 ≤ (709746719961/1562500000000 : ℝ)^6253 := by
    have hnat : (1103741757 : ℕ)^8301*1562500000000^6253 ≤ 709746719961^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103741757 2000000000 709746719961 1562500000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955231429/2000000000 : ℝ)^8301 ≤ (37494670202359/100000000000000 : ℝ)^6253 := by
    have hnat : (955231429 : ℕ)^8301*100000000000000^6253 ≤ 37494670202359^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955231429 2000000000 37494670202359 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528330697/2000000000 : ℝ)^8301 ≤ (17081539703251/100000000000000 : ℝ)^6253 := by
    have hnat : (528330697 : ℕ)^8301*100000000000000^6253 ≤ 17081539703251^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528330697 2000000000 17081539703251 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103741757/2000000000 : ℝ), (955231429/2000000000 : ℝ), (-528330697/2000000000 : ℝ)] ![(709746719961/1562500000000 : ℝ), (37494670202359/100000000000000 : ℝ), (17081539703251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103741757/2000000000 : ℝ)|^8301 ≤ (709746719961/1562500000000 : ℝ)^6253
        have hw : |(1103741757/2000000000 : ℝ)|=(1103741757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(955231429/2000000000 : ℝ)|^8301 ≤ (37494670202359/100000000000000 : ℝ)^6253
        have hw : |(955231429/2000000000 : ℝ)|=(955231429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528330697/2000000000 : ℝ)|^8301 ≤ (17081539703251/100000000000000 : ℝ)^6253
        have hw : |(-528330697/2000000000 : ℝ)|=(528330697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s0_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2101877481/5000000000 : ℝ)*x 0 + (3122706507/10000000000 : ℝ)*x 1 + (5664247163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101877481/5000000000 : ℝ)^8301 ≤ (3164973384337/10000000000000 : ℝ)^6253 := by
    have hnat : (2101877481 : ℕ)^8301*10000000000000^6253 ≤ 3164973384337^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101877481 5000000000 3164973384337 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122706507/10000000000 : ℝ)^8301 ≤ (21329398419739/100000000000000 : ℝ)^6253 := by
    have hnat : (3122706507 : ℕ)^8301*100000000000000^6253 ≤ 21329398419739^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122706507 10000000000 21329398419739 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664247163/10000000000 : ℝ)^8301 ≤ (11755216929301/25000000000000 : ℝ)^6253 := by
    have hnat : (5664247163 : ℕ)^8301*25000000000000^6253 ≤ 11755216929301^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664247163 10000000000 11755216929301 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101877481/5000000000 : ℝ), (3122706507/10000000000 : ℝ), (5664247163/10000000000 : ℝ)] ![(3164973384337/10000000000000 : ℝ), (21329398419739/100000000000000 : ℝ), (11755216929301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101877481/5000000000 : ℝ)|^8301 ≤ (3164973384337/10000000000000 : ℝ)^6253
        have hw : |(2101877481/5000000000 : ℝ)|=(2101877481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122706507/10000000000 : ℝ)|^8301 ≤ (21329398419739/100000000000000 : ℝ)^6253
        have hw : |(3122706507/10000000000 : ℝ)|=(3122706507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5664247163/10000000000 : ℝ)|^8301 ≤ (11755216929301/25000000000000 : ℝ)^6253
        have hw : |(5664247163/10000000000 : ℝ)|=(5664247163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s0_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-953932963/5000000000 : ℝ)*x 0 + (2404674991/5000000000 : ℝ)*x 1 + (6027864099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (953932963/5000000000 : ℝ)^8301 ≤ (11089472224141/100000000000000 : ℝ)^6253 := by
    have hnat : (953932963 : ℕ)^8301*100000000000000^6253 ≤ 11089472224141^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953932963 5000000000 11089472224141 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2404674991/5000000000 : ℝ)^8301 ≤ (7568196913733/20000000000000 : ℝ)^6253 := by
    have hnat : (2404674991 : ℕ)^8301*20000000000000^6253 ≤ 7568196913733^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404674991 5000000000 7568196913733 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6027864099/10000000000 : ℝ)^8301 ≤ (10213908637989/20000000000000 : ℝ)^6253 := by
    have hnat : (6027864099 : ℕ)^8301*20000000000000^6253 ≤ 10213908637989^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6027864099 10000000000 10213908637989 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-953932963/5000000000 : ℝ), (2404674991/5000000000 : ℝ), (6027864099/10000000000 : ℝ)] ![(11089472224141/100000000000000 : ℝ), (7568196913733/20000000000000 : ℝ), (10213908637989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-953932963/5000000000 : ℝ)|^8301 ≤ (11089472224141/100000000000000 : ℝ)^6253
        have hw : |(-953932963/5000000000 : ℝ)|=(953932963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2404674991/5000000000 : ℝ)|^8301 ≤ (7568196913733/20000000000000 : ℝ)^6253
        have hw : |(2404674991/5000000000 : ℝ)|=(2404674991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6027864099/10000000000 : ℝ)|^8301 ≤ (10213908637989/20000000000000 : ℝ)^6253
        have hw : |(6027864099/10000000000 : ℝ)|=(6027864099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s0_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (258471309/500000000 : ℝ)*x 0 + (-55597907/400000000 : ℝ)*x 1 + (1506966467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258471309/500000000 : ℝ)^8301 ≤ (20823713384651/50000000000000 : ℝ)^6253 := by
    have hnat : (258471309 : ℕ)^8301*50000000000000^6253 ≤ 20823713384651^6253*500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258471309 500000000 20823713384651 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55597907/400000000 : ℝ)^8301 ≤ (1820752532391/25000000000000 : ℝ)^6253 := by
    have hnat : (55597907 : ℕ)^8301*25000000000000^6253 ≤ 1820752532391^6253*400000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55597907 400000000 1820752532391 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506966467/2500000000 : ℝ)^8301 ≤ (51069563086063/100000000000000 : ℝ)^6253 := by
    have hnat : (1506966467 : ℕ)^8301*100000000000000^6253 ≤ 51069563086063^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506966467 2500000000 51069563086063 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258471309/500000000 : ℝ), (-55597907/400000000 : ℝ), (1506966467/2500000000 : ℝ)] ![(20823713384651/50000000000000 : ℝ), (1820752532391/25000000000000 : ℝ), (51069563086063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258471309/500000000 : ℝ)|^8301 ≤ (20823713384651/50000000000000 : ℝ)^6253
        have hw : |(258471309/500000000 : ℝ)|=(258471309/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55597907/400000000 : ℝ)|^8301 ≤ (1820752532391/25000000000000 : ℝ)^6253
        have hw : |(-55597907/400000000 : ℝ)|=(55597907/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1506966467/2500000000 : ℝ)|^8301 ≤ (51069563086063/100000000000000 : ℝ)^6253
        have hw : |(1506966467/2500000000 : ℝ)|=(1506966467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s0_6 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (516942861/1000000000 : ℝ)*x 0 + (1205572921/2000000000 : ℝ)*x 1 + (-694972991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516942861/1000000000 : ℝ)^8301 ≤ (1665898110343/4000000000000 : ℝ)^6253 := by
    have hnat : (516942861 : ℕ)^8301*4000000000000^6253 ≤ 1665898110343^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516942861 1000000000 1665898110343 4000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1205572921/2000000000 : ℝ)^8301 ≤ (51069548880977/100000000000000 : ℝ)^6253 := by
    have hnat : (1205572921 : ℕ)^8301*100000000000000^6253 ≤ 51069548880977^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205572921 2000000000 51069548880977 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694972991/5000000000 : ℝ)^8301 ≤ (7282998353197/100000000000000 : ℝ)^6253 := by
    have hnat : (694972991 : ℕ)^8301*100000000000000^6253 ≤ 7282998353197^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694972991 5000000000 7282998353197 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516942861/1000000000 : ℝ), (1205572921/2000000000 : ℝ), (-694972991/5000000000 : ℝ)] ![(1665898110343/4000000000000 : ℝ), (51069548880977/100000000000000 : ℝ), (7282998353197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516942861/1000000000 : ℝ)|^8301 ≤ (1665898110343/4000000000000 : ℝ)^6253
        have hw : |(516942861/1000000000 : ℝ)|=(516942861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1205572921/2000000000 : ℝ)|^8301 ≤ (51069548880977/100000000000000 : ℝ)^6253
        have hw : |(1205572921/2000000000 : ℝ)|=(1205572921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-694972991/5000000000 : ℝ)|^8301 ≤ (7282998353197/100000000000000 : ℝ)^6253
        have hw : |(-694972991/5000000000 : ℝ)|=(694972991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s0_7 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (16856487/40000000 : ℝ)*x 0 + (5598653249/10000000000 : ℝ)*x 1 + (3190602309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16856487/40000000 : ℝ)^8301 ≤ (15876694883843/50000000000000 : ℝ)^6253 := by
    have hnat : (16856487 : ℕ)^8301*50000000000000^6253 ≤ 15876694883843^6253*40000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16856487 40000000 15876694883843 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5598653249/10000000000 : ℝ)^8301 ≤ (46299382497221/100000000000000 : ℝ)^6253 := by
    have hnat : (5598653249 : ℕ)^8301*100000000000000^6253 ≤ 46299382497221^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598653249 10000000000 46299382497221 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3190602309/10000000000 : ℝ)^8301 ≤ (4389445545707/20000000000000 : ℝ)^6253 := by
    have hnat : (3190602309 : ℕ)^8301*20000000000000^6253 ≤ 4389445545707^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3190602309 10000000000 4389445545707 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16856487/40000000 : ℝ), (5598653249/10000000000 : ℝ), (3190602309/10000000000 : ℝ)] ![(15876694883843/50000000000000 : ℝ), (46299382497221/100000000000000 : ℝ), (4389445545707/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16856487/40000000 : ℝ)|^8301 ≤ (15876694883843/50000000000000 : ℝ)^6253
        have hw : |(16856487/40000000 : ℝ)|=(16856487/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5598653249/10000000000 : ℝ)|^8301 ≤ (46299382497221/100000000000000 : ℝ)^6253
        have hw : |(5598653249/10000000000 : ℝ)|=(5598653249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3190602309/10000000000 : ℝ)|^8301 ≤ (4389445545707/20000000000000 : ℝ)^6253
        have hw : |(3190602309/10000000000 : ℝ)|=(3190602309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (273/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13973/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2075/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2075 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2075*1^512 ≤ 0^512*1^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2075/512 : ℝ) ≤ (243924176613494977/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2075 ≤ (243924176613494977/10000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2075*10000000000000000000^512 ≤ 243924176613494977^512*5^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 243924176613494977 10000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (243924176613494977/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2075 := by
      have hnat : (1 : ℕ)^512*1^2075 ≤ 1^2075*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10243924176613494977/10000000000000000000 : ℝ) ≤ (10059642375256409/10000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (10243924176613494977/10000000000000000000 : ℝ)^512 ≤ (10059642375256409/10000000000000000 : ℝ)^2075 := by
      have hnat : (10243924176613494977 : ℕ)^512*10000000000000000^2075 ≤ 10059642375256409^2075*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10243924176613494977 10000000000000000000 10059642375256409 10000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059642375256409/10000000000000000 : ℝ)) (X := (10243924176613494977/10000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5243924176613494977/5000000000000000000 : ℝ) ≤ (5059642375256409/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (5243924176613494977/5000000000000000000 : ℝ)^512 ≤ (5059642375256409/5000000000000000 : ℝ)^2075 := by
      have hnat : (5243924176613494977 : ℕ)^512*5000000000000000^2075 ≤ 5059642375256409^2075*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5243924176613494977 5000000000000000000 5059642375256409 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059642375256409/5000000000000000 : ℝ)) (X := (5243924176613494977/5000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59642375256409/4000000000000000 : ℝ)*(0 : ℝ))^(2075/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(59642375256409/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(243924176613494977/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59642375256409/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (1 : ℝ)+(59642375256409/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059642375256409/10000000000000000 : ℝ) by norm_num, show 1+(243924176613494977/10000000000000000000 : ℝ)+(0 : ℝ)=(10243924176613494977/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(243924176613494977/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59642375256409/4000000000000000 : ℝ)*(2/5 : ℝ))^(2075/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(59642375256409/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059642375256409/5000000000000000 : ℝ) by norm_num, show 1+2*(243924176613494977/10000000000000000000 : ℝ)=(5243924176613494977/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59642375256409/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59642375256409/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59642375256409/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59642375256409/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59642375256409/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59642375256409/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-14864207/78125000 : ℝ)*X 0 0+(1212444373/2000000000 : ℝ)*X 0 1+(4776157247/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2759354281/5000000000 : ℝ)*X 1 0+(-2641653491/10000000000 : ℝ)*X 1 1+(2388078687/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1103741757/2000000000 : ℝ)*X 2 0+(955231429/2000000000 : ℝ)*X 2 1+(-528330697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2101877481/5000000000 : ℝ)*X 0 0+(3122706507/10000000000 : ℝ)*X 0 1+(5664247163/10000000000 : ℝ)*X 0 2+(2101877481/5000000000 : ℝ)*X 1 0+(3122706507/10000000000 : ℝ)*X 1 1+(5664247163/10000000000 : ℝ)*X 1 2+(2101877481/5000000000 : ℝ)*X 2 0+(3122706507/10000000000 : ℝ)*X 2 1+(5664247163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-953932963/5000000000 : ℝ)*X 0 0+(2404674991/5000000000 : ℝ)*X 0 1+(6027864099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((258471309/500000000 : ℝ)*X 1 0+(-55597907/400000000 : ℝ)*X 1 1+(1506966467/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((516942861/1000000000 : ℝ)*X 2 0+(1205572921/2000000000 : ℝ)*X 2 1+(-694972991/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((16856487/40000000 : ℝ)*X 0 0+(5598653249/10000000000 : ℝ)*X 0 1+(3190602309/10000000000 : ℝ)*X 0 2+(16856487/40000000 : ℝ)*X 1 0+(5598653249/10000000000 : ℝ)*X 1 1+(3190602309/10000000000 : ℝ)*X 1 2+(16856487/40000000 : ℝ)*X 2 0+(5598653249/10000000000 : ℝ)*X 2 1+(3190602309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16502019727850690527743/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26270021/100000000000000 : ℝ)*(base1) + (654475329/100000000000000 : ℝ)*(base19) + (317340163/50000000000000 : ℝ)*(base23) + (51215007/100000000000000 : ℝ)*(base24) + (31685469/20000000000000 : ℝ)*(upper3) + (36594801027641/6250000000000 : ℝ)*(major0) + (36594801027641/6250000000000 : ℝ)*(major1) + (36594801027641/6250000000000 : ℝ)*(major2) + (194392024346961/25000000000000 : ℝ)*(sp0) + (388784430488837/50000000000000 : ℝ)*(sp1) + (777568829557669/100000000000000 : ℝ)*(sp2) + (98365701749389/25000000000000 : ℝ)*(sp3) + (72216759/5000000000000 : ℝ)*(sp4) + (239230631/20000000000000 : ℝ)*(sp7) + (393464029420733/100000000000000 : ℝ)*(f.failure) + (388784757726501/50000000000000 : ℝ)*(f.sum) + (8118386176169/12500000000000000000000000000 : ℝ)*base65 + (64116511273831/25000000000000000000000000000 : ℝ)*base68 + (118309651126169/25000000000000000000000000000 : ℝ)*base69 + (22979401348831/25000000000000000000000000000 : ℝ)*base72 + (3705476988669/12500000000000000000000000000 : ℝ)*base73 + (61426843573831/25000000000000000000000000000 : ℝ)*base76 + (17526164226169/25000000000000000000000000000 : ℝ)*base77 + (33289490898831/25000000000000000000000000000 : ℝ)*base80 + (10483545676169/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (66907813/10000000000000000000000 : ℝ)*base89 + (66907813/10000000000000000000000 : ℝ)*base91 + (66907813/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20754969593311480978209/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (484002817/100000000000000 : ℝ)*(base19) + (1402121299/100000000000000 : ℝ)*(base23) + (252210933/50000000000000 : ℝ)*(base39) + (208559783/100000000000000 : ℝ)*(base45) + (128868669/100000000000000 : ℝ)*(upper3) + (11302973/4000000000000 : ℝ)*(upper5) + (61797025751177/10000000000000 : ℝ)*(major0) + (61797025751177/10000000000000 : ℝ)*(major1) + (123593950617981/20000000000000 : ℝ)*(major2) + (628627469/100000000000000 : ℝ)*(sp2) + (32826691085541/4000000000000 : ℝ)*(sp4) + (205166698283927/25000000000000 : ℝ)*(sp5) + (410332875405811/50000000000000 : ℝ)*(sp6) + (51909070063133/12500000000000 : ℝ)*(sp7) + (51909070063133/12500000000000 : ℝ)*(f.failure) + (820667781560391/100000000000000 : ℝ)*(f.sum) + (40204026004597/16000000000000000000000000000 : ℝ)*base66 + (603355877989771/80000000000000000000000000000 : ℝ)*base68 + (160824938503393/40000000000000000000000000000 : ℝ)*base69 + (647417314309771/80000000000000000000000000000 : ℝ)*base72 + (68881324980597/16000000000000000000000000000 : ℝ)*base74 + (54908915743393/40000000000000000000000000000 : ℝ)*base75 + (184597294856607/40000000000000000000000000000 : ℝ)*base78 + (72243121496607/40000000000000000000000000000 : ℝ)*base80 + (89423001596607/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (14774213/1250000000000000000000 : ℝ)*base89 + (14774213/1250000000000000000000 : ℝ)*base91 + (2274213/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1108_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13973/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1108_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1108_s1_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109735343/10000000000 : ℝ)*x 0 + (5710693263/10000000000 : ℝ)*x 1 + (4995074167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109735343/10000000000 : ℝ)^8301 ≤ (6336759804077/50000000000000 : ℝ)^6253 := by
    have hnat : (2109735343 : ℕ)^8301*50000000000000^6253 ≤ 6336759804077^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109735343 10000000000 6336759804077 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5710693263/10000000000 : ℝ)^8301 ≤ (47533400210581/100000000000000 : ℝ)^6253 := by
    have hnat : (5710693263 : ℕ)^8301*100000000000000^6253 ≤ 47533400210581^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5710693263 10000000000 47533400210581 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4995074167/10000000000 : ℝ)^8301 ≤ (39793080160879/100000000000000 : ℝ)^6253 := by
    have hnat : (4995074167 : ℕ)^8301*100000000000000^6253 ≤ 39793080160879^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4995074167 10000000000 39793080160879 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109735343/10000000000 : ℝ), (5710693263/10000000000 : ℝ), (4995074167/10000000000 : ℝ)] ![(6336759804077/50000000000000 : ℝ), (47533400210581/100000000000000 : ℝ), (39793080160879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109735343/10000000000 : ℝ)|^8301 ≤ (6336759804077/50000000000000 : ℝ)^6253
        have hw : |(-2109735343/10000000000 : ℝ)|=(2109735343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5710693263/10000000000 : ℝ)|^8301 ≤ (47533400210581/100000000000000 : ℝ)^6253
        have hw : |(5710693263/10000000000 : ℝ)|=(5710693263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4995074167/10000000000 : ℝ)|^8301 ≤ (39793080160879/100000000000000 : ℝ)^6253
        have hw : |(4995074167/10000000000 : ℝ)|=(4995074167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s1_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5420993713/10000000000 : ℝ)*x 0 + (-2496599227/10000000000 : ℝ)*x 1 + (39024017/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420993713/10000000000 : ℝ)^8301 ≤ (5544899734719/12500000000000 : ℝ)^6253 := by
    have hnat : (5420993713 : ℕ)^8301*12500000000000^6253 ≤ 5544899734719^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420993713 10000000000 5544899734719 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2496599227/10000000000 : ℝ)^8301 ≤ (3169544370929/20000000000000 : ℝ)^6253 := by
    have hnat : (2496599227 : ℕ)^8301*20000000000000^6253 ≤ 3169544370929^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2496599227 10000000000 3169544370929 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39024017/78125000 : ℝ)^8301 ≤ (1989654012803/5000000000000 : ℝ)^6253 := by
    have hnat : (39024017 : ℕ)^8301*5000000000000^6253 ≤ 1989654012803^6253*78125000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39024017 78125000 1989654012803 5000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420993713/10000000000 : ℝ), (-2496599227/10000000000 : ℝ), (39024017/78125000 : ℝ)] ![(5544899734719/12500000000000 : ℝ), (3169544370929/20000000000000 : ℝ), (1989654012803/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420993713/10000000000 : ℝ)|^8301 ≤ (5544899734719/12500000000000 : ℝ)^6253
        have hw : |(5420993713/10000000000 : ℝ)|=(5420993713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2496599227/10000000000 : ℝ)|^8301 ≤ (3169544370929/20000000000000 : ℝ)^6253
        have hw : |(-2496599227/10000000000 : ℝ)|=(2496599227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39024017/78125000 : ℝ)|^8301 ≤ (1989654012803/5000000000000 : ℝ)^6253
        have hw : |(39024017/78125000 : ℝ)|=(39024017/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s1_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2710497477/5000000000 : ℝ)*x 0 + (4995072991/10000000000 : ℝ)*x 1 + (-1248299557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710497477/5000000000 : ℝ)^8301 ≤ (22179605679321/50000000000000 : ℝ)^6253 := by
    have hnat : (2710497477 : ℕ)^8301*50000000000000^6253 ≤ 22179605679321^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710497477 5000000000 22179605679321 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4995072991/10000000000 : ℝ)^8301 ≤ (397930677239/1000000000000 : ℝ)^6253 := by
    have hnat : (4995072991 : ℕ)^8301*1000000000000^6253 ≤ 397930677239^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4995072991 10000000000 397930677239 1000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248299557/5000000000 : ℝ)^8301 ≤ (15847720902423/100000000000000 : ℝ)^6253 := by
    have hnat : (1248299557 : ℕ)^8301*100000000000000^6253 ≤ 15847720902423^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248299557 5000000000 15847720902423 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710497477/5000000000 : ℝ), (4995072991/10000000000 : ℝ), (-1248299557/5000000000 : ℝ)] ![(22179605679321/50000000000000 : ℝ), (397930677239/1000000000000 : ℝ), (15847720902423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710497477/5000000000 : ℝ)|^8301 ≤ (22179605679321/50000000000000 : ℝ)^6253
        have hw : |(2710497477/5000000000 : ℝ)|=(2710497477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4995072991/10000000000 : ℝ)|^8301 ≤ (397930677239/1000000000000 : ℝ)^6253
        have hw : |(4995072991/10000000000 : ℝ)|=(4995072991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1248299557/5000000000 : ℝ)|^8301 ≤ (15847720902423/100000000000000 : ℝ)^6253
        have hw : |(-1248299557/5000000000 : ℝ)|=(1248299557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s1_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4320304097/10000000000 : ℝ)*x 0 + (3670611523/10000000000 : ℝ)*x 1 + (5084827277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320304097/10000000000 : ℝ)^8301 ≤ (2051242314237/6250000000000 : ℝ)^6253 := by
    have hnat : (4320304097 : ℕ)^8301*6250000000000^6253 ≤ 2051242314237^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320304097 10000000000 2051242314237 6250000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3670611523/10000000000 : ℝ)^8301 ≤ (26435062295277/100000000000000 : ℝ)^6253 := by
    have hnat : (3670611523 : ℕ)^8301*100000000000000^6253 ≤ 26435062295277^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3670611523 10000000000 26435062295277 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084827277/10000000000 : ℝ)^8301 ≤ (1273283145879/3125000000000 : ℝ)^6253 := by
    have hnat : (5084827277 : ℕ)^8301*3125000000000^6253 ≤ 1273283145879^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084827277 10000000000 1273283145879 3125000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320304097/10000000000 : ℝ), (3670611523/10000000000 : ℝ), (5084827277/10000000000 : ℝ)] ![(2051242314237/6250000000000 : ℝ), (26435062295277/100000000000000 : ℝ), (1273283145879/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320304097/10000000000 : ℝ)|^8301 ≤ (2051242314237/6250000000000 : ℝ)^6253
        have hw : |(4320304097/10000000000 : ℝ)|=(4320304097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3670611523/10000000000 : ℝ)|^8301 ≤ (26435062295277/100000000000000 : ℝ)^6253
        have hw : |(3670611523/10000000000 : ℝ)|=(3670611523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084827277/10000000000 : ℝ)|^8301 ≤ (1273283145879/3125000000000 : ℝ)^6253
        have hw : |(5084827277/10000000000 : ℝ)|=(5084827277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s1_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-52764753/250000000 : ℝ)*x 0 + (2502486491/5000000000 : ℝ)*x 1 + (5700596211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52764753/250000000 : ℝ)^8301 ≤ (1268033660177/10000000000000 : ℝ)^6253 := by
    have hnat : (52764753 : ℕ)^8301*10000000000000^6253 ≤ 1268033660177^6253*250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52764753 250000000 1268033660177 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2502486491/5000000000 : ℝ)^8301 ≤ (9974450162631/25000000000000 : ℝ)^6253 := by
    have hnat : (2502486491 : ℕ)^8301*25000000000000^6253 ≤ 9974450162631^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502486491 5000000000 9974450162631 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5700596211/10000000000 : ℝ)^8301 ≤ (370483302619/781250000000 : ℝ)^6253 := by
    have hnat : (5700596211 : ℕ)^8301*781250000000^6253 ≤ 370483302619^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5700596211 10000000000 370483302619 781250000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52764753/250000000 : ℝ), (2502486491/5000000000 : ℝ), (5700596211/10000000000 : ℝ)] ![(1268033660177/10000000000000 : ℝ), (9974450162631/25000000000000 : ℝ), (370483302619/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52764753/250000000 : ℝ)|^8301 ≤ (1268033660177/10000000000000 : ℝ)^6253
        have hw : |(-52764753/250000000 : ℝ)|=(52764753/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2502486491/5000000000 : ℝ)|^8301 ≤ (9974450162631/25000000000000 : ℝ)^6253
        have hw : |(2502486491/5000000000 : ℝ)|=(2502486491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5700596211/10000000000 : ℝ)|^8301 ≤ (370483302619/781250000000 : ℝ)^6253
        have hw : |(5700596211/10000000000 : ℝ)|=(5700596211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s1_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5237837353/10000000000 : ℝ)*x 0 + (-1791076847/10000000000 : ℝ)*x 1 + (2850298011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5237837353/10000000000 : ℝ)^8301 ≤ (42380677096447/100000000000000 : ℝ)^6253 := by
    have hnat : (5237837353 : ℕ)^8301*100000000000000^6253 ≤ 42380677096447^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237837353 10000000000 42380677096447 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1791076847/10000000000 : ℝ)^8301 ≤ (1274682780547/12500000000000 : ℝ)^6253 := by
    have hnat : (1791076847 : ℕ)^8301*12500000000000^6253 ≤ 1274682780547^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791076847 10000000000 1274682780547 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2850298011/5000000000 : ℝ)^8301 ≤ (47421860648041/100000000000000 : ℝ)^6253 := by
    have hnat : (2850298011 : ℕ)^8301*100000000000000^6253 ≤ 47421860648041^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850298011 5000000000 47421860648041 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5237837353/10000000000 : ℝ), (-1791076847/10000000000 : ℝ), (2850298011/5000000000 : ℝ)] ![(42380677096447/100000000000000 : ℝ), (1274682780547/12500000000000 : ℝ), (47421860648041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5237837353/10000000000 : ℝ)|^8301 ≤ (42380677096447/100000000000000 : ℝ)^6253
        have hw : |(5237837353/10000000000 : ℝ)|=(5237837353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1791076847/10000000000 : ℝ)|^8301 ≤ (1274682780547/12500000000000 : ℝ)^6253
        have hw : |(-1791076847/10000000000 : ℝ)|=(1791076847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2850298011/5000000000 : ℝ)|^8301 ≤ (47421860648041/100000000000000 : ℝ)^6253
        have hw : |(2850298011/5000000000 : ℝ)|=(2850298011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s1_6 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5237837379/10000000000 : ℝ)*x 0 + (5700596161/10000000000 : ℝ)*x 1 + (-895538303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5237837379/10000000000 : ℝ)^8301 ≤ (21190338687861/50000000000000 : ℝ)^6253 := by
    have hnat : (5237837379 : ℕ)^8301*50000000000000^6253 ≤ 21190338687861^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237837379 10000000000 21190338687861 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5700596161/10000000000 : ℝ)^8301 ≤ (9484372436613/20000000000000 : ℝ)^6253 := by
    have hnat : (5700596161 : ℕ)^8301*20000000000000^6253 ≤ 9484372436613^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5700596161 10000000000 9484372436613 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895538303/5000000000 : ℝ)^8301 ≤ (10197460422843/100000000000000 : ℝ)^6253 := by
    have hnat : (895538303 : ℕ)^8301*100000000000000^6253 ≤ 10197460422843^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895538303 5000000000 10197460422843 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5237837379/10000000000 : ℝ), (5700596161/10000000000 : ℝ), (-895538303/5000000000 : ℝ)] ![(21190338687861/50000000000000 : ℝ), (9484372436613/20000000000000 : ℝ), (10197460422843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5237837379/10000000000 : ℝ)|^8301 ≤ (21190338687861/50000000000000 : ℝ)^6253
        have hw : |(5237837379/10000000000 : ℝ)|=(5237837379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5700596161/10000000000 : ℝ)|^8301 ≤ (9484372436613/20000000000000 : ℝ)^6253
        have hw : |(5700596161/10000000000 : ℝ)|=(5700596161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-895538303/5000000000 : ℝ)|^8301 ≤ (10197460422843/100000000000000 : ℝ)^6253
        have hw : |(-895538303/5000000000 : ℝ)|=(895538303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s1_7 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (864398367/2000000000 : ℝ)*x 0 + (5065265827/10000000000 : ℝ)*x 1 + (922641159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864398367/2000000000 : ℝ)^8301 ≤ (32836898512017/100000000000000 : ℝ)^6253 := by
    have hnat : (864398367 : ℕ)^8301*100000000000000^6253 ≤ 32836898512017^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864398367 2000000000 32836898512017 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5065265827/10000000000 : ℝ)^8301 ≤ (20268553193149/50000000000000 : ℝ)^6253 := by
    have hnat : (5065265827 : ℕ)^8301*50000000000000^6253 ≤ 20268553193149^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5065265827 10000000000 20268553193149 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922641159/2500000000 : ℝ)^8301 ≤ (13312997544191/50000000000000 : ℝ)^6253 := by
    have hnat : (922641159 : ℕ)^8301*50000000000000^6253 ≤ 13312997544191^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922641159 2500000000 13312997544191 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864398367/2000000000 : ℝ), (5065265827/10000000000 : ℝ), (922641159/2500000000 : ℝ)] ![(32836898512017/100000000000000 : ℝ), (20268553193149/50000000000000 : ℝ), (13312997544191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864398367/2000000000 : ℝ)|^8301 ≤ (32836898512017/100000000000000 : ℝ)^6253
        have hw : |(864398367/2000000000 : ℝ)|=(864398367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5065265827/10000000000 : ℝ)|^8301 ≤ (20268553193149/50000000000000 : ℝ)^6253
        have hw : |(5065265827/10000000000 : ℝ)|=(5065265827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(922641159/2500000000 : ℝ)|^8301 ≤ (13312997544191/50000000000000 : ℝ)^6253
        have hw : |(922641159/2500000000 : ℝ)|=(922641159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13973/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5457/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20593/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13973/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13973/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13973/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13973/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13973/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13973/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (273/100000 : ℝ) ^ (2075/512 : ℝ) ≤ (254289393/6250000000000000000 : ℝ) := by
    have hpowers : (273/100000 : ℝ)^2075 ≤ (254289393/6250000000000000000 : ℝ)^512 := by
      have hnat : (273 : ℕ)^2075*6250000000000000000^512 ≤ 254289393^512*100000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        273 100000 254289393 6250000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (273/100000 : ℝ)) (X := (254289393/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13973/50000 : ℝ) ^ (2075/512 : ℝ) ≤ (570270139858321323/100000000000000000000 : ℝ) := by
    have hpowers : (13973/50000 : ℝ)^2075 ≤ (570270139858321323/100000000000000000000 : ℝ)^512 := by
      have hnat : (13973 : ℕ)^2075*100000000000000000000^512 ≤ 570270139858321323^512*50000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13973 50000 570270139858321323 100000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13973/50000 : ℝ)) (X := (570270139858321323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000000254289393/3125000000000000000 : ℝ) ≤ (2000000000040157/2000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (3125000000254289393/3125000000000000000 : ℝ)^512 ≤ (2000000000040157/2000000000000000 : ℝ)^2075 := by
      have hnat : (3125000000254289393 : ℕ)^512*2000000000000000^2075 ≤ 2000000000040157^2075*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000000254289393 3125000000000000000 2000000000040157 2000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000040157/2000000000000000 : ℝ)) (X := (3125000000254289393/3125000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100570270143926951611/100000000000000000000 : ℝ) ≤ (5007020561153041/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (100570270143926951611/100000000000000000000 : ℝ)^512 ≤ (5007020561153041/5000000000000000 : ℝ)^2075 := by
      have hnat : (100570270143926951611 : ℕ)^512*5000000000000000^2075 ≤ 5007020561153041^2075*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100570270143926951611 100000000000000000000 5007020561153041 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007020561153041/5000000000000000 : ℝ)) (X := (100570270143926951611/100000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50570270139858321323/50000000000000000000 : ℝ) ≤ (10028082244411379/10000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (50570270139858321323/50000000000000000000 : ℝ)^512 ≤ (10028082244411379/10000000000000000 : ℝ)^2075 := by
      have hnat : (50570270139858321323 : ℕ)^512*10000000000000000^2075 ≤ 10028082244411379^2075*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50570270139858321323 50000000000000000000 10028082244411379 10000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028082244411379/10000000000000000 : ℝ)) (X := (50570270139858321323/50000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(254289393/6250000000000000000 : ℝ) ≤ ((276722333552886831143/276730000000000000000 : ℝ)+2*(14041122105297/2767300000000000 : ℝ)*(273/100000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (276722333552886831143/276730000000000000000 : ℝ)+2*(14041122105297/2767300000000000 : ℝ)*(273/100000 : ℝ)=(2000000000040157/2000000000000000 : ℝ) by norm_num, show 1+2*(254289393/6250000000000000000 : ℝ)=(3125000000254289393/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(570270139858321323/100000000000000000000 : ℝ)+(254289393/6250000000000000000 : ℝ) ≤ ((276722333552886831143/276730000000000000000 : ℝ)+(14041122105297/2767300000000000 : ℝ)*((13973/50000 : ℝ)+(273/100000 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (276722333552886831143/276730000000000000000 : ℝ)+(14041122105297/2767300000000000 : ℝ)*((13973/50000 : ℝ)+(273/100000 : ℝ))=(5007020561153041/5000000000000000 : ℝ) by norm_num, show 1+(570270139858321323/100000000000000000000 : ℝ)+(254289393/6250000000000000000 : ℝ)=(100570270143926951611/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(570270139858321323/100000000000000000000 : ℝ) ≤ ((276722333552886831143/276730000000000000000 : ℝ)+2*(14041122105297/2767300000000000 : ℝ)*(13973/50000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (276722333552886831143/276730000000000000000 : ℝ)+2*(14041122105297/2767300000000000 : ℝ)*(13973/50000 : ℝ)=(10028082244411379/10000000000000000 : ℝ) by norm_num, show 1+2*(570270139858321323/100000000000000000000 : ℝ)=(50570270139858321323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (276722333552886831143/276730000000000000000 : ℝ)*(X 1 0+X 2 0)+(14041122105297/2767300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (273/100000 : ℝ)) (hi := (13973/50000 : ℝ)) (c := (276722333552886831143/276730000000000000000 : ℝ)) (alpha := (14041122105297/2767300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (276722333552886831143/276730000000000000000 : ℝ)*(X 0 1+X 2 1)+(14041122105297/2767300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (273/100000 : ℝ)) (hi := (13973/50000 : ℝ)) (c := (276722333552886831143/276730000000000000000 : ℝ)) (alpha := (14041122105297/2767300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (276722333552886831143/276730000000000000000 : ℝ)*(X 0 2+X 1 2)+(14041122105297/2767300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (273/100000 : ℝ)) (hi := (13973/50000 : ℝ)) (c := (276722333552886831143/276730000000000000000 : ℝ)) (alpha := (14041122105297/2767300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2109735343/10000000000 : ℝ)*X 0 0+(5710693263/10000000000 : ℝ)*X 0 1+(4995074167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420993713/10000000000 : ℝ)*X 1 0+(-2496599227/10000000000 : ℝ)*X 1 1+(39024017/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710497477/5000000000 : ℝ)*X 2 0+(4995072991/10000000000 : ℝ)*X 2 1+(-1248299557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320304097/10000000000 : ℝ)*X 0 0+(3670611523/10000000000 : ℝ)*X 0 1+(5084827277/10000000000 : ℝ)*X 0 2+(4320304097/10000000000 : ℝ)*X 1 0+(3670611523/10000000000 : ℝ)*X 1 1+(5084827277/10000000000 : ℝ)*X 1 2+(4320304097/10000000000 : ℝ)*X 2 0+(3670611523/10000000000 : ℝ)*X 2 1+(5084827277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-52764753/250000000 : ℝ)*X 0 0+(2502486491/5000000000 : ℝ)*X 0 1+(5700596211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5237837353/10000000000 : ℝ)*X 1 0+(-1791076847/10000000000 : ℝ)*X 1 1+(2850298011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5237837379/10000000000 : ℝ)*X 2 0+(5700596161/10000000000 : ℝ)*X 2 1+(-895538303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864398367/2000000000 : ℝ)*X 0 0+(5065265827/10000000000 : ℝ)*X 0 1+(922641159/2500000000 : ℝ)*X 0 2+(864398367/2000000000 : ℝ)*X 1 0+(5065265827/10000000000 : ℝ)*X 1 1+(922641159/2500000000 : ℝ)*X 1 2+(864398367/2000000000 : ℝ)*X 2 0+(5065265827/10000000000 : ℝ)*X 2 1+(922641159/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (838985735911707633620728791/138365000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117800861/50000000000000 : ℝ)*(base1) + (69193649/6250000000000 : ℝ)*(base19) + (713498837/50000000000000 : ℝ)*(base23) + (45963209/100000000000000 : ℝ)*(upper3) + (85554183/50000000000000 : ℝ)*(upper5) + (10522550093393/1000000000000 : ℝ)*(major0) + (10522550093393/1000000000000 : ℝ)*(major1) + (10522550093393/1000000000000 : ℝ)*(major2) + (698697506380329/50000000000000 : ℝ)*(sp0) + (174674902754617/12500000000000 : ℝ)*(sp1) + (698699451068823/50000000000000 : ℝ)*(sp2) + (353553774533933/50000000000000 : ℝ)*(sp3) + (1110395277/20000000000000 : ℝ)*(sp4) + (1702754713/100000000000000 : ℝ)*(sp7) + (7071094874243/1000000000000 : ℝ)*(f.failure) + (34935008228383/2500000000000 : ℝ)*(f.sum) + (56298718257179/27673000000000000000000000000 : ℝ)*base66 + (4737496845000851801/276730000000000000000000000000000 : ℝ)*base68 + (3669684267166791801/276730000000000000000000000000000 : ℝ)*base70 + (2777144024426211801/276730000000000000000000000000000 : ℝ)*base72 + (189679828501861/27673000000000000000000000000 : ℝ)*base74 + (2869814359805741801/276730000000000000000000000000000 : ℝ)*base76 + (2132267629330891801/276730000000000000000000000000000 : ℝ)*base78 + (3464495138818111801/276730000000000000000000000000000 : ℝ)*base80 + (70540261377359/13836500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (128923/100000000000000000000 : ℝ)*base89 + (128923/100000000000000000000 : ℝ)*base91 + (128923/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168733361062465818567837/34591250000000000000000000000 : ℝ) := by norm_num
    linear_combination (59762891/100000000000000 : ℝ)*(base1) + (1098277387/100000000000000 : ℝ)*(base19) + (561097359/50000000000000 : ℝ)*(base23) + (106479869/100000000000000 : ℝ)*(upper3) + (27133613/25000000000000 : ℝ)*(upper5) + (1082495444761397/100000000000000 : ℝ)*(major0) + (1082495444761397/100000000000000 : ℝ)*(major1) + (1082495444761397/100000000000000 : ℝ)*(major2) + (4315609177/100000000000000 : ℝ)*(sp1) + (4795487339/100000000000000 : ℝ)*(sp2) + (44923746737841/3125000000000 : ℝ)*(sp4) + (1437554421961457/100000000000000 : ℝ)*(sp5) + (1437553918165963/100000000000000 : ℝ)*(sp6) + (363715415657267/50000000000000 : ℝ)*(sp7) + (29097235643097/4000000000000 : ℝ)*(f.failure) + (1437559835848021/100000000000000 : ℝ)*(f.sum) + (145947486955659/138365000000000000000000000000 : ℝ)*base65 + (267859783777891313229/27673000000000000000000000000000000 : ℝ)*base68 + (67097948117366686771/27673000000000000000000000000000000 : ℝ)*base69 + (100499795033221313229/27673000000000000000000000000000000 : ℝ)*base72 + (578226822496491/138365000000000000000000000000 : ℝ)*base74 + (56749319387535313229/27673000000000000000000000000000000 : ℝ)*base76 + (23093057010325686771/27673000000000000000000000000000000 : ℝ)*base77 + (74852350154524686771/27673000000000000000000000000000000 : ℝ)*base79 + (417225912873909/138365000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (966817/400000000000000000000 : ℝ)*base89 + (966817/400000000000000000000 : ℝ)*base91 + (966817/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1108_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13973/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5457/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20593/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1108_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1108_s2_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-216481749/1000000000 : ℝ)*x 0 + (5517401561/10000000000 : ℝ)*x 1 + (128834379/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216481749/1000000000 : ℝ)^8301 ≤ (13114647281247/100000000000000 : ℝ)^6253 := by
    have hnat : (216481749 : ℕ)^8301*100000000000000^6253 ≤ 13114647281247^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216481749 1000000000 13114647281247 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5517401561/10000000000 : ℝ)^8301 ≤ (45409507024731/100000000000000 : ℝ)^6253 := by
    have hnat : (5517401561 : ℕ)^8301*100000000000000^6253 ≤ 45409507024731^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517401561 10000000000 45409507024731 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128834379/250000000 : ℝ)^8301 ≤ (41475845681369/100000000000000 : ℝ)^6253 := by
    have hnat : (128834379 : ℕ)^8301*100000000000000^6253 ≤ 41475845681369^6253*250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128834379 250000000 41475845681369 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216481749/1000000000 : ℝ), (5517401561/10000000000 : ℝ), (128834379/250000000 : ℝ)] ![(13114647281247/100000000000000 : ℝ), (45409507024731/100000000000000 : ℝ), (41475845681369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216481749/1000000000 : ℝ)|^8301 ≤ (13114647281247/100000000000000 : ℝ)^6253
        have hw : |(-216481749/1000000000 : ℝ)|=(216481749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5517401561/10000000000 : ℝ)|^8301 ≤ (45409507024731/100000000000000 : ℝ)^6253
        have hw : |(5517401561/10000000000 : ℝ)|=(5517401561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128834379/250000000 : ℝ)|^8301 ≤ (41475845681369/100000000000000 : ℝ)^6253
        have hw : |(128834379/250000000 : ℝ)|=(128834379/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s2_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1075067823/2000000000 : ℝ)*x 0 + (-2354331367/10000000000 : ℝ)*x 1 + (5153376387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075067823/2000000000 : ℝ)^8301 ≤ (43863940704721/100000000000000 : ℝ)^6253 := by
    have hnat : (1075067823 : ℕ)^8301*100000000000000^6253 ≤ 43863940704721^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075067823 2000000000 43863940704721 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2354331367/10000000000 : ℝ)^8301 ≤ (2932040097499/20000000000000 : ℝ)^6253 := by
    have hnat : (2354331367 : ℕ)^8301*20000000000000^6253 ≤ 2932040097499^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354331367 10000000000 2932040097499 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5153376387/10000000000 : ℝ)^8301 ≤ (41475858790987/100000000000000 : ℝ)^6253 := by
    have hnat : (5153376387 : ℕ)^8301*100000000000000^6253 ≤ 41475858790987^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153376387 10000000000 41475858790987 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075067823/2000000000 : ℝ), (-2354331367/10000000000 : ℝ), (5153376387/10000000000 : ℝ)] ![(43863940704721/100000000000000 : ℝ), (2932040097499/20000000000000 : ℝ), (41475858790987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075067823/2000000000 : ℝ)|^8301 ≤ (43863940704721/100000000000000 : ℝ)^6253
        have hw : |(1075067823/2000000000 : ℝ)|=(1075067823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2354331367/10000000000 : ℝ)|^8301 ≤ (2932040097499/20000000000000 : ℝ)^6253
        have hw : |(-2354331367/10000000000 : ℝ)|=(2354331367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5153376387/10000000000 : ℝ)|^8301 ≤ (41475858790987/100000000000000 : ℝ)^6253
        have hw : |(5153376387/10000000000 : ℝ)|=(5153376387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s2_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671917383/1250000000 : ℝ)*x 0 + (2576688221/5000000000 : ℝ)*x 1 + (-2354331363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671917383/1250000000 : ℝ)^8301 ≤ (10965985038061/25000000000000 : ℝ)^6253 := by
    have hnat : (671917383 : ℕ)^8301*25000000000000^6253 ≤ 10965985038061^6253*1250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671917383 1250000000 10965985038061 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2576688221/5000000000 : ℝ)^8301 ≤ (41475859378623/100000000000000 : ℝ)^6253 := by
    have hnat : (2576688221 : ℕ)^8301*100000000000000^6253 ≤ 41475859378623^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576688221 5000000000 41475859378623 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2354331363/10000000000 : ℝ)^8301 ≤ (14660200454429/100000000000000 : ℝ)^6253 := by
    have hnat : (2354331363 : ℕ)^8301*100000000000000^6253 ≤ 14660200454429^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354331363 10000000000 14660200454429 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671917383/1250000000 : ℝ), (2576688221/5000000000 : ℝ), (-2354331363/10000000000 : ℝ)] ![(10965985038061/25000000000000 : ℝ), (41475859378623/100000000000000 : ℝ), (14660200454429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671917383/1250000000 : ℝ)|^8301 ≤ (10965985038061/25000000000000 : ℝ)^6253
        have hw : |(671917383/1250000000 : ℝ)|=(671917383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2576688221/5000000000 : ℝ)|^8301 ≤ (41475859378623/100000000000000 : ℝ)^6253
        have hw : |(2576688221/5000000000 : ℝ)|=(2576688221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2354331363/10000000000 : ℝ)|^8301 ≤ (14660200454429/100000000000000 : ℝ)^6253
        have hw : |(-2354331363/10000000000 : ℝ)|=(2354331363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s2_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179000877/5000000000 : ℝ)*x 0 + (4013131873/10000000000 : ℝ)*x 1 + (4732523707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179000877/5000000000 : ℝ)^8301 ≤ (16600295099919/50000000000000 : ℝ)^6253 := by
    have hnat : (2179000877 : ℕ)^8301*50000000000000^6253 ≤ 16600295099919^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179000877 5000000000 16600295099919 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4013131873/10000000000 : ℝ)^8301 ≤ (7439696639443/25000000000000 : ℝ)^6253 := by
    have hnat : (4013131873 : ℕ)^8301*25000000000000^6253 ≤ 7439696639443^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013131873 10000000000 7439696639443 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4732523707/10000000000 : ℝ)^8301 ≤ (18520311612193/50000000000000 : ℝ)^6253 := by
    have hnat : (4732523707 : ℕ)^8301*50000000000000^6253 ≤ 18520311612193^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4732523707 10000000000 18520311612193 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179000877/5000000000 : ℝ), (4013131873/10000000000 : ℝ), (4732523707/10000000000 : ℝ)] ![(16600295099919/50000000000000 : ℝ), (7439696639443/25000000000000 : ℝ), (18520311612193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179000877/5000000000 : ℝ)|^8301 ≤ (16600295099919/50000000000000 : ℝ)^6253
        have hw : |(2179000877/5000000000 : ℝ)|=(2179000877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4013131873/10000000000 : ℝ)|^8301 ≤ (7439696639443/25000000000000 : ℝ)^6253
        have hw : |(4013131873/10000000000 : ℝ)|=(4013131873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4732523707/10000000000 : ℝ)|^8301 ≤ (18520311612193/50000000000000 : ℝ)^6253
        have hw : |(4732523707/10000000000 : ℝ)|=(4732523707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s2_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-270616209/1250000000 : ℝ)*x 0 + (5155946203/10000000000 : ℝ)*x 1 + (8823687/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270616209/1250000000 : ℝ)^8301 ≤ (6557774742029/50000000000000 : ℝ)^6253 := by
    have hnat : (270616209 : ℕ)^8301*50000000000000^6253 ≤ 6557774742029^6253*1250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270616209 1250000000 6557774742029 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5155946203/10000000000 : ℝ)^8301 ≤ (41503317682299/100000000000000 : ℝ)^6253 := by
    have hnat : (5155946203 : ℕ)^8301*100000000000000^6253 ≤ 41503317682299^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155946203 10000000000 41503317682299 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8823687/16000000 : ℝ)^8301 ≤ (22690566408339/50000000000000 : ℝ)^6253 := by
    have hnat : (8823687 : ℕ)^8301*50000000000000^6253 ≤ 22690566408339^6253*16000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8823687 16000000 22690566408339 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270616209/1250000000 : ℝ), (5155946203/10000000000 : ℝ), (8823687/16000000 : ℝ)] ![(6557774742029/50000000000000 : ℝ), (41503317682299/100000000000000 : ℝ), (22690566408339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270616209/1250000000 : ℝ)|^8301 ≤ (6557774742029/50000000000000 : ℝ)^6253
        have hw : |(-270616209/1250000000 : ℝ)|=(270616209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5155946203/10000000000 : ℝ)|^8301 ≤ (41503317682299/100000000000000 : ℝ)^6253
        have hw : |(5155946203/10000000000 : ℝ)|=(5155946203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8823687/16000000 : ℝ)|^8301 ≤ (22690566408339/50000000000000 : ℝ)^6253
        have hw : |(8823687/16000000 : ℝ)|=(8823687/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s2_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330199223/625000000 : ℝ)*x 0 + (-398580557/2000000000 : ℝ)*x 1 + (5514804459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330199223/625000000 : ℝ)^8301 ≤ (10717121962353/25000000000000 : ℝ)^6253 := by
    have hnat : (330199223 : ℕ)^8301*25000000000000^6253 ≤ 10717121962353^6253*625000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330199223 625000000 10717121962353 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398580557/2000000000 : ℝ)^8301 ≤ (11750378396257/100000000000000 : ℝ)^6253 := by
    have hnat : (398580557 : ℕ)^8301*100000000000000^6253 ≤ 11750378396257^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398580557 2000000000 11750378396257 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5514804459/10000000000 : ℝ)^8301 ≤ (22690566867153/50000000000000 : ℝ)^6253 := by
    have hnat : (5514804459 : ℕ)^8301*50000000000000^6253 ≤ 22690566867153^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514804459 10000000000 22690566867153 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330199223/625000000 : ℝ), (-398580557/2000000000 : ℝ), (5514804459/10000000000 : ℝ)] ![(10717121962353/25000000000000 : ℝ), (11750378396257/100000000000000 : ℝ), (22690566867153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330199223/625000000 : ℝ)|^8301 ≤ (10717121962353/25000000000000 : ℝ)^6253
        have hw : |(330199223/625000000 : ℝ)|=(330199223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-398580557/2000000000 : ℝ)|^8301 ≤ (11750378396257/100000000000000 : ℝ)^6253
        have hw : |(-398580557/2000000000 : ℝ)|=(398580557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5514804459/10000000000 : ℝ)|^8301 ≤ (22690566867153/50000000000000 : ℝ)^6253
        have hw : |(5514804459/10000000000 : ℝ)|=(5514804459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s2_6 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1320796927/2500000000 : ℝ)*x 0 + (2757402201/5000000000 : ℝ)*x 1 + (-124556417/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320796927/2500000000 : ℝ)^8301 ≤ (42868489357449/100000000000000 : ℝ)^6253 := by
    have hnat : (1320796927 : ℕ)^8301*100000000000000^6253 ≤ 42868489357449^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320796927 2500000000 42868489357449 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757402201/5000000000 : ℝ)^8301 ≤ (4538113311163/10000000000000 : ℝ)^6253 := by
    have hnat : (2757402201 : ℕ)^8301*10000000000000^6253 ≤ 4538113311163^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757402201 5000000000 4538113311163 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124556417/625000000 : ℝ)^8301 ≤ (11750377511781/100000000000000 : ℝ)^6253 := by
    have hnat : (124556417 : ℕ)^8301*100000000000000^6253 ≤ 11750377511781^6253*625000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124556417 625000000 11750377511781 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320796927/2500000000 : ℝ), (2757402201/5000000000 : ℝ), (-124556417/625000000 : ℝ)] ![(42868489357449/100000000000000 : ℝ), (4538113311163/10000000000000 : ℝ), (11750377511781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320796927/2500000000 : ℝ)|^8301 ≤ (42868489357449/100000000000000 : ℝ)^6253
        have hw : |(1320796927/2500000000 : ℝ)|=(1320796927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757402201/5000000000 : ℝ)|^8301 ≤ (4538113311163/10000000000000 : ℝ)^6253
        have hw : |(2757402201/5000000000 : ℝ)|=(2757402201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124556417/625000000 : ℝ)|^8301 ≤ (11750377511781/100000000000000 : ℝ)^6253
        have hw : |(-124556417/625000000 : ℝ)|=(124556417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s2_7 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358224787/10000000000 : ℝ)*x 0 + (4727443861/10000000000 : ℝ)*x 1 + (4018262439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358224787/10000000000 : ℝ)^8301 ≤ (16601422928663/50000000000000 : ℝ)^6253 := by
    have hnat : (4358224787 : ℕ)^8301*50000000000000^6253 ≤ 16601422928663^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358224787 10000000000 16601422928663 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4727443861/10000000000 : ℝ)^8301 ≤ (7397570291061/20000000000000 : ℝ)^6253 := by
    have hnat : (4727443861 : ℕ)^8301*20000000000000^6253 ≤ 7397570291061^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4727443861 10000000000 7397570291061 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018262439/10000000000 : ℝ)^8301 ≤ (14904651336177/50000000000000 : ℝ)^6253 := by
    have hnat : (4018262439 : ℕ)^8301*50000000000000^6253 ≤ 14904651336177^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018262439 10000000000 14904651336177 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358224787/10000000000 : ℝ), (4727443861/10000000000 : ℝ), (4018262439/10000000000 : ℝ)] ![(16601422928663/50000000000000 : ℝ), (7397570291061/20000000000000 : ℝ), (14904651336177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358224787/10000000000 : ℝ)|^8301 ≤ (16601422928663/50000000000000 : ℝ)^6253
        have hw : |(4358224787/10000000000 : ℝ)|=(4358224787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4727443861/10000000000 : ℝ)|^8301 ≤ (7397570291061/20000000000000 : ℝ)^6253
        have hw : |(4727443861/10000000000 : ℝ)|=(4727443861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018262439/10000000000 : ℝ)|^8301 ≤ (14904651336177/50000000000000 : ℝ)^6253
        have hw : |(4018262439/10000000000 : ℝ)|=(4018262439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20593/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5457/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8913/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8303/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20593/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5457/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20593/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5457/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20593/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5457/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20593/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5457/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20593/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5457/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20593/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5457/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5457/100000 : ℝ) ^ (2075/512 : ℝ) ≤ (152138758149289/20000000000000000000 : ℝ) := by
    have hpowers : (5457/100000 : ℝ)^2075 ≤ (152138758149289/20000000000000000000 : ℝ)^512 := by
      have hnat : (5457 : ℕ)^2075*20000000000000000000^512 ≤ 152138758149289^512*100000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5457 100000 152138758149289 20000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5457/100000 : ℝ)) (X := (152138758149289/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20593/100000 : ℝ) ^ (2075/512 : ℝ) ≤ (41364513393442199/25000000000000000000 : ℝ) := by
    have hpowers : (20593/100000 : ℝ)^2075 ≤ (41364513393442199/25000000000000000000 : ℝ)^512 := by
      have hnat : (20593 : ℕ)^2075*25000000000000000000^512 ≤ 41364513393442199^512*100000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20593 100000 41364513393442199 25000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20593/100000 : ℝ)) (X := (41364513393442199/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000152138758149289/10000000000000000000 : ℝ) ≤ (400001501582609/400000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (10000152138758149289/10000000000000000000 : ℝ)^512 ≤ (400001501582609/400000000000000 : ℝ)^2075 := by
      have hnat : (10000152138758149289 : ℕ)^512*400000000000000^2075 ≤ 400001501582609^2075*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000152138758149289 10000000000000000000 400001501582609 400000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400001501582609/400000000000000 : ℝ)) (X := (10000152138758149289/10000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100166218747364515241/100000000000000000000 : ℝ) ≤ (500204941622197/500000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (100166218747364515241/100000000000000000000 : ℝ)^512 ≤ (500204941622197/500000000000000 : ℝ)^2075 := by
      have hnat : (100166218747364515241 : ℕ)^512*500000000000000^2075 ≤ 500204941622197^2075*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100166218747364515241 100000000000000000000 500204941622197 500000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500204941622197/500000000000000 : ℝ)) (X := (100166218747364515241/100000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12541364513393442199/12500000000000000000 : ℝ) ≤ (2001632025064531/2000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (12541364513393442199/12500000000000000000 : ℝ)^512 ≤ (2001632025064531/2000000000000000 : ℝ)^2075 := by
      have hnat : (12541364513393442199 : ℕ)^512*2000000000000000^2075 ≤ 2001632025064531^2075*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12541364513393442199 12500000000000000000 2001632025064531 2000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001632025064531/2000000000000000 : ℝ)) (X := (12541364513393442199/12500000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(152138758149289/20000000000000000000 : ℝ) ≤ ((15131624324838095009/15136000000000000000 : ℝ)+2*(812258575743/302720000000000 : ℝ)*(5457/100000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (15131624324838095009/15136000000000000000 : ℝ)+2*(812258575743/302720000000000 : ℝ)*(5457/100000 : ℝ)=(400001501582609/400000000000000 : ℝ) by norm_num, show 1+2*(152138758149289/20000000000000000000 : ℝ)=(10000152138758149289/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41364513393442199/25000000000000000000 : ℝ)+(152138758149289/20000000000000000000 : ℝ) ≤ ((15131624324838095009/15136000000000000000 : ℝ)+(812258575743/302720000000000 : ℝ)*((20593/100000 : ℝ)+(5457/100000 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (15131624324838095009/15136000000000000000 : ℝ)+(812258575743/302720000000000 : ℝ)*((20593/100000 : ℝ)+(5457/100000 : ℝ))=(500204941622197/500000000000000 : ℝ) by norm_num, show 1+(41364513393442199/25000000000000000000 : ℝ)+(152138758149289/20000000000000000000 : ℝ)=(100166218747364515241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41364513393442199/25000000000000000000 : ℝ) ≤ ((15131624324838095009/15136000000000000000 : ℝ)+2*(812258575743/302720000000000 : ℝ)*(20593/100000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (15131624324838095009/15136000000000000000 : ℝ)+2*(812258575743/302720000000000 : ℝ)*(20593/100000 : ℝ)=(2001632025064531/2000000000000000 : ℝ) by norm_num, show 1+2*(41364513393442199/25000000000000000000 : ℝ)=(12541364513393442199/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15131624324838095009/15136000000000000000 : ℝ)*(X 1 0+X 2 0)+(812258575743/302720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (5457/100000 : ℝ)) (hi := (20593/100000 : ℝ)) (c := (15131624324838095009/15136000000000000000 : ℝ)) (alpha := (812258575743/302720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15131624324838095009/15136000000000000000 : ℝ)*(X 0 1+X 2 1)+(812258575743/302720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (5457/100000 : ℝ)) (hi := (20593/100000 : ℝ)) (c := (15131624324838095009/15136000000000000000 : ℝ)) (alpha := (812258575743/302720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15131624324838095009/15136000000000000000 : ℝ)*(X 0 2+X 1 2)+(812258575743/302720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (5457/100000 : ℝ)) (hi := (20593/100000 : ℝ)) (c := (15131624324838095009/15136000000000000000 : ℝ)) (alpha := (812258575743/302720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-216481749/1000000000 : ℝ)*X 0 0+(5517401561/10000000000 : ℝ)*X 0 1+(128834379/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075067823/2000000000 : ℝ)*X 1 0+(-2354331367/10000000000 : ℝ)*X 1 1+(5153376387/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671917383/1250000000 : ℝ)*X 2 0+(2576688221/5000000000 : ℝ)*X 2 1+(-2354331363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179000877/5000000000 : ℝ)*X 0 0+(4013131873/10000000000 : ℝ)*X 0 1+(4732523707/10000000000 : ℝ)*X 0 2+(2179000877/5000000000 : ℝ)*X 1 0+(4013131873/10000000000 : ℝ)*X 1 1+(4732523707/10000000000 : ℝ)*X 1 2+(2179000877/5000000000 : ℝ)*X 2 0+(4013131873/10000000000 : ℝ)*X 2 1+(4732523707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-270616209/1250000000 : ℝ)*X 0 0+(5155946203/10000000000 : ℝ)*X 0 1+(8823687/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330199223/625000000 : ℝ)*X 1 0+(-398580557/2000000000 : ℝ)*X 1 1+(5514804459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1320796927/2500000000 : ℝ)*X 2 0+(2757402201/5000000000 : ℝ)*X 2 1+(-124556417/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358224787/10000000000 : ℝ)*X 0 0+(4727443861/10000000000 : ℝ)*X 0 1+(4018262439/10000000000 : ℝ)*X 0 2+(4358224787/10000000000 : ℝ)*X 1 0+(4727443861/10000000000 : ℝ)*X 1 1+(4018262439/10000000000 : ℝ)*X 1 2+(4358224787/10000000000 : ℝ)*X 2 0+(4727443861/10000000000 : ℝ)*X 2 1+(4018262439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89586076740321203739207/7568000000000000000000000000 : ℝ) := by norm_num
    linear_combination (830835051/50000000000000 : ℝ)*(base19) + (1444892131/100000000000000 : ℝ)*(base23) + (27707281/10000000000000 : ℝ)*(upper3) + (51257647/50000000000000 : ℝ)*(upper4) + (127486539/100000000000000 : ℝ)*(upper5) + (1034296507243613/50000000000000 : ℝ)*(major0) + (1034296507243613/50000000000000 : ℝ)*(major1) + (1034296507243613/50000000000000 : ℝ)*(major2) + (137353937168383/5000000000000 : ℝ)*(sp0) + (1373550512012283/50000000000000 : ℝ)*(sp1) + (343387655100317/12500000000000 : ℝ)*(sp2) + (173759028232409/12500000000000 : ℝ)*(sp3) + (23942327007/100000000000000 : ℝ)*(sp4) + (2144567543/20000000000000 : ℝ)*(sp7) + (347520737174247/25000000000000 : ℝ)*(f.failure) + (2747102685694667/100000000000000 : ℝ)*(f.sum) + (33951467193107/7568000000000000000000000000 : ℝ)*base65 + (4700993609261777517/756800000000000000000000000000000 : ℝ)*base67 + (2500574170139822483/756800000000000000000000000000000 : ℝ)*base70 + (1643833311720977517/756800000000000000000000000000000 : ℝ)*base71 + (39518089462227/7568000000000000000000000000 : ℝ)*base73 + (1332636377245422483/756800000000000000000000000000000 : ℝ)*base76 + (3058771404165777517/756800000000000000000000000000000 : ℝ)*base77 + (2707575293559022483/756800000000000000000000000000000 : ℝ)*base80 + (4593355268269/7568000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (35671967/2500000000000000000000 : ℝ)*base89 + (35671967/2500000000000000000000 : ℝ)*base91 + (35671967/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3806017144839470684674466913/756800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1009960477/100000000000000 : ℝ)*(base19) + (23814377/2000000000000 : ℝ)*(base23) + (9096223/6250000000000 : ℝ)*(upper3) + (1070077/3125000000000 : ℝ)*(lower4) + (11321677/12500000000000 : ℝ)*(upper5) + (2098346189301781/100000000000000 : ℝ)*(major0) + (2098346189301781/100000000000000 : ℝ)*(major1) + (2098346189301781/100000000000000 : ℝ)*(major2) + (457705211/5000000000000 : ℝ)*(sp1) + (289196677/2500000000000 : ℝ)*(sp2) + (2786615295023021/100000000000000 : ℝ)*(sp4) + (696651282739581/25000000000000 : ℝ)*(sp5) + (696650634109273/25000000000000 : ℝ)*(sp6) + (352519228986031/25000000000000 : ℝ)*(sp7) + (352519228986031/25000000000000 : ℝ)*(f.failure) + (2786615295023021/100000000000000 : ℝ)*(f.sum) + (21420592301547/15136000000000000000000000000 : ℝ)*base65 + (5274963376697861029/1513600000000000000000000000000000 : ℝ)*base67 + (580512870035461029/1513600000000000000000000000000000 : ℝ)*base69 + (739732073053061029/1513600000000000000000000000000000 : ℝ)*base71 + (6329738110741/15136000000000000000000000000 : ℝ)*base74 + (10136016517993861029/1513600000000000000000000000000000 : ℝ)*base75 + (3828005351113338971/1513600000000000000000000000000000 : ℝ)*base78 + (1830585024303738971/1513600000000000000000000000000000 : ℝ)*base80 + (2618343807509/15136000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6479591/2500000000000000000000 : ℝ)*base89 + (6479591/2500000000000000000000 : ℝ)*base91 + (6479591/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1108_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20593/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5457/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8303/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1108_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1108_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8303/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1108_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1108_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1108_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8303/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1108_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
