-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1299_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:36:00.131405+00:00
-- url     : https://prove2.me/submissions/08d8a2a5-838a-439e-9a11-cea2184bc503

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
theorem support_rectangle_w1299_s0_0 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-366968387/2000000000 : ℝ)*x 0 + (1203139251/2000000000 : ℝ)*x 1 + (1200136677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366968387/2000000000 : ℝ)^4259 ≤ (2145506045637/20000000000000 : ℝ)^3235 := by
    have hnat : (366968387 : ℕ)^4259*20000000000000^3235 ≤ 2145506045637^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366968387 2000000000 2145506045637 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203139251/2000000000 : ℝ)^4259 ≤ (51217871849543/100000000000000 : ℝ)^3235 := by
    have hnat : (1203139251 : ℕ)^4259*100000000000000^3235 ≤ 51217871849543^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203139251 2000000000 51217871849543 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200136677/2500000000 : ℝ)^4259 ≤ (38054597906903/100000000000000 : ℝ)^3235 := by
    have hnat : (1200136677 : ℕ)^4259*100000000000000^3235 ≤ 38054597906903^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200136677 2500000000 38054597906903 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-366968387/2000000000 : ℝ), (1203139251/2000000000 : ℝ), (1200136677/2500000000 : ℝ)] ![(2145506045637/20000000000000 : ℝ), (51217871849543/100000000000000 : ℝ), (38054597906903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-366968387/2000000000 : ℝ)|^4259 ≤ (2145506045637/20000000000000 : ℝ)^3235
        have hw : |(-366968387/2000000000 : ℝ)|=(366968387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203139251/2000000000 : ℝ)|^4259 ≤ (51217871849543/100000000000000 : ℝ)^3235
        have hw : |(1203139251/2000000000 : ℝ)|=(1203139251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200136677/2500000000 : ℝ)|^4259 ≤ (38054597906903/100000000000000 : ℝ)^3235
        have hw : |(1200136677/2500000000 : ℝ)|=(1200136677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s0_1 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2753316477/5000000000 : ℝ)*x 0 + (-1263857819/5000000000 : ℝ)*x 1 + (4800546681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753316477/5000000000 : ℝ)^4259 ≤ (22794852265083/50000000000000 : ℝ)^3235 := by
    have hnat : (2753316477 : ℕ)^4259*50000000000000^3235 ≤ 22794852265083^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753316477 5000000000 22794852265083 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1263857819/5000000000 : ℝ)^4259 ≤ (3271139566361/20000000000000 : ℝ)^3235 := by
    have hnat : (1263857819 : ℕ)^4259*20000000000000^3235 ≤ 3271139566361^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263857819 5000000000 3271139566361 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4800546681/10000000000 : ℝ)^4259 ≤ (38054597625121/100000000000000 : ℝ)^3235 := by
    have hnat : (4800546681 : ℕ)^4259*100000000000000^3235 ≤ 38054597625121^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800546681 10000000000 38054597625121 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753316477/5000000000 : ℝ), (-1263857819/5000000000 : ℝ), (4800546681/10000000000 : ℝ)] ![(22794852265083/50000000000000 : ℝ), (3271139566361/20000000000000 : ℝ), (38054597625121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753316477/5000000000 : ℝ)|^4259 ≤ (22794852265083/50000000000000 : ℝ)^3235
        have hw : |(2753316477/5000000000 : ℝ)|=(2753316477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1263857819/5000000000 : ℝ)|^4259 ≤ (3271139566361/20000000000000 : ℝ)^3235
        have hw : |(-1263857819/5000000000 : ℝ)|=(1263857819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4800546681/10000000000 : ℝ)|^4259 ≤ (38054597625121/100000000000000 : ℝ)^3235
        have hw : |(4800546681/10000000000 : ℝ)|=(4800546681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s0_2 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5506632927/10000000000 : ℝ)*x 0 + (30003417/62500000 : ℝ)*x 1 + (-315964453/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5506632927/10000000000 : ℝ)^4259 ≤ (22794852117937/50000000000000 : ℝ)^3235 := by
    have hnat : (5506632927 : ℕ)^4259*50000000000000^3235 ≤ 22794852117937^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506632927 10000000000 22794852117937 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30003417/62500000 : ℝ)^4259 ≤ (1902729901607/5000000000000 : ℝ)^3235 := by
    have hnat : (30003417 : ℕ)^4259*5000000000000^3235 ≤ 1902729901607^3235*62500000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30003417 62500000 1902729901607 5000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315964453/1250000000 : ℝ)^4259 ≤ (16355697712543/100000000000000 : ℝ)^3235 := by
    have hnat : (315964453 : ℕ)^4259*100000000000000^3235 ≤ 16355697712543^3235*1250000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315964453 1250000000 16355697712543 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5506632927/10000000000 : ℝ), (30003417/62500000 : ℝ), (-315964453/1250000000 : ℝ)] ![(22794852117937/50000000000000 : ℝ), (1902729901607/5000000000000 : ℝ), (16355697712543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5506632927/10000000000 : ℝ)|^4259 ≤ (22794852117937/50000000000000 : ℝ)^3235
        have hw : |(5506632927/10000000000 : ℝ)|=(5506632927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30003417/62500000 : ℝ)|^4259 ≤ (1902729901607/5000000000000 : ℝ)^3235
        have hw : |(30003417/62500000 : ℝ)|=(30003417/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-315964453/1250000000 : ℝ)|^4259 ≤ (16355697712543/100000000000000 : ℝ)^3235
        have hw : |(-315964453/1250000000 : ℝ)|=(315964453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s0_3 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2092628691/5000000000 : ℝ)*x 0 + (777246211/2500000000 : ℝ)*x 1 + (2806543391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092628691/5000000000 : ℝ)^4259 ≤ (3176749088319/10000000000000 : ℝ)^3235 := by
    have hnat : (2092628691 : ℕ)^4259*10000000000000^3235 ≤ 3176749088319^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092628691 5000000000 3176749088319 10000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777246211/2500000000 : ℝ)^4259 ≤ (4295791318291/20000000000000 : ℝ)^3235 := by
    have hnat : (777246211 : ℕ)^4259*20000000000000^3235 ≤ 4295791318291^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777246211 2500000000 4295791318291 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2806543391/5000000000 : ℝ)^4259 ≤ (11688388126953/25000000000000 : ℝ)^3235 := by
    have hnat : (2806543391 : ℕ)^4259*25000000000000^3235 ≤ 11688388126953^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806543391 5000000000 11688388126953 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092628691/5000000000 : ℝ), (777246211/2500000000 : ℝ), (2806543391/5000000000 : ℝ)] ![(3176749088319/10000000000000 : ℝ), (4295791318291/20000000000000 : ℝ), (11688388126953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092628691/5000000000 : ℝ)|^4259 ≤ (3176749088319/10000000000000 : ℝ)^3235
        have hw : |(2092628691/5000000000 : ℝ)|=(2092628691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(777246211/2500000000 : ℝ)|^4259 ≤ (4295791318291/20000000000000 : ℝ)^3235
        have hw : |(777246211/2500000000 : ℝ)|=(777246211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2806543391/5000000000 : ℝ)|^4259 ≤ (11688388126953/25000000000000 : ℝ)^3235
        have hw : |(2806543391/5000000000 : ℝ)|=(2806543391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s0_4 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1839526793/10000000000 : ℝ)*x 0 + (966379753/2000000000 : ℝ)*x 1 + (5983229123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1839526793/10000000000 : ℝ)^4259 ≤ (10763605219847/100000000000000 : ℝ)^3235 := by
    have hnat : (1839526793 : ℕ)^4259*100000000000000^3235 ≤ 10763605219847^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839526793 10000000000 10763605219847 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966379753/2000000000 : ℝ)^4259 ≤ (19191068763747/50000000000000 : ℝ)^3235 := by
    have hnat : (966379753 : ℕ)^4259*50000000000000^3235 ≤ 19191068763747^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966379753 2000000000 19191068763747 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5983229123/10000000000 : ℝ)^4259 ≤ (5085425723871/10000000000000 : ℝ)^3235 := by
    have hnat : (5983229123 : ℕ)^4259*10000000000000^3235 ≤ 5085425723871^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5983229123 10000000000 5085425723871 10000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1839526793/10000000000 : ℝ), (966379753/2000000000 : ℝ), (5983229123/10000000000 : ℝ)] ![(10763605219847/100000000000000 : ℝ), (19191068763747/50000000000000 : ℝ), (5085425723871/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1839526793/10000000000 : ℝ)|^4259 ≤ (10763605219847/100000000000000 : ℝ)^3235
        have hw : |(-1839526793/10000000000 : ℝ)|=(1839526793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(966379753/2000000000 : ℝ)|^4259 ≤ (19191068763747/50000000000000 : ℝ)^3235
        have hw : |(966379753/2000000000 : ℝ)|=(966379753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5983229123/10000000000 : ℝ)|^4259 ≤ (5085425723871/10000000000000 : ℝ)^3235
        have hw : |(5983229123/10000000000 : ℝ)|=(5983229123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s0_5 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2587882323/5000000000 : ℝ)*x 0 + (-1345030469/10000000000 : ℝ)*x 1 + (2991615893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587882323/5000000000 : ℝ)^4259 ≤ (8403624140113/20000000000000 : ℝ)^3235 := by
    have hnat : (2587882323 : ℕ)^4259*20000000000000^3235 ≤ 8403624140113^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587882323 5000000000 8403624140113 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1345030469/10000000000 : ℝ)^4259 ≤ (3563796124991/50000000000000 : ℝ)^3235 := by
    have hnat : (1345030469 : ℕ)^4259*50000000000000^3235 ≤ 3563796124991^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345030469 10000000000 3563796124991 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2991615893/5000000000 : ℝ)^4259 ≤ (6356785879667/12500000000000 : ℝ)^3235 := by
    have hnat : (2991615893 : ℕ)^4259*12500000000000^3235 ≤ 6356785879667^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991615893 5000000000 6356785879667 12500000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587882323/5000000000 : ℝ), (-1345030469/10000000000 : ℝ), (2991615893/5000000000 : ℝ)] ![(8403624140113/20000000000000 : ℝ), (3563796124991/50000000000000 : ℝ), (6356785879667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587882323/5000000000 : ℝ)|^4259 ≤ (8403624140113/20000000000000 : ℝ)^3235
        have hw : |(2587882323/5000000000 : ℝ)|=(2587882323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1345030469/10000000000 : ℝ)|^4259 ≤ (3563796124991/50000000000000 : ℝ)^3235
        have hw : |(-1345030469/10000000000 : ℝ)|=(1345030469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2991615893/5000000000 : ℝ)|^4259 ≤ (6356785879667/12500000000000 : ℝ)^3235
        have hw : |(2991615893/5000000000 : ℝ)|=(2991615893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s0_6 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035153193/2000000000 : ℝ)*x 0 + (598322947/1000000000 : ℝ)*x 1 + (-1345032163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035153193/2000000000 : ℝ)^4259 ≤ (21009067399003/50000000000000 : ℝ)^3235 := by
    have hnat : (1035153193 : ℕ)^4259*50000000000000^3235 ≤ 21009067399003^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035153193 2000000000 21009067399003 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598322947/1000000000 : ℝ)^4259 ≤ (10170852224319/20000000000000 : ℝ)^3235 := by
    have hnat : (598322947 : ℕ)^4259*20000000000000^3235 ≤ 10170852224319^3235*1000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598322947 1000000000 10170852224319 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1345032163/10000000000 : ℝ)^4259 ≤ (7127604068351/100000000000000 : ℝ)^3235 := by
    have hnat : (1345032163 : ℕ)^4259*100000000000000^3235 ≤ 7127604068351^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345032163 10000000000 7127604068351 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035153193/2000000000 : ℝ), (598322947/1000000000 : ℝ), (-1345032163/10000000000 : ℝ)] ![(21009067399003/50000000000000 : ℝ), (10170852224319/20000000000000 : ℝ), (7127604068351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035153193/2000000000 : ℝ)|^4259 ≤ (21009067399003/50000000000000 : ℝ)^3235
        have hw : |(1035153193/2000000000 : ℝ)|=(1035153193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598322947/1000000000 : ℝ)|^4259 ≤ (10170852224319/20000000000000 : ℝ)^3235
        have hw : |(598322947/1000000000 : ℝ)|=(598322947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1345032163/10000000000 : ℝ)|^4259 ≤ (7127604068351/100000000000000 : ℝ)^3235
        have hw : |(-1345032163/10000000000 : ℝ)|=(1345032163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s0_7 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4194917779/10000000000 : ℝ)*x 0 + (2774243251/5000000000 : ℝ)*x 1 + (79397081/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4194917779/10000000000 : ℝ)^4259 ≤ (1274562483209/4000000000000 : ℝ)^3235 := by
    have hnat : (4194917779 : ℕ)^4259*4000000000000^3235 ≤ 1274562483209^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194917779 10000000000 1274562483209 4000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2774243251/5000000000 : ℝ)^4259 ≤ (9209288579677/20000000000000 : ℝ)^3235 := by
    have hnat : (2774243251 : ℕ)^4259*20000000000000^3235 ≤ 9209288579677^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774243251 5000000000 9209288579677 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79397081/250000000 : ℝ)^4259 ≤ (22089495002039/100000000000000 : ℝ)^3235 := by
    have hnat : (79397081 : ℕ)^4259*100000000000000^3235 ≤ 22089495002039^3235*250000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79397081 250000000 22089495002039 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4194917779/10000000000 : ℝ), (2774243251/5000000000 : ℝ), (79397081/250000000 : ℝ)] ![(1274562483209/4000000000000 : ℝ), (9209288579677/20000000000000 : ℝ), (22089495002039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4194917779/10000000000 : ℝ)|^4259 ≤ (1274562483209/4000000000000 : ℝ)^3235
        have hw : |(4194917779/10000000000 : ℝ)|=(4194917779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2774243251/5000000000 : ℝ)|^4259 ≤ (9209288579677/20000000000000 : ℝ)^3235
        have hw : |(2774243251/5000000000 : ℝ)|=(2774243251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79397081/250000000 : ℝ)|^4259 ≤ (22089495002039/100000000000000 : ℝ)^3235
        have hw : |(79397081/250000000 : ℝ)|=(79397081/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1299_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1087/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1699/6250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2129/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2129 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2129*1^512 ≤ 0^512*1^2129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2129 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2129/512 : ℝ) ≤ (2214545523765761867/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2129 ≤ (2214545523765761867/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2129*100000000000000000000^512 ≤ 2214545523765761867^512*5^2129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2214545523765761867 100000000000000000000 2129 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2214545523765761867/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2129 := by
      have hnat : (1 : ℕ)^512*1^2129 ≤ 1^2129*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102214545523765761867/100000000000000000000 : ℝ) ≤ (1005281511489543/1000000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (102214545523765761867/100000000000000000000 : ℝ)^512 ≤ (1005281511489543/1000000000000000 : ℝ)^2129 := by
      have hnat : (102214545523765761867 : ℕ)^512*1000000000000000^2129 ≤ 1005281511489543^2129*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102214545523765761867 100000000000000000000 1005281511489543 1000000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005281511489543/1000000000000000 : ℝ)) (X := (102214545523765761867/100000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52214545523765761867/50000000000000000000 : ℝ) ≤ (505281511489543/500000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (52214545523765761867/50000000000000000000 : ℝ)^512 ≤ (505281511489543/500000000000000 : ℝ)^2129 := by
      have hnat : (52214545523765761867 : ℕ)^512*500000000000000^2129 ≤ 505281511489543^2129*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52214545523765761867 50000000000000000000 505281511489543 500000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (505281511489543/500000000000000 : ℝ)) (X := (52214545523765761867/50000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5281511489543/400000000000000 : ℝ)*(0 : ℝ))^(2129/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(5281511489543/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2214545523765761867/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5281511489543/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2129/512 : ℝ) := by
    rw [show (1 : ℝ)+(5281511489543/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1005281511489543/1000000000000000 : ℝ) by norm_num, show 1+(2214545523765761867/100000000000000000000 : ℝ)+(0 : ℝ)=(102214545523765761867/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2214545523765761867/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5281511489543/400000000000000 : ℝ)*(2/5 : ℝ))^(2129/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(5281511489543/400000000000000 : ℝ)*(2/5 : ℝ)=(505281511489543/500000000000000 : ℝ) by norm_num, show 1+2*(2214545523765761867/100000000000000000000 : ℝ)=(52214545523765761867/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5281511489543/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5281511489543/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5281511489543/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5281511489543/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5281511489543/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5281511489543/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-366968387/2000000000 : ℝ)*X 0 0+(1203139251/2000000000 : ℝ)*X 0 1+(1200136677/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2753316477/5000000000 : ℝ)*X 1 0+(-1263857819/5000000000 : ℝ)*X 1 1+(4800546681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5506632927/10000000000 : ℝ)*X 2 0+(30003417/62500000 : ℝ)*X 2 1+(-315964453/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2092628691/5000000000 : ℝ)*X 0 0+(777246211/2500000000 : ℝ)*X 0 1+(2806543391/5000000000 : ℝ)*X 0 2+(2092628691/5000000000 : ℝ)*X 1 0+(777246211/2500000000 : ℝ)*X 1 1+(2806543391/5000000000 : ℝ)*X 1 2+(2092628691/5000000000 : ℝ)*X 2 0+(777246211/2500000000 : ℝ)*X 2 1+(2806543391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1839526793/10000000000 : ℝ)*X 0 0+(966379753/2000000000 : ℝ)*X 0 1+(5983229123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587882323/5000000000 : ℝ)*X 1 0+(-1345030469/10000000000 : ℝ)*X 1 1+(2991615893/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1035153193/2000000000 : ℝ)*X 2 0+(598322947/1000000000 : ℝ)*X 2 1+(-1345032163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4194917779/10000000000 : ℝ)*X 0 0+(2774243251/5000000000 : ℝ)*X 0 1+(79397081/250000000 : ℝ)*X 0 2+(4194917779/10000000000 : ℝ)*X 1 0+(2774243251/5000000000 : ℝ)*X 1 1+(79397081/250000000 : ℝ)*X 1 2+(4194917779/10000000000 : ℝ)*X 2 0+(2774243251/5000000000 : ℝ)*X 2 1+(79397081/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40759686365557354160811/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1486701/5000000000000 : ℝ)*(base1) + (503221571/100000000000000 : ℝ)*(base19) + (249593259/50000000000000 : ℝ)*(base23) + (356513/625000000000 : ℝ)*(upper3) + (14778713/25000000000000 : ℝ)*(upper5) + (611146674667359/100000000000000 : ℝ)*(major0) + (611146674667359/100000000000000 : ℝ)*(major1) + (611146674667359/100000000000000 : ℝ)*(major2) + (822945475383323/100000000000000 : ℝ)*(sp0) + (4114732664811/500000000000 : ℝ)*(sp1) + (411473268498627/50000000000000 : ℝ)*(sp2) + (24959092167019/6250000000000 : ℝ)*(sp3) + (397633617/25000000000000 : ℝ)*(sp4) + (740811809/100000000000000 : ℝ)*(sp7) + (399346245218133/100000000000000 : ℝ)*(f.failure) + (822947036183771/100000000000000 : ℝ)*(f.sum) + (4493147726937/20000000000000000000000000000 : ℝ)*base65 + (115181871233063/40000000000000000000000000000 : ℝ)*base68 + (21533033513063/40000000000000000000000000000 : ℝ)*base70 + (31634566366937/40000000000000000000000000000 : ℝ)*base71 + (72711449953063/20000000000000000000000000000 : ℝ)*base74 + (20324871593063/40000000000000000000000000000 : ℝ)*base76 + (161511179953063/40000000000000000000000000000 : ℝ)*base78 + (269542651033063/40000000000000000000000000000 : ℝ)*base80 + (42852724086937/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2411307/1000000000000000000000 : ℝ)*base89 + (2411307/1000000000000000000000 : ℝ)*base91 + (2411307/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133480323332121746083887/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50571669/10000000000000 : ℝ)*(base1) + (1209000411/100000000000000 : ℝ)*(base19) + (279606579/20000000000000 : ℝ)*(base23) + (212296093/100000000000000 : ℝ)*(upper3) + (645019428542003/100000000000000 : ℝ)*(major0) + (645019428542003/100000000000000 : ℝ)*(major1) + (645019428542003/100000000000000 : ℝ)*(major2) + (427093053/25000000000000 : ℝ)*(sp1) + (12029211/1000000000000 : ℝ)*(sp2) + (211894847/50000000000000 : ℝ)*(sp3) + (217139790629423/25000000000000 : ℝ)*(sp4) + (43427786971419/5000000000000 : ℝ)*(sp5) + (868556055847007/100000000000000 : ℝ)*(sp6) + (42147904830941/10000000000000 : ℝ)*(sp7) + (210739988907897/50000000000000 : ℝ)*(f.failure) + (434279328400501/50000000000000 : ℝ)*(f.sum) + (18296724065371/20000000000000000000000000000 : ℝ)*base66 + (198535993334629/40000000000000000000000000000 : ℝ)*base67 + (153873018185371/40000000000000000000000000000 : ℝ)*base70 + (26332698265371/40000000000000000000000000000 : ℝ)*base72 + (19840869174629/20000000000000000000000000000 : ℝ)*base73 + (319415855625371/40000000000000000000000000000 : ℝ)*base76 + (46841352654629/40000000000000000000000000000 : ℝ)*base77 + (244454476934629/40000000000000000000000000000 : ℝ)*base79 + (106305940565371/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1253063/500000000000000000000 : ℝ)*base89 + (1253063/500000000000000000000 : ℝ)*base91 + (1253063/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1299_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1699/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1299_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1299_s1_0 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025870819/10000000000 : ℝ)*x 0 + (566197811/1000000000 : ℝ)*x 1 + (1257990629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025870819/10000000000 : ℝ)^4259 ≤ (2444320253999/20000000000000 : ℝ)^3235 := by
    have hnat : (2025870819 : ℕ)^4259*20000000000000^3235 ≤ 2444320253999^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025870819 10000000000 2444320253999 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566197811/1000000000 : ℝ)^4259 ≤ (47290429947453/100000000000000 : ℝ)^3235 := by
    have hnat : (566197811 : ℕ)^4259*100000000000000^3235 ≤ 47290429947453^3235*1000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566197811 1000000000 47290429947453 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1257990629/2500000000 : ℝ)^4259 ≤ (40487968762023/100000000000000 : ℝ)^3235 := by
    have hnat : (1257990629 : ℕ)^4259*100000000000000^3235 ≤ 40487968762023^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257990629 2500000000 40487968762023 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025870819/10000000000 : ℝ), (566197811/1000000000 : ℝ), (1257990629/2500000000 : ℝ)] ![(2444320253999/20000000000000 : ℝ), (47290429947453/100000000000000 : ℝ), (40487968762023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025870819/10000000000 : ℝ)|^4259 ≤ (2444320253999/20000000000000 : ℝ)^3235
        have hw : |(-2025870819/10000000000 : ℝ)|=(2025870819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566197811/1000000000 : ℝ)|^4259 ≤ (47290429947453/100000000000000 : ℝ)^3235
        have hw : |(566197811/1000000000 : ℝ)|=(566197811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1257990629/2500000000 : ℝ)|^4259 ≤ (40487968762023/100000000000000 : ℝ)^3235
        have hw : |(1257990629/2500000000 : ℝ)|=(1257990629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s1_1 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082048673/2000000000 : ℝ)*x 0 + (-1181667557/5000000000 : ℝ)*x 1 + (628995337/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082048673/2000000000 : ℝ)^4259 ≤ (44542010539001/100000000000000 : ℝ)^3235 := by
    have hnat : (1082048673 : ℕ)^4259*100000000000000^3235 ≤ 44542010539001^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082048673 2000000000 44542010539001 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1181667557/5000000000 : ℝ)^4259 ≤ (14970018767299/100000000000000 : ℝ)^3235 := by
    have hnat : (1181667557 : ℕ)^4259*100000000000000^3235 ≤ 14970018767299^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181667557 5000000000 14970018767299 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628995337/1250000000 : ℝ)^4259 ≤ (5060996333597/12500000000000 : ℝ)^3235 := by
    have hnat : (628995337 : ℕ)^4259*12500000000000^3235 ≤ 5060996333597^3235*1250000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628995337 1250000000 5060996333597 12500000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082048673/2000000000 : ℝ), (-1181667557/5000000000 : ℝ), (628995337/1250000000 : ℝ)] ![(44542010539001/100000000000000 : ℝ), (14970018767299/100000000000000 : ℝ), (5060996333597/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082048673/2000000000 : ℝ)|^4259 ≤ (44542010539001/100000000000000 : ℝ)^3235
        have hw : |(1082048673/2000000000 : ℝ)|=(1082048673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1181667557/5000000000 : ℝ)|^4259 ≤ (14970018767299/100000000000000 : ℝ)^3235
        have hw : |(-1181667557/5000000000 : ℝ)|=(1181667557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628995337/1250000000 : ℝ)|^4259 ≤ (5060996333597/12500000000000 : ℝ)^3235
        have hw : |(628995337/1250000000 : ℝ)|=(628995337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s1_2 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2705121747/5000000000 : ℝ)*x 0 + (5031962423/10000000000 : ℝ)*x 1 + (-1181667647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705121747/5000000000 : ℝ)^4259 ≤ (22271005968611/50000000000000 : ℝ)^3235 := by
    have hnat : (2705121747 : ℕ)^4259*50000000000000^3235 ≤ 22271005968611^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705121747 5000000000 22271005968611 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5031962423/10000000000 : ℝ)^4259 ≤ (40487967776867/100000000000000 : ℝ)^3235 := by
    have hnat : (5031962423 : ℕ)^4259*100000000000000^3235 ≤ 40487967776867^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031962423 10000000000 40487967776867 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1181667647/5000000000 : ℝ)^4259 ≤ (1871252533547/12500000000000 : ℝ)^3235 := by
    have hnat : (1181667647 : ℕ)^4259*12500000000000^3235 ≤ 1871252533547^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181667647 5000000000 1871252533547 12500000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705121747/5000000000 : ℝ), (5031962423/10000000000 : ℝ), (-1181667647/5000000000 : ℝ)] ![(22271005968611/50000000000000 : ℝ), (40487967776867/100000000000000 : ℝ), (1871252533547/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705121747/5000000000 : ℝ)|^4259 ≤ (22271005968611/50000000000000 : ℝ)^3235
        have hw : |(2705121747/5000000000 : ℝ)|=(2705121747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5031962423/10000000000 : ℝ)|^4259 ≤ (40487967776867/100000000000000 : ℝ)^3235
        have hw : |(5031962423/10000000000 : ℝ)|=(5031962423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1181667647/5000000000 : ℝ)|^4259 ≤ (1871252533547/12500000000000 : ℝ)^3235
        have hw : |(-1181667647/5000000000 : ℝ)|=(1181667647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s1_3 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214995663/500000000 : ℝ)*x 0 + (1848521301/5000000000 : ℝ)*x 1 + (2497668929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214995663/500000000 : ℝ)^4259 ≤ (4114772431827/12500000000000 : ℝ)^3235 := by
    have hnat : (214995663 : ℕ)^4259*12500000000000^3235 ≤ 4114772431827^3235*500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214995663 500000000 4114772431827 12500000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1848521301/5000000000 : ℝ)^4259 ≤ (5396274354177/20000000000000 : ℝ)^3235 := by
    have hnat : (1848521301 : ℕ)^4259*20000000000000^3235 ≤ 5396274354177^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848521301 5000000000 5396274354177 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2497668929/5000000000 : ℝ)^4259 ≤ (20050224381659/50000000000000 : ℝ)^3235 := by
    have hnat : (2497668929 : ℕ)^4259*50000000000000^3235 ≤ 20050224381659^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497668929 5000000000 20050224381659 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214995663/500000000 : ℝ), (1848521301/5000000000 : ℝ), (2497668929/5000000000 : ℝ)] ![(4114772431827/12500000000000 : ℝ), (5396274354177/20000000000000 : ℝ), (20050224381659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214995663/500000000 : ℝ)|^4259 ≤ (4114772431827/12500000000000 : ℝ)^3235
        have hw : |(214995663/500000000 : ℝ)|=(214995663/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1848521301/5000000000 : ℝ)|^4259 ≤ (5396274354177/20000000000000 : ℝ)^3235
        have hw : |(1848521301/5000000000 : ℝ)|=(1848521301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2497668929/5000000000 : ℝ)|^4259 ≤ (20050224381659/50000000000000 : ℝ)^3235
        have hw : |(2497668929/5000000000 : ℝ)|=(2497668929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s1_4 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-101324641/500000000 : ℝ)*x 0 + (630016613/1250000000 : ℝ)*x 1 + (5653653931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101324641/500000000 : ℝ)^4259 ≤ (1222654166759/10000000000000 : ℝ)^3235 := by
    have hnat : (101324641 : ℕ)^4259*10000000000000^3235 ≤ 1222654166759^3235*500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101324641 500000000 1222654166759 10000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (630016613/1250000000 : ℝ)^4259 ≤ (20287270254141/50000000000000 : ℝ)^3235 := by
    have hnat : (630016613 : ℕ)^4259*50000000000000^3235 ≤ 20287270254141^3235*1250000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630016613 1250000000 20287270254141 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5653653931/10000000000 : ℝ)^4259 ≤ (4719891780089/10000000000000 : ℝ)^3235 := by
    have hnat : (5653653931 : ℕ)^4259*10000000000000^3235 ≤ 4719891780089^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5653653931 10000000000 4719891780089 10000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101324641/500000000 : ℝ), (630016613/1250000000 : ℝ), (5653653931/10000000000 : ℝ)] ![(1222654166759/10000000000000 : ℝ), (20287270254141/50000000000000 : ℝ), (4719891780089/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101324641/500000000 : ℝ)|^4259 ≤ (1222654166759/10000000000000 : ℝ)^3235
        have hw : |(-101324641/500000000 : ℝ)|=(101324641/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(630016613/1250000000 : ℝ)|^4259 ≤ (20287270254141/50000000000000 : ℝ)^3235
        have hw : |(630016613/1250000000 : ℝ)|=(630016613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5653653931/10000000000 : ℝ)|^4259 ≤ (4719891780089/10000000000000 : ℝ)^3235
        have hw : |(5653653931/10000000000 : ℝ)|=(5653653931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s1_5 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1311841869/2500000000 : ℝ)*x 0 + (-348328647/2000000000 : ℝ)*x 1 + (353353417/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311841869/2500000000 : ℝ)^4259 ≤ (42785080386003/100000000000000 : ℝ)^3235 := by
    have hnat : (1311841869 : ℕ)^4259*100000000000000^3235 ≤ 42785080386003^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311841869 2500000000 42785080386003 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (348328647/2000000000 : ℝ)^4259 ≤ (2503998412111/25000000000000 : ℝ)^3235 := by
    have hnat : (348328647 : ℕ)^4259*25000000000000^3235 ≤ 2503998412111^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348328647 2000000000 2503998412111 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353353417/625000000 : ℝ)^4259 ≤ (47198925945201/100000000000000 : ℝ)^3235 := by
    have hnat : (353353417 : ℕ)^4259*100000000000000^3235 ≤ 47198925945201^3235*625000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353353417 625000000 47198925945201 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311841869/2500000000 : ℝ), (-348328647/2000000000 : ℝ), (353353417/625000000 : ℝ)] ![(42785080386003/100000000000000 : ℝ), (2503998412111/25000000000000 : ℝ), (47198925945201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311841869/2500000000 : ℝ)|^4259 ≤ (42785080386003/100000000000000 : ℝ)^3235
        have hw : |(1311841869/2500000000 : ℝ)|=(1311841869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-348328647/2000000000 : ℝ)|^4259 ≤ (2503998412111/25000000000000 : ℝ)^3235
        have hw : |(-348328647/2000000000 : ℝ)|=(348328647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(353353417/625000000 : ℝ)|^4259 ≤ (47198925945201/100000000000000 : ℝ)^3235
        have hw : |(353353417/625000000 : ℝ)|=(353353417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s1_6 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5247367391/10000000000 : ℝ)*x 0 + (5653654259/10000000000 : ℝ)*x 1 + (-348328791/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247367391/10000000000 : ℝ)^4259 ≤ (8557015894713/20000000000000 : ℝ)^3235 := by
    have hnat : (5247367391 : ℕ)^4259*20000000000000^3235 ≤ 8557015894713^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247367391 10000000000 8557015894713 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5653654259/10000000000 : ℝ)^4259 ≤ (47198921405929/100000000000000 : ℝ)^3235 := by
    have hnat : (5653654259 : ℕ)^4259*100000000000000^3235 ≤ 47198921405929^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5653654259 10000000000 47198921405929 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (348328791/2000000000 : ℝ)^4259 ≤ (1251999887469/12500000000000 : ℝ)^3235 := by
    have hnat : (348328791 : ℕ)^4259*12500000000000^3235 ≤ 1251999887469^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348328791 2000000000 1251999887469 12500000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247367391/10000000000 : ℝ), (5653654259/10000000000 : ℝ), (-348328791/2000000000 : ℝ)] ![(8557015894713/20000000000000 : ℝ), (47198921405929/100000000000000 : ℝ), (1251999887469/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247367391/10000000000 : ℝ)|^4259 ≤ (8557015894713/20000000000000 : ℝ)^3235
        have hw : |(5247367391/10000000000 : ℝ)|=(5247367391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5653654259/10000000000 : ℝ)|^4259 ≤ (47198921405929/100000000000000 : ℝ)^3235
        have hw : |(5653654259/10000000000 : ℝ)|=(5653654259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-348328791/2000000000 : ℝ)|^4259 ≤ (1251999887469/12500000000000 : ℝ)^3235
        have hw : |(-348328791/2000000000 : ℝ)|=(348328791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s1_7 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150597103/5000000000 : ℝ)*x 0 + (4978501457/10000000000 : ℝ)*x 1 + (3714195663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150597103/5000000000 : ℝ)^4259 ≤ (32931090480891/100000000000000 : ℝ)^3235 := by
    have hnat : (2150597103 : ℕ)^4259*100000000000000^3235 ≤ 32931090480891^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150597103 5000000000 32931090480891 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4978501457/10000000000 : ℝ)^4259 ≤ (7984521291973/20000000000000 : ℝ)^3235 := by
    have hnat : (4978501457 : ℕ)^4259*20000000000000^3235 ≤ 7984521291973^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4978501457 10000000000 7984521291973 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3714195663/10000000000 : ℝ)^4259 ≤ (27146303045067/100000000000000 : ℝ)^3235 := by
    have hnat : (3714195663 : ℕ)^4259*100000000000000^3235 ≤ 27146303045067^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714195663 10000000000 27146303045067 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150597103/5000000000 : ℝ), (4978501457/10000000000 : ℝ), (3714195663/10000000000 : ℝ)] ![(32931090480891/100000000000000 : ℝ), (7984521291973/20000000000000 : ℝ), (27146303045067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150597103/5000000000 : ℝ)|^4259 ≤ (32931090480891/100000000000000 : ℝ)^3235
        have hw : |(2150597103/5000000000 : ℝ)|=(2150597103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4978501457/10000000000 : ℝ)|^4259 ≤ (7984521291973/20000000000000 : ℝ)^3235
        have hw : |(4978501457/10000000000 : ℝ)|=(4978501457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3714195663/10000000000 : ℝ)|^4259 ≤ (27146303045067/100000000000000 : ℝ)^3235
        have hw : |(3714195663/10000000000 : ℝ)|=(3714195663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1299_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1699/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3239/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9897/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1699/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1699/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1699/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1699/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1699/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1699/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1087/100000 : ℝ) ^ (2129/512 : ℝ) ≤ (341360729357/50000000000000000000 : ℝ) := by
    have hpowers : (1087/100000 : ℝ)^2129 ≤ (341360729357/50000000000000000000 : ℝ)^512 := by
      have hnat : (1087 : ℕ)^2129*50000000000000000000^512 ≤ 341360729357^512*100000^2129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1087 100000 341360729357 50000000000000000000 2129 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1087/100000 : ℝ)) (X := (341360729357/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1699/6250 : ℝ) ^ (2129/512 : ℝ) ≤ (444385676364112533/100000000000000000000 : ℝ) := by
    have hpowers : (1699/6250 : ℝ)^2129 ≤ (444385676364112533/100000000000000000000 : ℝ)^512 := by
      have hnat : (1699 : ℕ)^2129*100000000000000000000^512 ≤ 444385676364112533^512*6250^2129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1699 6250 444385676364112533 100000000000000000000 2129 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1699/6250 : ℝ)) (X := (444385676364112533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000341360729357/25000000000000000000 : ℝ) ≤ (10000000032837331/10000000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (25000000341360729357/25000000000000000000 : ℝ)^512 ≤ (10000000032837331/10000000000000000 : ℝ)^2129 := by
      have hnat : (25000000341360729357 : ℕ)^512*10000000000000000^2129 ≤ 10000000032837331^2129*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000341360729357 25000000000000000000 10000000032837331 10000000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000032837331/10000000000000000 : ℝ)) (X := (25000000341360729357/25000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100444386359085571247/100000000000000000000 : ℝ) ≤ (5005334496122637/5000000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (100444386359085571247/100000000000000000000 : ℝ)^512 ≤ (5005334496122637/5000000000000000 : ℝ)^2129 := by
      have hnat : (100444386359085571247 : ℕ)^512*5000000000000000^2129 ≤ 5005334496122637^2129*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100444386359085571247 100000000000000000000 5005334496122637 5000000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005334496122637/5000000000000000 : ℝ)) (X := (100444386359085571247/100000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50444385676364112533/50000000000000000000 : ℝ) ≤ (10021337951653217/10000000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (50444385676364112533/50000000000000000000 : ℝ)^512 ≤ (10021337951653217/10000000000000000 : ℝ)^2129 := by
      have hnat : (50444385676364112533 : ℕ)^512*10000000000000000^2129 ≤ 10021337951653217^2129*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50444385676364112533 50000000000000000000 10021337951653217 10000000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10021337951653217/10000000000000000 : ℝ)) (X := (50444385676364112533/50000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(341360729357/50000000000000000000 : ℝ) ≤ ((10437872261568118361/10438800000000000000 : ℝ)+2*(10668959407943/2609700000000000 : ℝ)*(1087/100000 : ℝ))^(2129/512 : ℝ) := by
    rw [show (10437872261568118361/10438800000000000000 : ℝ)+2*(10668959407943/2609700000000000 : ℝ)*(1087/100000 : ℝ)=(10000000032837331/10000000000000000 : ℝ) by norm_num, show 1+2*(341360729357/50000000000000000000 : ℝ)=(25000000341360729357/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(444385676364112533/100000000000000000000 : ℝ)+(341360729357/50000000000000000000 : ℝ) ≤ ((10437872261568118361/10438800000000000000 : ℝ)+(10668959407943/2609700000000000 : ℝ)*((1699/6250 : ℝ)+(1087/100000 : ℝ)))^(2129/512 : ℝ) := by
    rw [show (10437872261568118361/10438800000000000000 : ℝ)+(10668959407943/2609700000000000 : ℝ)*((1699/6250 : ℝ)+(1087/100000 : ℝ))=(5005334496122637/5000000000000000 : ℝ) by norm_num, show 1+(444385676364112533/100000000000000000000 : ℝ)+(341360729357/50000000000000000000 : ℝ)=(100444386359085571247/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(444385676364112533/100000000000000000000 : ℝ) ≤ ((10437872261568118361/10438800000000000000 : ℝ)+2*(10668959407943/2609700000000000 : ℝ)*(1699/6250 : ℝ))^(2129/512 : ℝ) := by
    rw [show (10437872261568118361/10438800000000000000 : ℝ)+2*(10668959407943/2609700000000000 : ℝ)*(1699/6250 : ℝ)=(10021337951653217/10000000000000000 : ℝ) by norm_num, show 1+2*(444385676364112533/100000000000000000000 : ℝ)=(50444385676364112533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10437872261568118361/10438800000000000000 : ℝ)*(X 1 0+X 2 0)+(10668959407943/2609700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (1087/100000 : ℝ)) (hi := (1699/6250 : ℝ)) (c := (10437872261568118361/10438800000000000000 : ℝ)) (alpha := (10668959407943/2609700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10437872261568118361/10438800000000000000 : ℝ)*(X 0 1+X 2 1)+(10668959407943/2609700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (1087/100000 : ℝ)) (hi := (1699/6250 : ℝ)) (c := (10437872261568118361/10438800000000000000 : ℝ)) (alpha := (10668959407943/2609700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10437872261568118361/10438800000000000000 : ℝ)*(X 0 2+X 1 2)+(10668959407943/2609700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (1087/100000 : ℝ)) (hi := (1699/6250 : ℝ)) (c := (10437872261568118361/10438800000000000000 : ℝ)) (alpha := (10668959407943/2609700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2025870819/10000000000 : ℝ)*X 0 0+(566197811/1000000000 : ℝ)*X 0 1+(1257990629/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1082048673/2000000000 : ℝ)*X 1 0+(-1181667557/5000000000 : ℝ)*X 1 1+(628995337/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2705121747/5000000000 : ℝ)*X 2 0+(5031962423/10000000000 : ℝ)*X 2 1+(-1181667647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((214995663/500000000 : ℝ)*X 0 0+(1848521301/5000000000 : ℝ)*X 0 1+(2497668929/5000000000 : ℝ)*X 0 2+(214995663/500000000 : ℝ)*X 1 0+(1848521301/5000000000 : ℝ)*X 1 1+(2497668929/5000000000 : ℝ)*X 1 2+(214995663/500000000 : ℝ)*X 2 0+(1848521301/5000000000 : ℝ)*X 2 1+(2497668929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-101324641/500000000 : ℝ)*X 0 0+(630016613/1250000000 : ℝ)*X 0 1+(5653653931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1311841869/2500000000 : ℝ)*X 1 0+(-348328647/2000000000 : ℝ)*X 1 1+(353353417/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5247367391/10000000000 : ℝ)*X 2 0+(5653654259/10000000000 : ℝ)*X 2 1+(-348328791/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2150597103/5000000000 : ℝ)*X 0 0+(4978501457/10000000000 : ℝ)*X 0 1+(3714195663/10000000000 : ℝ)*X 0 2+(2150597103/5000000000 : ℝ)*X 1 0+(4978501457/10000000000 : ℝ)*X 1 1+(3714195663/10000000000 : ℝ)*X 1 2+(2150597103/5000000000 : ℝ)*X 2 0+(4978501457/10000000000 : ℝ)*X 2 1+(3714195663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1031109859101279178025996643/173980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6776537/12500000000000 : ℝ)*(base1) + (1071890627/100000000000000 : ℝ)*(base19) + (554868519/50000000000000 : ℝ)*(base23) + (160571837/100000000000000 : ℝ)*(upper3) + (99930111/100000000000000 : ℝ)*(upper5) + (1178760762238679/100000000000000 : ℝ)*(major0) + (1178760762238679/100000000000000 : ℝ)*(major1) + (1178760762238679/100000000000000 : ℝ)*(major2) + (198408589798261/12500000000000 : ℝ)*(sp0) + (317454719177557/20000000000000 : ℝ)*(sp1) + (793636779020687/50000000000000 : ℝ)*(sp2) + (385121756520439/50000000000000 : ℝ)*(sp3) + (300180231/5000000000000 : ℝ)*(sp4) + (3091892433/100000000000000 : ℝ)*(sp7) + (770246659145607/100000000000000 : ℝ)*(f.failure) + (396818666944603/25000000000000 : ℝ)*(f.sum) + (524642900509387/130485000000000000000000000000 : ℝ)*base65 + (4520065735597113119/1043880000000000000000000000000000 : ℝ)*base67 + (5830232807273193119/1043880000000000000000000000000000 : ℝ)*base69 + (3845226120421833119/1043880000000000000000000000000000 : ℝ)*base71 + (184579404499001/65242500000000000000000000000 : ℝ)*base73 + (7649267058633033119/1043880000000000000000000000000000 : ℝ)*base75 + (9079737086165553119/1043880000000000000000000000000000 : ℝ)*base77 + (3690871096434153119/1043880000000000000000000000000000 : ℝ)*base79 + (172669614472751/65242500000000000000000000000 : ℝ)*base81 + (6211847/1000000000000000000000 : ℝ)*base90 + (6211847/1000000000000000000000 : ℝ)*base92 + (6211847/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (849053489155115158422655551/173980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (832480599/100000000000000 : ℝ)*(base19) + (422572653/50000000000000 : ℝ)*(base23) + (19441753/50000000000000 : ℝ)*(upper2) + (165819489/100000000000000 : ℝ)*(upper3) + (25252209/25000000000000 : ℝ)*(upper5) + (1210441501371209/100000000000000 : ℝ)*(major0) + (1210441501371209/100000000000000 : ℝ)*(major1) + (1210441501371209/100000000000000 : ℝ)*(major2) + (1273876403/25000000000000 : ℝ)*(sp1) + (79336463/2000000000000 : ℝ)*(sp2) + (1629934793282339/100000000000000 : ℝ)*(sp4) + (1629928865296127/100000000000000 : ℝ)*(sp5) + (1629929981313883/100000000000000 : ℝ)*(sp6) + (98868505848431/12500000000000 : ℝ)*(sp7) + (98868505848431/12500000000000 : ℝ)*(f.failure) + (1629934793282339/100000000000000 : ℝ)*(f.sum) + (824511778223707/130485000000000000000000000000 : ℝ)*base65 + (2570400737182943551/1043880000000000000000000000000000 : ℝ)*base68 + (6243111046625976449/1043880000000000000000000000000000 : ℝ)*base69 + (6367652729416416449/1043880000000000000000000000000000 : ℝ)*base71 + (2851824287837/2038828125000000000000000000 : ℝ)*base74 + (10794969947080416449/1043880000000000000000000000000000 : ℝ)*base75 + (8920935690954936449/1043880000000000000000000000000000 : ℝ)*base77 + (2120788772064023551/1043880000000000000000000000000000 : ℝ)*base80 + (10785359466671/4077656250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (572351/125000000000000000000 : ℝ)*base90 + (572351/125000000000000000000 : ℝ)*base92 + (572351/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1299_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1699/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3239/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9897/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1299_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1299_s2_0 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2069910633/10000000000 : ℝ)*x 0 + (686514857/1250000000 : ℝ)*x 1 + (1293420189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069910633/10000000000 : ℝ)^4259 ≤ (6286289490579/50000000000000 : ℝ)^3235 := by
    have hnat : (2069910633 : ℕ)^4259*50000000000000^3235 ≤ 6286289490579^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069910633 10000000000 6286289490579 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686514857/1250000000 : ℝ)^4259 ≤ (2271578572351/5000000000000 : ℝ)^3235 := by
    have hnat : (686514857 : ℕ)^4259*5000000000000^3235 ≤ 2271578572351^3235*1250000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686514857 1250000000 2271578572351 5000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293420189/2500000000 : ℝ)^4259 ≤ (41995849554191/100000000000000 : ℝ)^3235 := by
    have hnat : (1293420189 : ℕ)^4259*100000000000000^3235 ≤ 41995849554191^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293420189 2500000000 41995849554191 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2069910633/10000000000 : ℝ), (686514857/1250000000 : ℝ), (1293420189/2500000000 : ℝ)] ![(6286289490579/50000000000000 : ℝ), (2271578572351/5000000000000 : ℝ), (41995849554191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2069910633/10000000000 : ℝ)|^4259 ≤ (6286289490579/50000000000000 : ℝ)^3235
        have hw : |(-2069910633/10000000000 : ℝ)|=(2069910633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686514857/1250000000 : ℝ)|^4259 ≤ (2271578572351/5000000000000 : ℝ)^3235
        have hw : |(686514857/1250000000 : ℝ)|=(686514857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293420189/2500000000 : ℝ)|^4259 ≤ (41995849554191/100000000000000 : ℝ)^3235
        have hw : |(1293420189/2500000000 : ℝ)|=(1293420189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s2_1 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369061917/10000000000 : ℝ)*x 0 + (-1117430347/5000000000 : ℝ)*x 1 + (206947227/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369061917/10000000000 : ℝ)^4259 ≤ (5512023302487/12500000000000 : ℝ)^3235 := by
    have hnat : (5369061917 : ℕ)^4259*12500000000000^3235 ≤ 5512023302487^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369061917 10000000000 5512023302487 12500000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117430347/5000000000 : ℝ)^4259 ≤ (13907964872737/100000000000000 : ℝ)^3235 := by
    have hnat : (1117430347 : ℕ)^4259*100000000000000^3235 ≤ 13907964872737^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117430347 5000000000 13907964872737 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206947227/400000000 : ℝ)^4259 ≤ (1679833947543/4000000000000 : ℝ)^3235 := by
    have hnat : (206947227 : ℕ)^4259*4000000000000^3235 ≤ 1679833947543^3235*400000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206947227 400000000 1679833947543 4000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369061917/10000000000 : ℝ), (-1117430347/5000000000 : ℝ), (206947227/400000000 : ℝ)] ![(5512023302487/12500000000000 : ℝ), (13907964872737/100000000000000 : ℝ), (1679833947543/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369061917/10000000000 : ℝ)|^4259 ≤ (5512023302487/12500000000000 : ℝ)^3235
        have hw : |(5369061917/10000000000 : ℝ)|=(5369061917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1117430347/5000000000 : ℝ)|^4259 ≤ (13907964872737/100000000000000 : ℝ)^3235
        have hw : |(-1117430347/5000000000 : ℝ)|=(1117430347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206947227/400000000 : ℝ)|^4259 ≤ (1679833947543/4000000000000 : ℝ)^3235
        have hw : |(206947227/400000000 : ℝ)|=(206947227/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s2_2 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369061727/10000000000 : ℝ)*x 0 + (206947231/400000000 : ℝ)*x 1 + (-446972163/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369061727/10000000000 : ℝ)^4259 ≤ (22048092182737/50000000000000 : ℝ)^3235 := by
    have hnat : (5369061727 : ℕ)^4259*50000000000000^3235 ≤ 22048092182737^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369061727 10000000000 22048092182737 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206947231/400000000 : ℝ)^4259 ≤ (41995849757237/100000000000000 : ℝ)^3235 := by
    have hnat : (206947231 : ℕ)^4259*100000000000000^3235 ≤ 41995849757237^3235*400000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206947231 400000000 41995849757237 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446972163/2000000000 : ℝ)^4259 ≤ (6953982932049/50000000000000 : ℝ)^3235 := by
    have hnat : (446972163 : ℕ)^4259*50000000000000^3235 ≤ 6953982932049^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446972163 2000000000 6953982932049 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369061727/10000000000 : ℝ), (206947231/400000000 : ℝ), (-446972163/2000000000 : ℝ)] ![(22048092182737/50000000000000 : ℝ), (41995849757237/100000000000000 : ℝ), (6953982932049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369061727/10000000000 : ℝ)|^4259 ≤ (22048092182737/50000000000000 : ℝ)^3235
        have hw : |(5369061727/10000000000 : ℝ)|=(5369061727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206947231/400000000 : ℝ)|^4259 ≤ (41995849757237/100000000000000 : ℝ)^3235
        have hw : |(206947231/400000000 : ℝ)|=(206947231/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446972163/2000000000 : ℝ)|^4259 ≤ (6953982932049/50000000000000 : ℝ)^3235
        have hw : |(-446972163/2000000000 : ℝ)|=(446972163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s2_3 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165275917/5000000000 : ℝ)*x 0 + (2007123059/5000000000 : ℝ)*x 1 + (467047073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165275917/5000000000 : ℝ)^4259 ≤ (16224281079/48828125000 : ℝ)^3235 := by
    have hnat : (2165275917 : ℕ)^4259*48828125000^3235 ≤ 16224281079^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165275917 5000000000 16224281079 48828125000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007123059/5000000000 : ℝ)^4259 ≤ (6013947688283/20000000000000 : ℝ)^3235 := by
    have hnat : (2007123059 : ℕ)^4259*20000000000000^3235 ≤ 6013947688283^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007123059 5000000000 6013947688283 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467047073/1000000000 : ℝ)^4259 ≤ (7340586779583/20000000000000 : ℝ)^3235 := by
    have hnat : (467047073 : ℕ)^4259*20000000000000^3235 ≤ 7340586779583^3235*1000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467047073 1000000000 7340586779583 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165275917/5000000000 : ℝ), (2007123059/5000000000 : ℝ), (467047073/1000000000 : ℝ)] ![(16224281079/48828125000 : ℝ), (6013947688283/20000000000000 : ℝ), (7340586779583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165275917/5000000000 : ℝ)|^4259 ≤ (16224281079/48828125000 : ℝ)^3235
        have hw : |(2165275917/5000000000 : ℝ)|=(2165275917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2007123059/5000000000 : ℝ)|^4259 ≤ (6013947688283/20000000000000 : ℝ)^3235
        have hw : |(2007123059/5000000000 : ℝ)|=(2007123059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467047073/1000000000 : ℝ)|^4259 ≤ (7340586779583/20000000000000 : ℝ)^3235
        have hw : |(467047073/1000000000 : ℝ)|=(467047073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s2_4 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-129374393/625000000 : ℝ)*x 0 + (2587888679/5000000000 : ℝ)*x 1 + (1372500693/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129374393/625000000 : ℝ)^4259 ≤ (3143303988831/25000000000000 : ℝ)^3235 := by
    have hnat : (129374393 : ℕ)^4259*25000000000000^3235 ≤ 3143303988831^3235*625000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129374393 625000000 3143303988831 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587888679/5000000000 : ℝ)^4259 ≤ (21009128283083/50000000000000 : ℝ)^3235 := by
    have hnat : (2587888679 : ℕ)^4259*50000000000000^3235 ≤ 21009128283083^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587888679 5000000000 21009128283083 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372500693/2500000000 : ℝ)^4259 ≤ (9081705492193/20000000000000 : ℝ)^3235 := by
    have hnat : (1372500693 : ℕ)^4259*20000000000000^3235 ≤ 9081705492193^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372500693 2500000000 9081705492193 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129374393/625000000 : ℝ), (2587888679/5000000000 : ℝ), (1372500693/2500000000 : ℝ)] ![(3143303988831/25000000000000 : ℝ), (21009128283083/50000000000000 : ℝ), (9081705492193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129374393/625000000 : ℝ)|^4259 ≤ (3143303988831/25000000000000 : ℝ)^3235
        have hw : |(-129374393/625000000 : ℝ)|=(129374393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587888679/5000000000 : ℝ)|^4259 ≤ (21009128283083/50000000000000 : ℝ)^3235
        have hw : |(2587888679/5000000000 : ℝ)|=(2587888679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372500693/2500000000 : ℝ)|^4259 ≤ (9081705492193/20000000000000 : ℝ)^3235
        have hw : |(1372500693/2500000000 : ℝ)|=(1372500693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s2_5 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643689753/5000000000 : ℝ)*x 0 + (-959269017/5000000000 : ℝ)*x 1 + (2745001447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643689753/5000000000 : ℝ)^4259 ≤ (43215109351637/100000000000000 : ℝ)^3235 := by
    have hnat : (2643689753 : ℕ)^4259*100000000000000^3235 ≤ 43215109351637^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643689753 5000000000 43215109351637 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959269017/5000000000 : ℝ)^4259 ≤ (5688180924681/50000000000000 : ℝ)^3235 := by
    have hnat : (959269017 : ℕ)^4259*50000000000000^3235 ≤ 5688180924681^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959269017 5000000000 5688180924681 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745001447/5000000000 : ℝ)^4259 ≤ (9081705757891/20000000000000 : ℝ)^3235 := by
    have hnat : (2745001447 : ℕ)^4259*20000000000000^3235 ≤ 9081705757891^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745001447 5000000000 9081705757891 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643689753/5000000000 : ℝ), (-959269017/5000000000 : ℝ), (2745001447/5000000000 : ℝ)] ![(43215109351637/100000000000000 : ℝ), (5688180924681/50000000000000 : ℝ), (9081705757891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643689753/5000000000 : ℝ)|^4259 ≤ (43215109351637/100000000000000 : ℝ)^3235
        have hw : |(2643689753/5000000000 : ℝ)|=(2643689753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-959269017/5000000000 : ℝ)|^4259 ≤ (5688180924681/50000000000000 : ℝ)^3235
        have hw : |(-959269017/5000000000 : ℝ)|=(959269017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745001447/5000000000 : ℝ)|^4259 ≤ (9081705757891/20000000000000 : ℝ)^3235
        have hw : |(2745001447/5000000000 : ℝ)|=(2745001447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s2_6 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660922457/1250000000 : ℝ)*x 0 + (5490002779/10000000000 : ℝ)*x 1 + (-1918537987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660922457/1250000000 : ℝ)^4259 ≤ (21607555482849/50000000000000 : ℝ)^3235 := by
    have hnat : (660922457 : ℕ)^4259*50000000000000^3235 ≤ 21607555482849^3235*1250000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660922457 1250000000 21607555482849 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490002779/10000000000 : ℝ)^4259 ≤ (4540852753719/10000000000000 : ℝ)^3235 := by
    have hnat : (5490002779 : ℕ)^4259*10000000000000^3235 ≤ 4540852753719^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490002779 10000000000 4540852753719 10000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918537987/10000000000 : ℝ)^4259 ≤ (711022592653/6250000000000 : ℝ)^3235 := by
    have hnat : (1918537987 : ℕ)^4259*6250000000000^3235 ≤ 711022592653^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918537987 10000000000 711022592653 6250000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660922457/1250000000 : ℝ), (5490002779/10000000000 : ℝ), (-1918537987/10000000000 : ℝ)] ![(21607555482849/50000000000000 : ℝ), (4540852753719/10000000000000 : ℝ), (711022592653/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660922457/1250000000 : ℝ)|^4259 ≤ (21607555482849/50000000000000 : ℝ)^3235
        have hw : |(660922457/1250000000 : ℝ)|=(660922457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490002779/10000000000 : ℝ)|^4259 ≤ (4540852753719/10000000000000 : ℝ)^3235
        have hw : |(5490002779/10000000000 : ℝ)|=(5490002779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1918537987/10000000000 : ℝ)|^4259 ≤ (711022592653/6250000000000 : ℝ)^3235
        have hw : |(-1918537987/10000000000 : ℝ)|=(1918537987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_s2_7 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165357633/5000000000 : ℝ)*x 0 + (4666148341/10000000000 : ℝ)*x 1 + (4018611891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165357633/5000000000 : ℝ)^4259 ≤ (33228978566707/100000000000000 : ℝ)^3235 := by
    have hnat : (2165357633 : ℕ)^4259*100000000000000^3235 ≤ 33228978566707^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165357633 5000000000 33228978566707 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4666148341/10000000000 : ℝ)^4259 ≤ (9164555227287/25000000000000 : ℝ)^3235 := by
    have hnat : (4666148341 : ℕ)^4259*25000000000000^3235 ≤ 9164555227287^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4666148341 10000000000 9164555227287 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018611891/10000000000 : ℝ)^4259 ≤ (30112800510131/100000000000000 : ℝ)^3235 := by
    have hnat : (4018611891 : ℕ)^4259*100000000000000^3235 ≤ 30112800510131^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018611891 10000000000 30112800510131 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165357633/5000000000 : ℝ), (4666148341/10000000000 : ℝ), (4018611891/10000000000 : ℝ)] ![(33228978566707/100000000000000 : ℝ), (9164555227287/25000000000000 : ℝ), (30112800510131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165357633/5000000000 : ℝ)|^4259 ≤ (33228978566707/100000000000000 : ℝ)^3235
        have hw : |(2165357633/5000000000 : ℝ)|=(2165357633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4666148341/10000000000 : ℝ)|^4259 ≤ (9164555227287/25000000000000 : ℝ)^3235
        have hw : |(4666148341/10000000000 : ℝ)|=(4666148341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018611891/10000000000 : ℝ)|^4259 ≤ (30112800510131/100000000000000 : ℝ)^3235
        have hw : |(4018611891/10000000000 : ℝ)|=(4018611891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1299_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9897/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3239/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2389/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8143/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9897/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3239/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9897/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3239/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9897/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3239/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9897/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3239/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9897/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3239/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9897/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3239/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3239/50000 : ℝ) ^ (2129/512 : ℝ) ≤ (1142168077115549/100000000000000000000 : ℝ) := by
    have hpowers : (3239/50000 : ℝ)^2129 ≤ (1142168077115549/100000000000000000000 : ℝ)^512 := by
      have hnat : (3239 : ℕ)^2129*100000000000000000000^512 ≤ 1142168077115549^512*50000^2129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3239 50000 1142168077115549 100000000000000000000 2129 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3239/50000 : ℝ)) (X := (1142168077115549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9897/50000 : ℝ) ^ (2129/512 : ℝ) ≤ (59403725126523007/50000000000000000000 : ℝ) := by
    have hpowers : (9897/50000 : ℝ)^2129 ≤ (59403725126523007/50000000000000000000 : ℝ)^512 := by
      have hnat : (9897 : ℕ)^2129*50000000000000000000^512 ≤ 59403725126523007^512*50000^2129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9897 50000 59403725126523007 50000000000000000000 2129 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9897/50000 : ℝ)) (X := (59403725126523007/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001142168077115549/50000000000000000000 : ℝ) ≤ (5000027467589599/5000000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (50001142168077115549/50000000000000000000 : ℝ)^512 ≤ (5000027467589599/5000000000000000 : ℝ)^2129 := by
      have hnat : (50001142168077115549 : ℕ)^512*5000000000000000^2129 ≤ 5000027467589599^2129*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001142168077115549 50000000000000000000 5000027467589599 5000000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000027467589599/5000000000000000 : ℝ)) (X := (50001142168077115549/50000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100119949618330161563/100000000000000000000 : ℝ) ≤ (5001441668603163/5000000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (100119949618330161563/100000000000000000000 : ℝ)^512 ≤ (5001441668603163/5000000000000000 : ℝ)^2129 := by
      have hnat : (100119949618330161563 : ℕ)^512*5000000000000000^2129 ≤ 5001441668603163^2129*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100119949618330161563 100000000000000000000 5001441668603163 5000000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001441668603163/5000000000000000 : ℝ)) (X := (100119949618330161563/100000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25059403725126523007/25000000000000000000 : ℝ) ≤ (5002855869616727/5000000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (25059403725126523007/25000000000000000000 : ℝ)^512 ≤ (5002855869616727/5000000000000000 : ℝ)^2129 := by
      have hnat : (25059403725126523007 : ℕ)^512*5000000000000000^2129 ≤ 5002855869616727^2129*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25059403725126523007 25000000000000000000 5002855869616727 5000000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002855869616727/5000000000000000 : ℝ)) (X := (25059403725126523007/25000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1142168077115549/100000000000000000000 : ℝ) ≤ ((665620433700913651/665800000000000000 : ℝ)+2*(353550253391/166450000000000 : ℝ)*(3239/50000 : ℝ))^(2129/512 : ℝ) := by
    rw [show (665620433700913651/665800000000000000 : ℝ)+2*(353550253391/166450000000000 : ℝ)*(3239/50000 : ℝ)=(5000027467589599/5000000000000000 : ℝ) by norm_num, show 1+2*(1142168077115549/100000000000000000000 : ℝ)=(50001142168077115549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(59403725126523007/50000000000000000000 : ℝ)+(1142168077115549/100000000000000000000 : ℝ) ≤ ((665620433700913651/665800000000000000 : ℝ)+(353550253391/166450000000000 : ℝ)*((9897/50000 : ℝ)+(3239/50000 : ℝ)))^(2129/512 : ℝ) := by
    rw [show (665620433700913651/665800000000000000 : ℝ)+(353550253391/166450000000000 : ℝ)*((9897/50000 : ℝ)+(3239/50000 : ℝ))=(5001441668603163/5000000000000000 : ℝ) by norm_num, show 1+(59403725126523007/50000000000000000000 : ℝ)+(1142168077115549/100000000000000000000 : ℝ)=(100119949618330161563/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(59403725126523007/50000000000000000000 : ℝ) ≤ ((665620433700913651/665800000000000000 : ℝ)+2*(353550253391/166450000000000 : ℝ)*(9897/50000 : ℝ))^(2129/512 : ℝ) := by
    rw [show (665620433700913651/665800000000000000 : ℝ)+2*(353550253391/166450000000000 : ℝ)*(9897/50000 : ℝ)=(5002855869616727/5000000000000000 : ℝ) by norm_num, show 1+2*(59403725126523007/50000000000000000000 : ℝ)=(25059403725126523007/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (665620433700913651/665800000000000000 : ℝ)*(X 1 0+X 2 0)+(353550253391/166450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (3239/50000 : ℝ)) (hi := (9897/50000 : ℝ)) (c := (665620433700913651/665800000000000000 : ℝ)) (alpha := (353550253391/166450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (665620433700913651/665800000000000000 : ℝ)*(X 0 1+X 2 1)+(353550253391/166450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (3239/50000 : ℝ)) (hi := (9897/50000 : ℝ)) (c := (665620433700913651/665800000000000000 : ℝ)) (alpha := (353550253391/166450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (665620433700913651/665800000000000000 : ℝ)*(X 0 2+X 1 2)+(353550253391/166450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (3239/50000 : ℝ)) (hi := (9897/50000 : ℝ)) (c := (665620433700913651/665800000000000000 : ℝ)) (alpha := (353550253391/166450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2069910633/10000000000 : ℝ)*X 0 0+(686514857/1250000000 : ℝ)*X 0 1+(1293420189/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369061917/10000000000 : ℝ)*X 1 0+(-1117430347/5000000000 : ℝ)*X 1 1+(206947227/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369061727/10000000000 : ℝ)*X 2 0+(206947231/400000000 : ℝ)*X 2 1+(-446972163/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2165275917/5000000000 : ℝ)*X 0 0+(2007123059/5000000000 : ℝ)*X 0 1+(467047073/1000000000 : ℝ)*X 0 2+(2165275917/5000000000 : ℝ)*X 1 0+(2007123059/5000000000 : ℝ)*X 1 1+(467047073/1000000000 : ℝ)*X 1 2+(2165275917/5000000000 : ℝ)*X 2 0+(2007123059/5000000000 : ℝ)*X 2 1+(467047073/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-129374393/625000000 : ℝ)*X 0 0+(2587888679/5000000000 : ℝ)*X 0 1+(1372500693/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643689753/5000000000 : ℝ)*X 1 0+(-959269017/5000000000 : ℝ)*X 1 1+(2745001447/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660922457/1250000000 : ℝ)*X 2 0+(5490002779/10000000000 : ℝ)*X 2 1+(-1918537987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2165357633/5000000000 : ℝ)*X 0 0+(4666148341/10000000000 : ℝ)*X 0 1+(4018611891/10000000000 : ℝ)*X 0 2+(2165357633/5000000000 : ℝ)*X 1 0+(4666148341/10000000000 : ℝ)*X 1 1+(4018611891/10000000000 : ℝ)*X 1 2+(2165357633/5000000000 : ℝ)*X 2 0+(4666148341/10000000000 : ℝ)*X 2 1+(4018611891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9370742161558875823219353/6658000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76728091/6250000000000 : ℝ)*(base19) + (831493933/100000000000000 : ℝ)*(base23) + (76515977/50000000000000 : ℝ)*(lower2) + (501316521/100000000000000 : ℝ)*(upper3) + (31337327/20000000000000 : ℝ)*(upper5) + (466422920264801/20000000000000 : ℝ)*(major0) + (466422920264801/20000000000000 : ℝ)*(major1) + (466422920264801/20000000000000 : ℝ)*(major2) + (3140335598966611/100000000000000 : ℝ)*(sp0) + (1570168224940887/50000000000000 : ℝ)*(sp1) + (3140336846037297/100000000000000 : ℝ)*(sp2) + (1523878228090949/100000000000000 : ℝ)*(sp3) + (2078564619/100000000000000 : ℝ)*(sp4) + (6625055563/50000000000000 : ℝ)*(sp7) + (60955659128083/4000000000000 : ℝ)*(f.failure) + (314033767753123/10000000000000 : ℝ)*(f.sum) + (7726711011819/3329000000000000000000000000 : ℝ)*base65 + (17883008223606451/13316000000000000000000000000000 : ℝ)*base67 + (45776024030657549/13316000000000000000000000000000 : ℝ)*base70 + (156623959737377549/13316000000000000000000000000000 : ℝ)*base72 + (5992197999907/1664500000000000000000000000 : ℝ)*base73 + (203630583120886451/13316000000000000000000000000000 : ℝ)*base75 + (36799017077253549/13316000000000000000000000000000 : ℝ)*base78 + (86970525509405549/13316000000000000000000000000000 : ℝ)*base80 + (2791264601367/3329000000000000000000000000 : ℝ)*base82 + (117357/40000000000000000000 : ℝ)*base89 + (117357/40000000000000000000 : ℝ)*base91 + (117357/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (174887713699784877578589/16645000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1003667789/50000000000000 : ℝ)*(base19) + (296700397/12500000000000 : ℝ)*(base23) + (284110761/100000000000000 : ℝ)*(upper3) + (13372191/12500000000000 : ℝ)*(lower4) + (41490587/25000000000000 : ℝ)*(upper5) + (73855335876453/3125000000000 : ℝ)*(major0) + (73855335876453/3125000000000 : ℝ)*(major1) + (73855335876453/3125000000000 : ℝ)*(major2) + (5216378723/25000000000000 : ℝ)*(sp1) + (5126712741/20000000000000 : ℝ)*(sp2) + (1591212862341899/50000000000000 : ℝ)*(sp4) + (198900178239583/6250000000000 : ℝ)*(sp5) + (1591198858758459/50000000000000 : ℝ)*(sp6) + (77215771058923/5000000000000 : ℝ)*(sp7) + (77215771058923/5000000000000 : ℝ)*(f.failure) + (1591212862341899/50000000000000 : ℝ)*(f.sum) + (5669622363231/2080625000000000000000000000 : ℝ)*base66 + (13408251896291903/2080625000000000000000000000000 : ℝ)*base67 + (7225934012924403/2080625000000000000000000000000 : ℝ)*base69 + (4685161366859403/2080625000000000000000000000000 : ℝ)*base71 + (4917651615043/4161250000000000000000000000 : ℝ)*base73 + (2651365608203097/2080625000000000000000000000000 : ℝ)*base76 + (111865453883671/65019531250000000000000000000 : ℝ)*base78 + (2344450603878111/1040312500000000000000000000000 : ℝ)*base80 + (49872933010617/16645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (322283/50000000000000000000 : ℝ)*base90 + (322283/50000000000000000000 : ℝ)*base92 + (322283/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1299_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9897/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3239/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2389/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8143/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1299_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1299_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2389/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8143/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1299_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1299_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1299_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2389/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8143/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1299_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
