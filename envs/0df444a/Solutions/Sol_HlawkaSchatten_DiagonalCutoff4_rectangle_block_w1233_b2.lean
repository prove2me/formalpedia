-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1233_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:15:48.483827+00:00
-- url     : https://prove2.me/submissions/da293d92-0928-469c-99e3-349611cb32af

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
theorem support_rectangle_w1233_s6_0 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124096717/10000000000 : ℝ)*x 0 + (2695783391/5000000000 : ℝ)*x 1 + (1316725533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124096717/10000000000 : ℝ)^4213 ≤ (6457990516289/50000000000000 : ℝ)^3189 := by
    have hnat : (2124096717 : ℕ)^4213*50000000000000^3189 ≤ 6457990516289^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124096717 10000000000 6457990516289 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695783391/5000000000 : ℝ)^4213 ≤ (2210739944131/5000000000000 : ℝ)^3189 := by
    have hnat : (2695783391 : ℕ)^4213*5000000000000^3189 ≤ 2210739944131^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695783391 5000000000 2210739944131 5000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316725533/2500000000 : ℝ)^4213 ≤ (42869220063741/100000000000000 : ℝ)^3189 := by
    have hnat : (1316725533 : ℕ)^4213*100000000000000^3189 ≤ 42869220063741^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316725533 2500000000 42869220063741 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124096717/10000000000 : ℝ), (2695783391/5000000000 : ℝ), (1316725533/2500000000 : ℝ)] ![(6457990516289/50000000000000 : ℝ), (2210739944131/5000000000000 : ℝ), (42869220063741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124096717/10000000000 : ℝ)|^4213 ≤ (6457990516289/50000000000000 : ℝ)^3189
        have hw : |(-2124096717/10000000000 : ℝ)|=(2124096717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695783391/5000000000 : ℝ)|^4213 ≤ (2210739944131/5000000000000 : ℝ)^3189
        have hw : |(2695783391/5000000000 : ℝ)|=(2695783391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316725533/2500000000 : ℝ)|^4213 ≤ (42869220063741/100000000000000 : ℝ)^3189
        have hw : |(1316725533/2500000000 : ℝ)|=(1316725533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s6_1 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672203343/5000000000 : ℝ)*x 0 + (-437461971/2000000000 : ℝ)*x 1 + (2633451009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672203343/5000000000 : ℝ)^4213 ≤ (43704584446893/100000000000000 : ℝ)^3189 := by
    have hnat : (2672203343 : ℕ)^4213*100000000000000^3189 ≤ 43704584446893^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672203343 5000000000 43704584446893 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437461971/2000000000 : ℝ)^4213 ≤ (671309835069/5000000000000 : ℝ)^3189 := by
    have hnat : (437461971 : ℕ)^4213*5000000000000^3189 ≤ 671309835069^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437461971 2000000000 671309835069 5000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633451009/5000000000 : ℝ)^4213 ≤ (21434609418953/50000000000000 : ℝ)^3189 := by
    have hnat : (2633451009 : ℕ)^4213*50000000000000^3189 ≤ 21434609418953^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633451009 5000000000 21434609418953 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672203343/5000000000 : ℝ), (-437461971/2000000000 : ℝ), (2633451009/5000000000 : ℝ)] ![(43704584446893/100000000000000 : ℝ), (671309835069/5000000000000 : ℝ), (21434609418953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672203343/5000000000 : ℝ)|^4213 ≤ (43704584446893/100000000000000 : ℝ)^3189
        have hw : |(2672203343/5000000000 : ℝ)|=(2672203343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437461971/2000000000 : ℝ)|^4213 ≤ (671309835069/5000000000000 : ℝ)^3189
        have hw : |(-437461971/2000000000 : ℝ)|=(437461971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633451009/5000000000 : ℝ)|^4213 ≤ (21434609418953/50000000000000 : ℝ)^3189
        have hw : |(2633451009/5000000000 : ℝ)|=(2633451009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s6_2 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344406623/10000000000 : ℝ)*x 0 + (263345103/500000000 : ℝ)*x 1 + (-2187309883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344406623/10000000000 : ℝ)^4213 ≤ (43704583766273/100000000000000 : ℝ)^3189 := by
    have hnat : (5344406623 : ℕ)^4213*100000000000000^3189 ≤ 43704583766273^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344406623 10000000000 43704583766273 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263345103/500000000 : ℝ)^4213 ≤ (42869219289529/100000000000000 : ℝ)^3189 := by
    have hnat : (263345103 : ℕ)^4213*100000000000000^3189 ≤ 42869219289529^3189*500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263345103 500000000 42869219289529 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187309883/10000000000 : ℝ)^4213 ≤ (13426196928439/100000000000000 : ℝ)^3189 := by
    have hnat : (2187309883 : ℕ)^4213*100000000000000^3189 ≤ 13426196928439^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187309883 10000000000 13426196928439 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344406623/10000000000 : ℝ), (263345103/500000000 : ℝ), (-2187309883/10000000000 : ℝ)] ![(43704583766273/100000000000000 : ℝ), (42869219289529/100000000000000 : ℝ), (13426196928439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344406623/10000000000 : ℝ)|^4213 ≤ (43704583766273/100000000000000 : ℝ)^3189
        have hw : |(5344406623/10000000000 : ℝ)|=(5344406623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263345103/500000000 : ℝ)|^4213 ≤ (42869219289529/100000000000000 : ℝ)^3189
        have hw : |(263345103/500000000 : ℝ)|=(263345103/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187309883/10000000000 : ℝ)|^4213 ≤ (13426196928439/100000000000000 : ℝ)^3189
        have hw : |(-2187309883/10000000000 : ℝ)|=(2187309883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s6_3 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175999439/5000000000 : ℝ)*x 0 + (1056889147/2500000000 : ℝ)*x 1 + (2240004221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175999439/5000000000 : ℝ)^4213 ≤ (8329335931789/25000000000000 : ℝ)^3189 := by
    have hnat : (2175999439 : ℕ)^4213*25000000000000^3189 ≤ 8329335931789^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175999439 5000000000 8329335931789 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056889147/2500000000 : ℝ)^4213 ≤ (32064563093491/100000000000000 : ℝ)^3189 := by
    have hnat : (1056889147 : ℕ)^4213*100000000000000^3189 ≤ 32064563093491^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056889147 2500000000 32064563093491 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240004221/5000000000 : ℝ)^4213 ≤ (8654523289667/25000000000000 : ℝ)^3189 := by
    have hnat : (2240004221 : ℕ)^4213*25000000000000^3189 ≤ 8654523289667^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240004221 5000000000 8654523289667 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175999439/5000000000 : ℝ), (1056889147/2500000000 : ℝ), (2240004221/5000000000 : ℝ)] ![(8329335931789/25000000000000 : ℝ), (32064563093491/100000000000000 : ℝ), (8654523289667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175999439/5000000000 : ℝ)|^4213 ≤ (8329335931789/25000000000000 : ℝ)^3189
        have hw : |(2175999439/5000000000 : ℝ)|=(2175999439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056889147/2500000000 : ℝ)|^4213 ≤ (32064563093491/100000000000000 : ℝ)^3189
        have hw : |(1056889147/2500000000 : ℝ)|=(1056889147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240004221/5000000000 : ℝ)|^4213 ≤ (8654523289667/25000000000000 : ℝ)^3189
        have hw : |(2240004221/5000000000 : ℝ)|=(2240004221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s6_4 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124101579/10000000000 : ℝ)*x 0 + (2633608549/5000000000 : ℝ)*x 1 + (2695625281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124101579/10000000000 : ℝ)^4213 ≤ (12916020090143/100000000000000 : ℝ)^3189 := by
    have hnat : (2124101579 : ℕ)^4213*100000000000000^3189 ≤ 12916020090143^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124101579 10000000000 12916020090143 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633608549/5000000000 : ℝ)^4213 ≤ (42872606907157/100000000000000 : ℝ)^3189 := by
    have hnat : (2633608549 : ℕ)^4213*100000000000000^3189 ≤ 42872606907157^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633608549 5000000000 42872606907157 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695625281/5000000000 : ℝ)^4213 ≤ (22105686490649/50000000000000 : ℝ)^3189 := by
    have hnat : (2695625281 : ℕ)^4213*50000000000000^3189 ≤ 22105686490649^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695625281 5000000000 22105686490649 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124101579/10000000000 : ℝ), (2633608549/5000000000 : ℝ), (2695625281/5000000000 : ℝ)] ![(12916020090143/100000000000000 : ℝ), (42872606907157/100000000000000 : ℝ), (22105686490649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124101579/10000000000 : ℝ)|^4213 ≤ (12916020090143/100000000000000 : ℝ)^3189
        have hw : |(-2124101579/10000000000 : ℝ)|=(2124101579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633608549/5000000000 : ℝ)|^4213 ≤ (42872606907157/100000000000000 : ℝ)^3189
        have hw : |(2633608549/5000000000 : ℝ)|=(2633608549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695625281/5000000000 : ℝ)|^4213 ≤ (22105686490649/50000000000000 : ℝ)^3189
        have hw : |(2695625281/5000000000 : ℝ)|=(2695625281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s6_5 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328154351/2500000000 : ℝ)*x 0 + (-515740439/2500000000 : ℝ)*x 1 + (43130001/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328154351/2500000000 : ℝ)^4213 ≤ (43361477388673/100000000000000 : ℝ)^3189 := by
    have hnat : (1328154351 : ℕ)^4213*100000000000000^3189 ≤ 43361477388673^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328154351 2500000000 43361477388673 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515740439/2500000000 : ℝ)^4213 ≤ (12427154359777/100000000000000 : ℝ)^3189 := by
    have hnat : (515740439 : ℕ)^4213*100000000000000^3189 ≤ 12427154359777^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515740439 2500000000 12427154359777 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43130001/80000000 : ℝ)^4213 ≤ (44211368246921/100000000000000 : ℝ)^3189 := by
    have hnat : (43130001 : ℕ)^4213*100000000000000^3189 ≤ 44211368246921^3189*80000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43130001 80000000 44211368246921 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328154351/2500000000 : ℝ), (-515740439/2500000000 : ℝ), (43130001/80000000 : ℝ)] ![(43361477388673/100000000000000 : ℝ), (12427154359777/100000000000000 : ℝ), (44211368246921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328154351/2500000000 : ℝ)|^4213 ≤ (43361477388673/100000000000000 : ℝ)^3189
        have hw : |(1328154351/2500000000 : ℝ)|=(1328154351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-515740439/2500000000 : ℝ)|^4213 ≤ (12427154359777/100000000000000 : ℝ)^3189
        have hw : |(-515740439/2500000000 : ℝ)|=(515740439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43130001/80000000 : ℝ)|^4213 ≤ (44211368246921/100000000000000 : ℝ)^3189
        have hw : |(43130001/80000000 : ℝ)|=(43130001/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s6_6 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312617211/10000000000 : ℝ)*x 0 + (2695625217/5000000000 : ℝ)*x 1 + (-515740399/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312617211/10000000000 : ℝ)^4213 ≤ (10840368826897/25000000000000 : ℝ)^3189 := by
    have hnat : (5312617211 : ℕ)^4213*25000000000000^3189 ≤ 10840368826897^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312617211 10000000000 10840368826897 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695625217/5000000000 : ℝ)^4213 ≤ (4421137159457/10000000000000 : ℝ)^3189 := by
    have hnat : (2695625217 : ℕ)^4213*10000000000000^3189 ≤ 4421137159457^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695625217 5000000000 4421137159457 10000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515740399/2500000000 : ℝ)^4213 ≤ (12427153086457/100000000000000 : ℝ)^3189 := by
    have hnat : (515740399 : ℕ)^4213*100000000000000^3189 ≤ 12427153086457^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515740399 2500000000 12427153086457 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312617211/10000000000 : ℝ), (2695625217/5000000000 : ℝ), (-515740399/2500000000 : ℝ)] ![(10840368826897/25000000000000 : ℝ), (4421137159457/10000000000000 : ℝ), (12427153086457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312617211/10000000000 : ℝ)|^4213 ≤ (10840368826897/25000000000000 : ℝ)^3189
        have hw : |(5312617211/10000000000 : ℝ)|=(5312617211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695625217/5000000000 : ℝ)|^4213 ≤ (4421137159457/10000000000000 : ℝ)^3189
        have hw : |(2695625217/5000000000 : ℝ)|=(2695625217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515740399/2500000000 : ℝ)|^4213 ≤ (12427153086457/100000000000000 : ℝ)^3189
        have hw : |(-515740399/2500000000 : ℝ)|=(515740399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s6_7 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2176004479/5000000000 : ℝ)*x 0 + (17497539/39062500 : ℝ)*x 1 + (1057049211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176004479/5000000000 : ℝ)^4213 ≤ (16658722837639/50000000000000 : ℝ)^3189 := by
    have hnat : (2176004479 : ℕ)^4213*50000000000000^3189 ≤ 16658722837639^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176004479 5000000000 16658722837639 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17497539/39062500 : ℝ)^4213 ≤ (8652893904891/25000000000000 : ℝ)^3189 := by
    have hnat : (17497539 : ℕ)^4213*25000000000000^3189 ≤ 8652893904891^3189*39062500^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17497539 39062500 8652893904891 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057049211/2500000000 : ℝ)^4213 ≤ (6414195738033/20000000000000 : ℝ)^3189 := by
    have hnat : (1057049211 : ℕ)^4213*20000000000000^3189 ≤ 6414195738033^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057049211 2500000000 6414195738033 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176004479/5000000000 : ℝ), (17497539/39062500 : ℝ), (1057049211/2500000000 : ℝ)] ![(16658722837639/50000000000000 : ℝ), (8652893904891/25000000000000 : ℝ), (6414195738033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176004479/5000000000 : ℝ)|^4213 ≤ (16658722837639/50000000000000 : ℝ)^3189
        have hw : |(2176004479/5000000000 : ℝ)|=(2176004479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17497539/39062500 : ℝ)|^4213 ≤ (8652893904891/25000000000000 : ℝ)^3189
        have hw : |(17497539/39062500 : ℝ)|=(17497539/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057049211/2500000000 : ℝ)|^4213 ≤ (6414195738033/20000000000000 : ℝ)^3189
        have hw : |(1057049211/2500000000 : ℝ)|=(1057049211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1233_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11463/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7063/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5721/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7063/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5721/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7063/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5721/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7063/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5721/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7063/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5721/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7063/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5721/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5721/50000 : ℝ) ^ (8425/2048 : ℝ) ≤ (535739875567437/4000000000000000000 : ℝ) := by
    have hpowers : (5721/50000 : ℝ)^8425 ≤ (535739875567437/4000000000000000000 : ℝ)^2048 := by
      have hnat : (5721 : ℕ)^8425*4000000000000000000^2048 ≤ 535739875567437^2048*50000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5721 50000 535739875567437 4000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5721/50000 : ℝ)) (X := (535739875567437/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7063/50000 : ℝ) ^ (8425/2048 : ℝ) ≤ (31869473641254661/100000000000000000000 : ℝ) := by
    have hpowers : (7063/50000 : ℝ)^8425 ≤ (31869473641254661/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7063 : ℕ)^8425*100000000000000000000^2048 ≤ 31869473641254661^2048*50000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7063 50000 31869473641254661 100000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7063/50000 : ℝ)) (X := (31869473641254661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000535739875567437/2000000000000000000 : ℝ) ≤ (2000130217691629/2000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (2000535739875567437/2000000000000000000 : ℝ)^2048 ≤ (2000130217691629/2000000000000000 : ℝ)^8425 := by
      have hnat : (2000535739875567437 : ℕ)^2048*2000000000000000^8425 ≤ 2000130217691629^8425*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000535739875567437 2000000000000000000 2000130217691629 2000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000130217691629/2000000000000000 : ℝ)) (X := (2000535739875567437/2000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022631485265220293/50000000000000000000 : ℝ) ≤ (5000550045629139/5000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (50022631485265220293/50000000000000000000 : ℝ)^2048 ≤ (5000550045629139/5000000000000000 : ℝ)^8425 := by
      have hnat : (50022631485265220293 : ℕ)^2048*5000000000000000^8425 ≤ 5000550045629139^8425*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022631485265220293 50000000000000000000 5000550045629139 5000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000550045629139/5000000000000000 : ℝ)) (X := (50022631485265220293/50000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031869473641254661/50000000000000000000 : ℝ) ≤ (10001549094058411/10000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (50031869473641254661/50000000000000000000 : ℝ)^2048 ≤ (10001549094058411/10000000000000000 : ℝ)^8425 := by
      have hnat : (50031869473641254661 : ℕ)^2048*10000000000000000^8425 ≤ 10001549094058411^8425*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031869473641254661 50000000000000000000 10001549094058411 10000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001549094058411/10000000000000000 : ℝ)) (X := (50031869473641254661/50000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(535739875567437/4000000000000000000 : ℝ) ≤ ((3353934067667927201/3355000000000000000 : ℝ)+2*(449002800133/268400000000000 : ℝ)*(5721/50000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (3353934067667927201/3355000000000000000 : ℝ)+2*(449002800133/268400000000000 : ℝ)*(5721/50000 : ℝ)=(2000130217691629/2000000000000000 : ℝ) by norm_num, show 1+2*(535739875567437/4000000000000000000 : ℝ)=(2000535739875567437/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31869473641254661/100000000000000000000 : ℝ)+(535739875567437/4000000000000000000 : ℝ) ≤ ((3353934067667927201/3355000000000000000 : ℝ)+(449002800133/268400000000000 : ℝ)*((7063/50000 : ℝ)+(5721/50000 : ℝ)))^(8425/2048 : ℝ) := by
    rw [show (3353934067667927201/3355000000000000000 : ℝ)+(449002800133/268400000000000 : ℝ)*((7063/50000 : ℝ)+(5721/50000 : ℝ))=(5000550045629139/5000000000000000 : ℝ) by norm_num, show 1+(31869473641254661/100000000000000000000 : ℝ)+(535739875567437/4000000000000000000 : ℝ)=(50022631485265220293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31869473641254661/100000000000000000000 : ℝ) ≤ ((3353934067667927201/3355000000000000000 : ℝ)+2*(449002800133/268400000000000 : ℝ)*(7063/50000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (3353934067667927201/3355000000000000000 : ℝ)+2*(449002800133/268400000000000 : ℝ)*(7063/50000 : ℝ)=(10001549094058411/10000000000000000 : ℝ) by norm_num, show 1+2*(31869473641254661/100000000000000000000 : ℝ)=(50031869473641254661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3353934067667927201/3355000000000000000 : ℝ)*(X 1 0+X 2 0)+(449002800133/268400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (5721/50000 : ℝ)) (hi := (7063/50000 : ℝ)) (c := (3353934067667927201/3355000000000000000 : ℝ)) (alpha := (449002800133/268400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3353934067667927201/3355000000000000000 : ℝ)*(X 0 1+X 2 1)+(449002800133/268400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (5721/50000 : ℝ)) (hi := (7063/50000 : ℝ)) (c := (3353934067667927201/3355000000000000000 : ℝ)) (alpha := (449002800133/268400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3353934067667927201/3355000000000000000 : ℝ)*(X 0 2+X 1 2)+(449002800133/268400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (5721/50000 : ℝ)) (hi := (7063/50000 : ℝ)) (c := (3353934067667927201/3355000000000000000 : ℝ)) (alpha := (449002800133/268400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2124096717/10000000000 : ℝ)*X 0 0+(2695783391/5000000000 : ℝ)*X 0 1+(1316725533/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672203343/5000000000 : ℝ)*X 1 0+(-437461971/2000000000 : ℝ)*X 1 1+(2633451009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344406623/10000000000 : ℝ)*X 2 0+(263345103/500000000 : ℝ)*X 2 1+(-2187309883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175999439/5000000000 : ℝ)*X 0 0+(1056889147/2500000000 : ℝ)*X 0 1+(2240004221/5000000000 : ℝ)*X 0 2+(2175999439/5000000000 : ℝ)*X 1 0+(1056889147/2500000000 : ℝ)*X 1 1+(2240004221/5000000000 : ℝ)*X 1 2+(2175999439/5000000000 : ℝ)*X 2 0+(1056889147/2500000000 : ℝ)*X 2 1+(2240004221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2124101579/10000000000 : ℝ)*X 0 0+(2633608549/5000000000 : ℝ)*X 0 1+(2695625281/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328154351/2500000000 : ℝ)*X 1 0+(-515740439/2500000000 : ℝ)*X 1 1+(43130001/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312617211/10000000000 : ℝ)*X 2 0+(2695625217/5000000000 : ℝ)*X 2 1+(-515740399/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176004479/5000000000 : ℝ)*X 0 0+(17497539/39062500 : ℝ)*X 0 1+(1057049211/2500000000 : ℝ)*X 0 2+(2176004479/5000000000 : ℝ)*X 1 0+(17497539/39062500 : ℝ)*X 1 1+(1057049211/2500000000 : ℝ)*X 1 2+(2176004479/5000000000 : ℝ)*X 2 0+(17497539/39062500 : ℝ)*X 2 1+(1057049211/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (813637183851158908336982151/83875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104913057/6250000000000 : ℝ)*(base19) + (1469451009/100000000000000 : ℝ)*(base23) + (12249279/20000000000000 : ℝ)*(lower2) + (221547211/100000000000000 : ℝ)*(upper3) + (74229343/100000000000000 : ℝ)*(upper5) + (2995700150988317/50000000000000 : ℝ)*(major0) + (2995700150988317/50000000000000 : ℝ)*(major1) + (2995700150988317/50000000000000 : ℝ)*(major2) + (4010782619653417/50000000000000 : ℝ)*(sp0) + (4010801141612797/50000000000000 : ℝ)*(sp1) + (4010801246191749/50000000000000 : ℝ)*(sp2) + (3961172201989929/100000000000000 : ℝ)*(sp3) + (38722527673/100000000000000 : ℝ)*(sp4) + (4823355149/20000000000000 : ℝ)*(sp7) + (1980598159382837/50000000000000 : ℝ)*(f.failure) + (4010801980917253/50000000000000 : ℝ)*(f.sum) + (26314913437991/6710000000000000000000000000 : ℝ)*base65 + (2039004636228976783/167750000000000000000000000000000 : ℝ)*base68 + (1051044406153476783/167750000000000000000000000000000 : ℝ)*base70 + (33111093559476783/167750000000000000000000000000000 : ℝ)*base72 + (33904301863859/6710000000000000000000000000 : ℝ)*base74 + (4775034481437023217/167750000000000000000000000000000 : ℝ)*base75 + (1049348493523023217/167750000000000000000000000000000 : ℝ)*base77 + (1371773096028476783/167750000000000000000000000000000 : ℝ)*base80 + (762318189279/6710000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (10239039/2500000000000000000000 : ℝ)*base89 + (10239039/2500000000000000000000 : ℝ)*base91 + (10239039/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9137435366876016462969/2684000000000000000000000000 : ℝ) := by norm_num
    linear_combination (522157503/50000000000000 : ℝ)*(base19) + (111709843/12500000000000 : ℝ)*(base23) + (28241597/100000000000000 : ℝ)*(lower2) + (128974319/100000000000000 : ℝ)*(upper3) + (1632713/2000000000000 : ℝ)*(lower4) + (243071751/100000000000000 : ℝ)*(upper5) + (1204365548774219/20000000000000 : ℝ)*(major0) + (1204365548774219/20000000000000 : ℝ)*(major1) + (1204365548774219/20000000000000 : ℝ)*(major2) + (697774761/10000000000000 : ℝ)*(sp2) + (8062342043654729/100000000000000 : ℝ)*(sp4) + (8062340999339723/100000000000000 : ℝ)*(sp5) + (64498673377827/800000000000 : ℝ)*(sp6) + (1990656665303567/50000000000000 : ℝ)*(sp7) + (1990656665303567/50000000000000 : ℝ)*(f.failure) + (8062342043654729/100000000000000 : ℝ)*(f.sum) + (14395080940923/2684000000000000000000000000 : ℝ)*base65 + (112109747979081481/67100000000000000000000000000000 : ℝ)*base68 + (535112878260681481/67100000000000000000000000000000 : ℝ)*base70 + (568027717582318519/67100000000000000000000000000000 : ℝ)*base71 + (1838512647237/536800000000000000000000000 : ℝ)*base74 + (116696006612618519/67100000000000000000000000000000 : ℝ)*base75 + (24843999044981481/67100000000000000000000000000000 : ℝ)*base78 + (39698304694118519/67100000000000000000000000000000 : ℝ)*base79 + (14690298933617/2684000000000000000000000000 : ℝ)*base82 + (17433651/2500000000000000000000 : ℝ)*base90 + (17433651/2500000000000000000000 : ℝ)*base92 + (17433651/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1233_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1233_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1233_s7_0 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-531028561/2500000000 : ℝ)*x 0 + (2695681589/5000000000 : ℝ)*x 1 + (210683767/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531028561/2500000000 : ℝ)^4213 ≤ (6458060915569/50000000000000 : ℝ)^3189 := by
    have hnat : (531028561 : ℕ)^4213*50000000000000^3189 ≤ 6458060915569^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531028561 2500000000 6458060915569 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695681589/5000000000 : ℝ)^4213 ≤ (44212593046329/100000000000000 : ℝ)^3189 := by
    have hnat : (2695681589 : ℕ)^4213*100000000000000^3189 ≤ 44212593046329^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695681589 5000000000 44212593046329 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210683767/400000000 : ℝ)^4213 ≤ (42871285102929/100000000000000 : ℝ)^3189 := by
    have hnat : (210683767 : ℕ)^4213*100000000000000^3189 ≤ 42871285102929^3189*400000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210683767 400000000 42871285102929 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531028561/2500000000 : ℝ), (2695681589/5000000000 : ℝ), (210683767/400000000 : ℝ)] ![(6458060915569/50000000000000 : ℝ), (44212593046329/100000000000000 : ℝ), (42871285102929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531028561/2500000000 : ℝ)|^4213 ≤ (6458060915569/50000000000000 : ℝ)^3189
        have hw : |(-531028561/2500000000 : ℝ)|=(531028561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695681589/5000000000 : ℝ)|^4213 ≤ (44212593046329/100000000000000 : ℝ)^3189
        have hw : |(2695681589/5000000000 : ℝ)|=(2695681589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210683767/400000000 : ℝ)|^4213 ≤ (42871285102929/100000000000000 : ℝ)^3189
        have hw : |(210683767/400000000 : ℝ)|=(210683767/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s7_1 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672177501/5000000000 : ℝ)*x 0 + (-2187123833/10000000000 : ℝ)*x 1 + (5267094229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672177501/5000000000 : ℝ)^4213 ≤ (43704026079717/100000000000000 : ℝ)^3189 := by
    have hnat : (2672177501 : ℕ)^4213*100000000000000^3189 ≤ 43704026079717^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672177501 5000000000 43704026079717 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187123833/10000000000 : ℝ)^4213 ≤ (2684937645347/20000000000000 : ℝ)^3189 := by
    have hnat : (2187123833 : ℕ)^4213*20000000000000^3189 ≤ 2684937645347^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187123833 10000000000 2684937645347 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267094229/10000000000 : ℝ)^4213 ≤ (8574257136719/20000000000000 : ℝ)^3189 := by
    have hnat : (5267094229 : ℕ)^4213*20000000000000^3189 ≤ 8574257136719^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267094229 10000000000 8574257136719 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672177501/5000000000 : ℝ), (-2187123833/10000000000 : ℝ), (5267094229/10000000000 : ℝ)] ![(43704026079717/100000000000000 : ℝ), (2684937645347/20000000000000 : ℝ), (8574257136719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672177501/5000000000 : ℝ)|^4213 ≤ (43704026079717/100000000000000 : ℝ)^3189
        have hw : |(2672177501/5000000000 : ℝ)|=(2672177501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2187123833/10000000000 : ℝ)|^4213 ≤ (2684937645347/20000000000000 : ℝ)^3189
        have hw : |(-2187123833/10000000000 : ℝ)|=(2187123833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267094229/10000000000 : ℝ)|^4213 ≤ (8574257136719/20000000000000 : ℝ)^3189
        have hw : |(5267094229/10000000000 : ℝ)|=(5267094229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s7_2 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344355027/10000000000 : ℝ)*x 0 + (5267094211/10000000000 : ℝ)*x 1 + (-2187123823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344355027/10000000000 : ℝ)^4213 ≤ (10926006587451/25000000000000 : ℝ)^3189 := by
    have hnat : (5344355027 : ℕ)^4213*25000000000000^3189 ≤ 10926006587451^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344355027 10000000000 10926006587451 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267094211/10000000000 : ℝ)^4213 ≤ (1071782137251/2500000000000 : ℝ)^3189 := by
    have hnat : (5267094211 : ℕ)^4213*2500000000000^3189 ≤ 1071782137251^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267094211 10000000000 1071782137251 2500000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187123823/10000000000 : ℝ)^4213 ≤ (2684937629129/20000000000000 : ℝ)^3189 := by
    have hnat : (2187123823 : ℕ)^4213*20000000000000^3189 ≤ 2684937629129^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187123823 10000000000 2684937629129 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344355027/10000000000 : ℝ), (5267094211/10000000000 : ℝ), (-2187123823/10000000000 : ℝ)] ![(10926006587451/25000000000000 : ℝ), (1071782137251/2500000000000 : ℝ), (2684937629129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344355027/10000000000 : ℝ)|^4213 ≤ (10926006587451/25000000000000 : ℝ)^3189
        have hw : |(5344355027/10000000000 : ℝ)|=(5344355027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267094211/10000000000 : ℝ)|^4213 ≤ (1071782137251/2500000000000 : ℝ)^3189
        have hw : |(5267094211/10000000000 : ℝ)|=(5267094211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187123823/10000000000 : ℝ)|^4213 ≤ (2684937629129/20000000000000 : ℝ)^3189
        have hw : |(-2187123823/10000000000 : ℝ)|=(2187123823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s7_3 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4352009021/10000000000 : ℝ)*x 0 + (4227956031/10000000000 : ℝ)*x 1 + (447960631/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352009021/10000000000 : ℝ)^4213 ≤ (16658723156227/50000000000000 : ℝ)^3189 := by
    have hnat : (4352009021 : ℕ)^4213*50000000000000^3189 ≤ 16658723156227^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352009021 10000000000 16658723156227 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227956031/10000000000 : ℝ)^4213 ≤ (32068565620211/100000000000000 : ℝ)^3189 := by
    have hnat : (4227956031 : ℕ)^4213*100000000000000^3189 ≤ 32068565620211^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227956031 10000000000 32068565620211 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447960631/1000000000 : ℝ)^4213 ≤ (34613988059767/100000000000000 : ℝ)^3189 := by
    have hnat : (447960631 : ℕ)^4213*100000000000000^3189 ≤ 34613988059767^3189*1000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447960631 1000000000 34613988059767 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352009021/10000000000 : ℝ), (4227956031/10000000000 : ℝ), (447960631/1000000000 : ℝ)] ![(16658723156227/50000000000000 : ℝ), (32068565620211/100000000000000 : ℝ), (34613988059767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352009021/10000000000 : ℝ)|^4213 ≤ (16658723156227/50000000000000 : ℝ)^3189
        have hw : |(4352009021/10000000000 : ℝ)|=(4352009021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227956031/10000000000 : ℝ)|^4213 ≤ (32068565620211/100000000000000 : ℝ)^3189
        have hw : |(4227956031/10000000000 : ℝ)|=(4227956031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447960631/1000000000 : ℝ)|^4213 ≤ (34613988059767/100000000000000 : ℝ)^3189
        have hw : |(447960631/1000000000 : ℝ)|=(447960631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s7_4 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16594679/78125000 : ℝ)*x 0 + (5267407529/10000000000 : ℝ)*x 1 + (1078209739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16594679/78125000 : ℝ)^4213 ≤ (2583231866071/20000000000000 : ℝ)^3189 := by
    have hnat : (16594679 : ℕ)^4213*20000000000000^3189 ≤ 2583231866071^3189*78125000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16594679 78125000 2583231866071 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267407529/10000000000 : ℝ)^4213 ≤ (42874654651721/100000000000000 : ℝ)^3189 := by
    have hnat : (5267407529 : ℕ)^4213*100000000000000^3189 ≤ 42874654651721^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267407529 10000000000 42874654651721 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078209739/2000000000 : ℝ)^4213 ≤ (44209186004661/100000000000000 : ℝ)^3189 := by
    have hnat : (1078209739 : ℕ)^4213*100000000000000^3189 ≤ 44209186004661^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078209739 2000000000 44209186004661 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16594679/78125000 : ℝ), (5267407529/10000000000 : ℝ), (1078209739/2000000000 : ℝ)] ![(2583231866071/20000000000000 : ℝ), (42874654651721/100000000000000 : ℝ), (44209186004661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16594679/78125000 : ℝ)|^4213 ≤ (2583231866071/20000000000000 : ℝ)^3189
        have hw : |(-16594679/78125000 : ℝ)|=(16594679/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267407529/10000000000 : ℝ)|^4213 ≤ (42874654651721/100000000000000 : ℝ)^3189
        have hw : |(5267407529/10000000000 : ℝ)|=(5267407529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078209739/2000000000 : ℝ)|^4213 ≤ (44209186004661/100000000000000 : ℝ)^3189
        have hw : |(1078209739/2000000000 : ℝ)|=(1078209739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s7_5 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265633329/500000000 : ℝ)*x 0 + (-2063169333/10000000000 : ℝ)*x 1 + (1078209739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265633329/500000000 : ℝ)^4213 ≤ (43362007645557/100000000000000 : ℝ)^3189 := by
    have hnat : (265633329 : ℕ)^4213*100000000000000^3189 ≤ 43362007645557^3189*500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265633329 500000000 43362007645557 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063169333/10000000000 : ℝ)^4213 ≤ (12428806335659/100000000000000 : ℝ)^3189 := by
    have hnat : (2063169333 : ℕ)^4213*100000000000000^3189 ≤ 12428806335659^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063169333 10000000000 12428806335659 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078209739/2000000000 : ℝ)^4213 ≤ (44209186004661/100000000000000 : ℝ)^3189 := by
    have hnat : (1078209739 : ℕ)^4213*100000000000000^3189 ≤ 44209186004661^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078209739 2000000000 44209186004661 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265633329/500000000 : ℝ), (-2063169333/10000000000 : ℝ), (1078209739/2000000000 : ℝ)] ![(43362007645557/100000000000000 : ℝ), (12428806335659/100000000000000 : ℝ), (44209186004661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265633329/500000000 : ℝ)|^4213 ≤ (43362007645557/100000000000000 : ℝ)^3189
        have hw : |(265633329/500000000 : ℝ)|=(265633329/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2063169333/10000000000 : ℝ)|^4213 ≤ (12428806335659/100000000000000 : ℝ)^3189
        have hw : |(-2063169333/10000000000 : ℝ)|=(2063169333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078209739/2000000000 : ℝ)|^4213 ≤ (44209186004661/100000000000000 : ℝ)^3189
        have hw : |(1078209739/2000000000 : ℝ)|=(1078209739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s7_6 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265633329/500000000 : ℝ)*x 0 + (1078209739/2000000000 : ℝ)*x 1 + (-2063169333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265633329/500000000 : ℝ)^4213 ≤ (43362007645557/100000000000000 : ℝ)^3189 := by
    have hnat : (265633329 : ℕ)^4213*100000000000000^3189 ≤ 43362007645557^3189*500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265633329 500000000 43362007645557 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078209739/2000000000 : ℝ)^4213 ≤ (44209186004661/100000000000000 : ℝ)^3189 := by
    have hnat : (1078209739 : ℕ)^4213*100000000000000^3189 ≤ 44209186004661^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078209739 2000000000 44209186004661 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063169333/10000000000 : ℝ)^4213 ≤ (12428806335659/100000000000000 : ℝ)^3189 := by
    have hnat : (2063169333 : ℕ)^4213*100000000000000^3189 ≤ 12428806335659^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063169333 10000000000 12428806335659 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265633329/500000000 : ℝ), (1078209739/2000000000 : ℝ), (-2063169333/10000000000 : ℝ)] ![(43362007645557/100000000000000 : ℝ), (44209186004661/100000000000000 : ℝ), (12428806335659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265633329/500000000 : ℝ)|^4213 ≤ (43362007645557/100000000000000 : ℝ)^3189
        have hw : |(265633329/500000000 : ℝ)|=(265633329/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078209739/2000000000 : ℝ)|^4213 ≤ (44209186004661/100000000000000 : ℝ)^3189
        have hw : |(1078209739/2000000000 : ℝ)|=(1078209739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2063169333/10000000000 : ℝ)|^4213 ≤ (12428806335659/100000000000000 : ℝ)^3189
        have hw : |(-2063169333/10000000000 : ℝ)|=(2063169333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s7_7 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (68000289/156250000 : ℝ)*x 0 + (895794367/2000000000 : ℝ)*x 1 + (4228592801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68000289/156250000 : ℝ)^4213 ≤ (6663508428347/20000000000000 : ℝ)^3189 := by
    have hnat : (68000289 : ℕ)^4213*20000000000000^3189 ≤ 6663508428347^3189*156250000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68000289 156250000 6663508428347 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895794367/2000000000 : ℝ)^4213 ≤ (346075113659/1000000000000 : ℝ)^3189 := by
    have hnat : (895794367 : ℕ)^4213*1000000000000^3189 ≤ 346075113659^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895794367 2000000000 346075113659 1000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228592801/10000000000 : ℝ)^4213 ≤ (256599571829/800000000000 : ℝ)^3189 := by
    have hnat : (4228592801 : ℕ)^4213*800000000000^3189 ≤ 256599571829^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228592801 10000000000 256599571829 800000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68000289/156250000 : ℝ), (895794367/2000000000 : ℝ), (4228592801/10000000000 : ℝ)] ![(6663508428347/20000000000000 : ℝ), (346075113659/1000000000000 : ℝ), (256599571829/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68000289/156250000 : ℝ)|^4213 ≤ (6663508428347/20000000000000 : ℝ)^3189
        have hw : |(68000289/156250000 : ℝ)|=(68000289/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895794367/2000000000 : ℝ)|^4213 ≤ (346075113659/1000000000000 : ℝ)^3189
        have hw : |(895794367/2000000000 : ℝ)|=(895794367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228592801/10000000000 : ℝ)|^4213 ≤ (256599571829/800000000000 : ℝ)^3189
        have hw : |(4228592801/10000000000 : ℝ)|=(4228592801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1233_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11467/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (141/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11463/100000 : ℝ) ^ (8425/2048 : ℝ) ≤ (421715922740119/3125000000000000000 : ℝ) := by
    have hpowers : (11463/100000 : ℝ)^8425 ≤ (421715922740119/3125000000000000000 : ℝ)^2048 := by
      have hnat : (11463 : ℕ)^8425*3125000000000000000^2048 ≤ 421715922740119^2048*100000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11463 100000 421715922740119 3125000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11463/100000 : ℝ)) (X := (421715922740119/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1763/12500 : ℝ) ^ (8425/2048 : ℝ) ≤ (31665785770914827/100000000000000000000 : ℝ) := by
    have hpowers : (1763/12500 : ℝ)^8425 ≤ (31665785770914827/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1763 : ℕ)^8425*100000000000000000000^2048 ≤ 31665785770914827^2048*12500^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 12500 31665785770914827 100000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/12500 : ℝ)) (X := (31665785770914827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562921715922740119/1562500000000000000 : ℝ) ≤ (10000656017854549/10000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (1562921715922740119/1562500000000000000 : ℝ)^2048 ≤ (10000656017854549/10000000000000000 : ℝ)^8425 := by
      have hnat : (1562921715922740119 : ℕ)^2048*10000000000000000^8425 ≤ 10000656017854549^8425*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562921715922740119 1562500000000000000 10000656017854549 10000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000656017854549/10000000000000000 : ℝ)) (X := (1562921715922740119/1562500000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009032139059719727/20000000000000000000 : ℝ) ≤ (625068600371281/625000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (20009032139059719727/20000000000000000000 : ℝ)^2048 ≤ (625068600371281/625000000000000 : ℝ)^8425 := by
      have hnat : (20009032139059719727 : ℕ)^2048*625000000000000^8425 ≤ 625068600371281^8425*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009032139059719727 20000000000000000000 625068600371281 625000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625068600371281/625000000000000 : ℝ)) (X := (20009032139059719727/20000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031665785770914827/50000000000000000000 : ℝ) ≤ (10001539194026443/10000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (50031665785770914827/50000000000000000000 : ℝ)^2048 ≤ (10001539194026443/10000000000000000 : ℝ)^8425 := by
      have hnat : (50031665785770914827 : ℕ)^2048*10000000000000000^8425 ≤ 10001539194026443^8425*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031665785770914827 50000000000000000000 10001539194026443 10000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001539194026443/10000000000000000 : ℝ)) (X := (50031665785770914827/50000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(421715922740119/3125000000000000000 : ℝ) ≤ ((26401608694695442987/26410000000000000000 : ℝ)+2*(441588085947/264100000000000 : ℝ)*(11463/100000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (26401608694695442987/26410000000000000000 : ℝ)+2*(441588085947/264100000000000 : ℝ)*(11463/100000 : ℝ)=(10000656017854549/10000000000000000 : ℝ) by norm_num, show 1+2*(421715922740119/3125000000000000000 : ℝ)=(1562921715922740119/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31665785770914827/100000000000000000000 : ℝ)+(421715922740119/3125000000000000000 : ℝ) ≤ ((26401608694695442987/26410000000000000000 : ℝ)+(441588085947/264100000000000 : ℝ)*((1763/12500 : ℝ)+(11463/100000 : ℝ)))^(8425/2048 : ℝ) := by
    rw [show (26401608694695442987/26410000000000000000 : ℝ)+(441588085947/264100000000000 : ℝ)*((1763/12500 : ℝ)+(11463/100000 : ℝ))=(625068600371281/625000000000000 : ℝ) by norm_num, show 1+(31665785770914827/100000000000000000000 : ℝ)+(421715922740119/3125000000000000000 : ℝ)=(20009032139059719727/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31665785770914827/100000000000000000000 : ℝ) ≤ ((26401608694695442987/26410000000000000000 : ℝ)+2*(441588085947/264100000000000 : ℝ)*(1763/12500 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (26401608694695442987/26410000000000000000 : ℝ)+2*(441588085947/264100000000000 : ℝ)*(1763/12500 : ℝ)=(10001539194026443/10000000000000000 : ℝ) by norm_num, show 1+2*(31665785770914827/100000000000000000000 : ℝ)=(50031665785770914827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26401608694695442987/26410000000000000000 : ℝ)*(X 1 0+X 2 0)+(441588085947/264100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (11463/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (26401608694695442987/26410000000000000000 : ℝ)) (alpha := (441588085947/264100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26401608694695442987/26410000000000000000 : ℝ)*(X 0 1+X 2 1)+(441588085947/264100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (11463/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (26401608694695442987/26410000000000000000 : ℝ)) (alpha := (441588085947/264100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26401608694695442987/26410000000000000000 : ℝ)*(X 0 2+X 1 2)+(441588085947/264100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (11463/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (26401608694695442987/26410000000000000000 : ℝ)) (alpha := (441588085947/264100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-531028561/2500000000 : ℝ)*X 0 0+(2695681589/5000000000 : ℝ)*X 0 1+(210683767/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672177501/5000000000 : ℝ)*X 1 0+(-2187123833/10000000000 : ℝ)*X 1 1+(5267094229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344355027/10000000000 : ℝ)*X 2 0+(5267094211/10000000000 : ℝ)*X 2 1+(-2187123823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352009021/10000000000 : ℝ)*X 0 0+(4227956031/10000000000 : ℝ)*X 0 1+(447960631/1000000000 : ℝ)*X 0 2+(4352009021/10000000000 : ℝ)*X 1 0+(4227956031/10000000000 : ℝ)*X 1 1+(447960631/1000000000 : ℝ)*X 1 2+(4352009021/10000000000 : ℝ)*X 2 0+(4227956031/10000000000 : ℝ)*X 2 1+(447960631/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-16594679/78125000 : ℝ)*X 0 0+(5267407529/10000000000 : ℝ)*X 0 1+(1078209739/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265633329/500000000 : ℝ)*X 1 0+(-2063169333/10000000000 : ℝ)*X 1 1+(1078209739/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265633329/500000000 : ℝ)*X 2 0+(1078209739/2000000000 : ℝ)*X 2 1+(-2063169333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((68000289/156250000 : ℝ)*X 0 0+(895794367/2000000000 : ℝ)*X 0 1+(4228592801/10000000000 : ℝ)*X 0 2+(68000289/156250000 : ℝ)*X 1 0+(895794367/2000000000 : ℝ)*X 1 1+(4228592801/10000000000 : ℝ)*X 1 2+(68000289/156250000 : ℝ)*X 2 0+(895794367/2000000000 : ℝ)*X 2 1+(4228592801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6718460970153806029637397153/660250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (473097301/25000000000000 : ℝ)*(base19) + (1810504291/100000000000000 : ℝ)*(base23) + (6388013/10000000000000 : ℝ)*(lower2) + (240920011/100000000000000 : ℝ)*(upper3) + (87990649/50000000000000 : ℝ)*(upper5) + (6010497522103073/100000000000000 : ℝ)*(major0) + (6010497522103073/100000000000000 : ℝ)*(major1) + (6010497522103073/100000000000000 : ℝ)*(major2) + (62868093676833/781250000000 : ℝ)*(sp0) + (4023585212060887/50000000000000 : ℝ)*(sp1) + (8047170506006687/100000000000000 : ℝ)*(sp2) + (248362148446359/6250000000000 : ℝ)*(sp3) + (56325876353/100000000000000 : ℝ)*(sp4) + (28013365681/100000000000000 : ℝ)*(sp7) + (1986911194253713/50000000000000 : ℝ)*(f.failure) + (4023586158255489/50000000000000 : ℝ)*(f.sum) + (10776573311509/13205000000000000000000000000 : ℝ)*base66 + (10062345087505900949/2641000000000000000000000000000000 : ℝ)*base68 + (52941098560373900949/2641000000000000000000000000000000 : ℝ)*base70 + (462746538454099051/2641000000000000000000000000000000 : ℝ)*base71 + (16907188858973/6602500000000000000000000000 : ℝ)*base73 + (100566034235124900949/2641000000000000000000000000000000 : ℝ)*base76 + (18103620796186900949/2641000000000000000000000000000000 : ℝ)*base78 + (30726195010373900949/2641000000000000000000000000000000 : ℝ)*base80 + (547684597531/13205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (29633811/2500000000000000000000 : ℝ)*base89 + (29633811/2500000000000000000000 : ℝ)*base91 + (29633811/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3575544652838906308581/528200000000000000000000000 : ℝ) := by norm_num
    linear_combination (606066709/50000000000000 : ℝ)*(base19) + (1318798709/100000000000000 : ℝ)*(base23) + (135829607/100000000000000 : ℝ)*(upper3) + (6067683/12500000000000 : ℝ)*(lower4) + (34548359/25000000000000 : ℝ)*(upper5) + (1208186430117129/20000000000000 : ℝ)*(major0) + (1208186430117129/20000000000000 : ℝ)*(major1) + (1208186430117129/20000000000000 : ℝ)*(major2) + (34112266983/100000000000000 : ℝ)*(sp1) + (4584582459/12500000000000 : ℝ)*(sp2) + (505494995236743/6250000000000 : ℝ)*(sp4) + (4043942299693743/50000000000000 : ℝ)*(sp5) + (8087881928329507/100000000000000 : ℝ)*(sp6) + (998486037935009/25000000000000 : ℝ)*(sp7) + (998486037935009/25000000000000 : ℝ)*(f.failure) + (505494995236743/6250000000000 : ℝ)*(f.sum) + (7496441001837/2641000000000000000000000000 : ℝ)*base66 + (2781798382130475677/528200000000000000000000000000000 : ℝ)*base68 + (1582299786280724323/528200000000000000000000000000000 : ℝ)*base69 + (420917573628475677/528200000000000000000000000000000 : ℝ)*base72 + (893784542917/132050000000000000000000000 : ℝ)*base74 + (9290340494561324323/528200000000000000000000000000000 : ℝ)*base75 + (3176002751275924323/528200000000000000000000000000000 : ℝ)*base77 + (9120458998651475677/528200000000000000000000000000000 : ℝ)*base80 + (7338313962573/1320500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4580323/1250000000000000000000 : ℝ)*base89 + (4580323/1250000000000000000000 : ℝ)*base91 + (4580323/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1233_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1233_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1233_s8_0 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124116871/10000000000 : ℝ)*x 0 + (5391325729/10000000000 : ℝ)*x 1 + (658391243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124116871/10000000000 : ℝ)^4213 ≤ (6458071467243/50000000000000 : ℝ)^3189 := by
    have hnat : (2124116871 : ℕ)^4213*50000000000000^3189 ≤ 6458071467243^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124116871 10000000000 6458071467243 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391325729/10000000000 : ℝ)^4213 ≤ (44212187328513/100000000000000 : ℝ)^3189 := by
    have hnat : (5391325729 : ℕ)^4213*100000000000000^3189 ≤ 44212187328513^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391325729 10000000000 44212187328513 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658391243/1250000000 : ℝ)^4213 ≤ (2679479358113/6250000000000 : ℝ)^3189 := by
    have hnat : (658391243 : ℕ)^4213*6250000000000^3189 ≤ 2679479358113^3189*1250000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658391243 1250000000 2679479358113 6250000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124116871/10000000000 : ℝ), (5391325729/10000000000 : ℝ), (658391243/1250000000 : ℝ)] ![(6458071467243/50000000000000 : ℝ), (44212187328513/100000000000000 : ℝ), (2679479358113/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124116871/10000000000 : ℝ)|^4213 ≤ (6458071467243/50000000000000 : ℝ)^3189
        have hw : |(-2124116871/10000000000 : ℝ)|=(2124116871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391325729/10000000000 : ℝ)|^4213 ≤ (44212187328513/100000000000000 : ℝ)^3189
        have hw : |(5391325729/10000000000 : ℝ)|=(5391325729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658391243/1250000000 : ℝ)|^4213 ≤ (2679479358113/6250000000000 : ℝ)^3189
        have hw : |(658391243/1250000000 : ℝ)|=(658391243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s8_1 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167010807/312500000 : ℝ)*x 0 + (-2187088903/10000000000 : ℝ)*x 1 + (5267129791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167010807/312500000 : ℝ)^4213 ≤ (43703926925539/100000000000000 : ℝ)^3189 := by
    have hnat : (167010807 : ℕ)^4213*100000000000000^3189 ≤ 43703926925539^3189*312500000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167010807 312500000 43703926925539 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187088903/10000000000 : ℝ)^4213 ≤ (13424404979781/100000000000000 : ℝ)^3189 := by
    have hnat : (2187088903 : ℕ)^4213*100000000000000^3189 ≤ 13424404979781^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187088903 10000000000 13424404979781 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267129791/10000000000 : ℝ)^4213 ≤ (8574333616917/20000000000000 : ℝ)^3189 := by
    have hnat : (5267129791 : ℕ)^4213*20000000000000^3189 ≤ 8574333616917^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267129791 10000000000 8574333616917 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167010807/312500000 : ℝ), (-2187088903/10000000000 : ℝ), (5267129791/10000000000 : ℝ)] ![(43703926925539/100000000000000 : ℝ), (13424404979781/100000000000000 : ℝ), (8574333616917/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167010807/312500000 : ℝ)|^4213 ≤ (43703926925539/100000000000000 : ℝ)^3189
        have hw : |(167010807/312500000 : ℝ)|=(167010807/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2187088903/10000000000 : ℝ)|^4213 ≤ (13424404979781/100000000000000 : ℝ)^3189
        have hw : |(-2187088903/10000000000 : ℝ)|=(2187088903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267129791/10000000000 : ℝ)|^4213 ≤ (8574333616917/20000000000000 : ℝ)^3189
        have hw : |(5267129791/10000000000 : ℝ)|=(5267129791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s8_2 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068869133/2000000000 : ℝ)*x 0 + (1053425983/2000000000 : ℝ)*x 1 + (-43741779/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068869133/2000000000 : ℝ)^4213 ≤ (43703925207789/100000000000000 : ℝ)^3189 := by
    have hnat : (1068869133 : ℕ)^4213*100000000000000^3189 ≤ 43703925207789^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068869133 2000000000 43703925207789 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053425983/2000000000 : ℝ)^4213 ≤ (42871669417969/100000000000000 : ℝ)^3189 := by
    have hnat : (1053425983 : ℕ)^4213*100000000000000^3189 ≤ 42871669417969^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053425983 2000000000 42871669417969 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43741779/200000000 : ℝ)^4213 ≤ (13424405360903/100000000000000 : ℝ)^3189 := by
    have hnat : (43741779 : ℕ)^4213*100000000000000^3189 ≤ 13424405360903^3189*200000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43741779 200000000 13424405360903 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068869133/2000000000 : ℝ), (1053425983/2000000000 : ℝ), (-43741779/200000000 : ℝ)] ![(43703925207789/100000000000000 : ℝ), (42871669417969/100000000000000 : ℝ), (13424405360903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068869133/2000000000 : ℝ)|^4213 ≤ (43703925207789/100000000000000 : ℝ)^3189
        have hw : |(1068869133/2000000000 : ℝ)|=(1068869133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053425983/2000000000 : ℝ)|^4213 ≤ (42871669417969/100000000000000 : ℝ)^3189
        have hw : |(1053425983/2000000000 : ℝ)|=(1053425983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43741779/200000000 : ℝ)|^4213 ≤ (13424405360903/100000000000000 : ℝ)^3189
        have hw : |(-43741779/200000000 : ℝ)|=(43741779/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s8_3 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (870402173/2000000000 : ℝ)*x 0 + (422802979/1000000000 : ℝ)*x 1 + (4479532079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870402173/2000000000 : ℝ)^4213 ≤ (520585390039/1562500000000 : ℝ)^3189 := by
    have hnat : (870402173 : ℕ)^4213*1562500000000^3189 ≤ 520585390039^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870402173 2000000000 520585390039 1562500000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422802979/1000000000 : ℝ)^4213 ≤ (32069304718589/100000000000000 : ℝ)^3189 := by
    have hnat : (422802979 : ℕ)^4213*100000000000000^3189 ≤ 32069304718589^3189*1000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422802979 1000000000 32069304718589 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479532079/10000000000 : ℝ)^4213 ≤ (17306615148827/50000000000000 : ℝ)^3189 := by
    have hnat : (4479532079 : ℕ)^4213*50000000000000^3189 ≤ 17306615148827^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479532079 10000000000 17306615148827 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870402173/2000000000 : ℝ), (422802979/1000000000 : ℝ), (4479532079/10000000000 : ℝ)] ![(520585390039/1562500000000 : ℝ), (32069304718589/100000000000000 : ℝ), (17306615148827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870402173/2000000000 : ℝ)|^4213 ≤ (520585390039/1562500000000 : ℝ)^3189
        have hw : |(870402173/2000000000 : ℝ)|=(870402173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422802979/1000000000 : ℝ)|^4213 ≤ (32069304718589/100000000000000 : ℝ)^3189
        have hw : |(422802979/1000000000 : ℝ)|=(422802979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479532079/10000000000 : ℝ)|^4213 ≤ (17306615148827/50000000000000 : ℝ)^3189
        have hw : |(4479532079/10000000000 : ℝ)|=(4479532079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s8_4 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124121193/10000000000 : ℝ)*x 0 + (5267443107/10000000000 : ℝ)*x 1 + (539101169/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124121193/10000000000 : ℝ)^4213 ≤ (12916177654211/100000000000000 : ℝ)^3189 := by
    have hnat : (2124121193 : ℕ)^4213*100000000000000^3189 ≤ 12916177654211^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124121193 10000000000 12916177654211 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267443107/10000000000 : ℝ)^4213 ≤ (10718759308017/25000000000000 : ℝ)^3189 := by
    have hnat : (5267443107 : ℕ)^4213*25000000000000^3189 ≤ 10718759308017^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267443107 10000000000 10718759308017 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539101169/1000000000 : ℝ)^4213 ≤ (44208785104589/100000000000000 : ℝ)^3189 := by
    have hnat : (539101169 : ℕ)^4213*100000000000000^3189 ≤ 44208785104589^3189*1000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539101169 1000000000 44208785104589 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124121193/10000000000 : ℝ), (5267443107/10000000000 : ℝ), (539101169/1000000000 : ℝ)] ![(12916177654211/100000000000000 : ℝ), (10718759308017/25000000000000 : ℝ), (44208785104589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124121193/10000000000 : ℝ)|^4213 ≤ (12916177654211/100000000000000 : ℝ)^3189
        have hw : |(-2124121193/10000000000 : ℝ)|=(2124121193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267443107/10000000000 : ℝ)|^4213 ≤ (10718759308017/25000000000000 : ℝ)^3189
        have hw : |(5267443107/10000000000 : ℝ)|=(5267443107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539101169/1000000000 : ℝ)|^4213 ≤ (44208785104589/100000000000000 : ℝ)^3189
        have hw : |(539101169/1000000000 : ℝ)|=(539101169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s8_5 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328169093/2500000000 : ℝ)*x 0 + (-1031603223/5000000000 : ℝ)*x 1 + (2695505843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328169093/2500000000 : ℝ)^4213 ≤ (5420264153913/12500000000000 : ℝ)^3189 := by
    have hnat : (1328169093 : ℕ)^4213*12500000000000^3189 ≤ 5420264153913^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328169093 2500000000 5420264153913 12500000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031603223/5000000000 : ℝ)^4213 ≤ (1553637712563/12500000000000 : ℝ)^3189 := by
    have hnat : (1031603223 : ℕ)^4213*12500000000000^3189 ≤ 1553637712563^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031603223 5000000000 1553637712563 12500000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695505843/5000000000 : ℝ)^4213 ≤ (8841757012251/20000000000000 : ℝ)^3189 := by
    have hnat : (2695505843 : ℕ)^4213*20000000000000^3189 ≤ 8841757012251^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695505843 5000000000 8841757012251 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328169093/2500000000 : ℝ), (-1031603223/5000000000 : ℝ), (2695505843/5000000000 : ℝ)] ![(5420264153913/12500000000000 : ℝ), (1553637712563/12500000000000 : ℝ), (8841757012251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328169093/2500000000 : ℝ)|^4213 ≤ (5420264153913/12500000000000 : ℝ)^3189
        have hw : |(1328169093/2500000000 : ℝ)|=(1328169093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031603223/5000000000 : ℝ)|^4213 ≤ (1553637712563/12500000000000 : ℝ)^3189
        have hw : |(-1031603223/5000000000 : ℝ)|=(1031603223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695505843/5000000000 : ℝ)|^4213 ≤ (8841757012251/20000000000000 : ℝ)^3189
        have hw : |(2695505843/5000000000 : ℝ)|=(2695505843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s8_6 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166021119/312500000 : ℝ)*x 0 + (1347752969/2500000000 : ℝ)*x 1 + (-41264139/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166021119/312500000 : ℝ)^4213 ≤ (4336210714977/10000000000000 : ℝ)^3189 := by
    have hnat : (166021119 : ℕ)^4213*10000000000000^3189 ≤ 4336210714977^3189*312500000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166021119 312500000 4336210714977 10000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347752969/2500000000 : ℝ)^4213 ≤ (884175742393/2000000000000 : ℝ)^3189 := by
    have hnat : (1347752969 : ℕ)^4213*2000000000000^3189 ≤ 884175742393^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347752969 2500000000 884175742393 2000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41264139/200000000 : ℝ)^4213 ≤ (12429105711613/100000000000000 : ℝ)^3189 := by
    have hnat : (41264139 : ℕ)^4213*100000000000000^3189 ≤ 12429105711613^3189*200000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41264139 200000000 12429105711613 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166021119/312500000 : ℝ), (1347752969/2500000000 : ℝ), (-41264139/200000000 : ℝ)] ![(4336210714977/10000000000000 : ℝ), (884175742393/2000000000000 : ℝ), (12429105711613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166021119/312500000 : ℝ)|^4213 ≤ (4336210714977/10000000000000 : ℝ)^3189
        have hw : |(166021119/312500000 : ℝ)|=(166021119/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347752969/2500000000 : ℝ)|^4213 ≤ (884175742393/2000000000000 : ℝ)^3189
        have hw : |(1347752969/2500000000 : ℝ)|=(1347752969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41264139/200000000 : ℝ)|^4213 ≤ (12429105711613/100000000000000 : ℝ)^3189
        have hw : |(-41264139/200000000 : ℝ)|=(41264139/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s8_7 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4352019989/10000000000 : ℝ)*x 0 + (139965571/312500000 : ℝ)*x 1 + (4228666227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352019989/10000000000 : ℝ)^4213 ≤ (16658778620903/50000000000000 : ℝ)^3189 := by
    have hnat : (4352019989 : ℕ)^4213*50000000000000^3189 ≤ 16658778620903^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352019989 10000000000 16658778620903 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139965571/312500000 : ℝ)^4213 ≤ (2162922528561/6250000000000 : ℝ)^3189 := by
    have hnat : (139965571 : ℕ)^4213*6250000000000^3189 ≤ 2162922528561^3189*312500000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139965571 312500000 2162922528561 6250000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228666227/10000000000 : ℝ)^4213 ≤ (8018920568941/25000000000000 : ℝ)^3189 := by
    have hnat : (4228666227 : ℕ)^4213*25000000000000^3189 ≤ 8018920568941^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228666227 10000000000 8018920568941 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352019989/10000000000 : ℝ), (139965571/312500000 : ℝ), (4228666227/10000000000 : ℝ)] ![(16658778620903/50000000000000 : ℝ), (2162922528561/6250000000000 : ℝ), (8018920568941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352019989/10000000000 : ℝ)|^4213 ≤ (16658778620903/50000000000000 : ℝ)^3189
        have hw : |(4352019989/10000000000 : ℝ)|=(4352019989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(139965571/312500000 : ℝ)|^4213 ≤ (2162922528561/6250000000000 : ℝ)^3189
        have hw : |(139965571/312500000 : ℝ)|=(139965571/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228666227/10000000000 : ℝ)|^4213 ≤ (8018920568941/25000000000000 : ℝ)^3189
        have hw : |(4228666227/10000000000 : ℝ)|=(4228666227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1233_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2867/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14099/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11467/100000 : ℝ) ^ (8425/2048 : ℝ) ≤ (6757145964196663/50000000000000000000 : ℝ) := by
    have hpowers : (11467/100000 : ℝ)^8425 ≤ (6757145964196663/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11467 : ℕ)^8425*50000000000000000000^2048 ≤ 6757145964196663^2048*100000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11467 100000 6757145964196663 50000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11467/100000 : ℝ)) (X := (6757145964196663/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (141/1000 : ℝ) ^ (8425/2048 : ℝ) ≤ (15814428869844921/50000000000000000000 : ℝ) := by
    have hpowers : (141/1000 : ℝ)^8425 ≤ (15814428869844921/50000000000000000000 : ℝ)^2048 := by
      have hnat : (141 : ℕ)^8425*50000000000000000000^2048 ≤ 15814428869844921^2048*1000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 1000 15814428869844921 50000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/1000 : ℝ)) (X := (15814428869844921/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006757145964196663/25000000000000000000 : ℝ) ≤ (10000656959980209/10000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (25006757145964196663/25000000000000000000 : ℝ)^2048 ≤ (10000656959980209/10000000000000000 : ℝ)^8425 := by
      have hnat : (25006757145964196663 : ℕ)^2048*10000000000000000^8425 ≤ 10000656959980209^8425*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006757145964196663 25000000000000000000 10000656959980209 10000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000656959980209/10000000000000000 : ℝ)) (X := (25006757145964196663/25000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126410723427127599/3125000000000000000 : ℝ) ≤ (2000219435915279/2000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (3126410723427127599/3125000000000000000 : ℝ)^2048 ≤ (2000219435915279/2000000000000000 : ℝ)^8425 := by
      have hnat : (3126410723427127599 : ℕ)^2048*2000000000000000^8425 ≤ 2000219435915279^8425*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126410723427127599 3125000000000000000 2000219435915279 2000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000219435915279/2000000000000000 : ℝ)) (X := (3126410723427127599/3125000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015814428869844921/25000000000000000000 : ℝ) ≤ (10001537399172581/10000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (25015814428869844921/25000000000000000000 : ℝ)^2048 ≤ (10001537399172581/10000000000000000 : ℝ)^8425 := by
      have hnat : (25015814428869844921 : ℕ)^2048*10000000000000000^8425 ≤ 10001537399172581^8425*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015814428869844921 25000000000000000000 10001537399172581 10000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001537399172581/10000000000000000 : ℝ)) (X := (25015814428869844921/25000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6757145964196663/50000000000000000000 : ℝ) ≤ ((26321633779408960573/26330000000000000000 : ℝ)+2*(220109798093/131650000000000 : ℝ)*(11467/100000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (26321633779408960573/26330000000000000000 : ℝ)+2*(220109798093/131650000000000 : ℝ)*(11467/100000 : ℝ)=(10000656959980209/10000000000000000 : ℝ) by norm_num, show 1+2*(6757145964196663/50000000000000000000 : ℝ)=(25006757145964196663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15814428869844921/50000000000000000000 : ℝ)+(6757145964196663/50000000000000000000 : ℝ) ≤ ((26321633779408960573/26330000000000000000 : ℝ)+(220109798093/131650000000000 : ℝ)*((141/1000 : ℝ)+(11467/100000 : ℝ)))^(8425/2048 : ℝ) := by
    rw [show (26321633779408960573/26330000000000000000 : ℝ)+(220109798093/131650000000000 : ℝ)*((141/1000 : ℝ)+(11467/100000 : ℝ))=(2000219435915279/2000000000000000 : ℝ) by norm_num, show 1+(15814428869844921/50000000000000000000 : ℝ)+(6757145964196663/50000000000000000000 : ℝ)=(3126410723427127599/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15814428869844921/50000000000000000000 : ℝ) ≤ ((26321633779408960573/26330000000000000000 : ℝ)+2*(220109798093/131650000000000 : ℝ)*(141/1000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (26321633779408960573/26330000000000000000 : ℝ)+2*(220109798093/131650000000000 : ℝ)*(141/1000 : ℝ)=(10001537399172581/10000000000000000 : ℝ) by norm_num, show 1+2*(15814428869844921/50000000000000000000 : ℝ)=(25015814428869844921/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26321633779408960573/26330000000000000000 : ℝ)*(X 1 0+X 2 0)+(220109798093/131650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (11467/100000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (26321633779408960573/26330000000000000000 : ℝ)) (alpha := (220109798093/131650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26321633779408960573/26330000000000000000 : ℝ)*(X 0 1+X 2 1)+(220109798093/131650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (11467/100000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (26321633779408960573/26330000000000000000 : ℝ)) (alpha := (220109798093/131650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26321633779408960573/26330000000000000000 : ℝ)*(X 0 2+X 1 2)+(220109798093/131650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (11467/100000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (26321633779408960573/26330000000000000000 : ℝ)) (alpha := (220109798093/131650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2124116871/10000000000 : ℝ)*X 0 0+(5391325729/10000000000 : ℝ)*X 0 1+(658391243/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167010807/312500000 : ℝ)*X 1 0+(-2187088903/10000000000 : ℝ)*X 1 1+(5267129791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068869133/2000000000 : ℝ)*X 2 0+(1053425983/2000000000 : ℝ)*X 2 1+(-43741779/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870402173/2000000000 : ℝ)*X 0 0+(422802979/1000000000 : ℝ)*X 0 1+(4479532079/10000000000 : ℝ)*X 0 2+(870402173/2000000000 : ℝ)*X 1 0+(422802979/1000000000 : ℝ)*X 1 1+(4479532079/10000000000 : ℝ)*X 1 2+(870402173/2000000000 : ℝ)*X 2 0+(422802979/1000000000 : ℝ)*X 2 1+(4479532079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2124121193/10000000000 : ℝ)*X 0 0+(5267443107/10000000000 : ℝ)*X 0 1+(539101169/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328169093/2500000000 : ℝ)*X 1 0+(-1031603223/5000000000 : ℝ)*X 1 1+(2695505843/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166021119/312500000 : ℝ)*X 2 0+(1347752969/2500000000 : ℝ)*X 2 1+(-41264139/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352019989/10000000000 : ℝ)*X 0 0+(139965571/312500000 : ℝ)*X 0 1+(4228666227/10000000000 : ℝ)*X 0 2+(4352019989/10000000000 : ℝ)*X 1 0+(139965571/312500000 : ℝ)*X 1 1+(4228666227/10000000000 : ℝ)*X 1 2+(4352019989/10000000000 : ℝ)*X 2 0+(139965571/312500000 : ℝ)*X 2 1+(4228666227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2535565734842300601587571381/329125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1663423951/100000000000000 : ℝ)*(base19) + (1286022963/100000000000000 : ℝ)*(base23) + (3683563/5000000000000 : ℝ)*(lower2) + (255200633/100000000000000 : ℝ)*(upper3) + (33183651/100000000000000 : ℝ)*(upper5) + (1503503496075101/25000000000000 : ℝ)*(major0) + (1503503496075101/25000000000000 : ℝ)*(major1) + (1503503496075101/25000000000000 : ℝ)*(major2) + (2012961854748857/25000000000000 : ℝ)*(sp0) + (4025939380724089/50000000000000 : ℝ)*(sp1) + (4025939569424583/50000000000000 : ℝ)*(sp2) + (1988062521656841/50000000000000 : ℝ)*(sp3) + (16502938351/50000000000000 : ℝ)*(sp4) + (22243616329/100000000000000 : ℝ)*(sp7) + (994036821732503/25000000000000 : ℝ)*(f.failure) + (805188042487213/10000000000000 : ℝ)*(f.sum) + (52293320412039/13165000000000000000000000000 : ℝ)*base65 + (486707434815907127/658250000000000000000000000000000 : ℝ)*base68 + (1230049653807342873/658250000000000000000000000000000 : ℝ)*base69 + (1787260905224842873/658250000000000000000000000000000 : ℝ)*base71 + (12230218482017/6582500000000000000000000000 : ℝ)*base73 + (8965850793722842873/658250000000000000000000000000000 : ℝ)*base75 + (5528698579398657127/658250000000000000000000000000000 : ℝ)*base78 + (11256577382281092873/658250000000000000000000000000000 : ℝ)*base79 + (16495502339079/13165000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16555941/1250000000000000000000 : ℝ)*base89 + (16555941/1250000000000000000000 : ℝ)*base91 + (16555941/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2983655051246572085798373117/658250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (614090807/50000000000000 : ℝ)*(base19) + (568291239/100000000000000 : ℝ)*(base23) + (330510959/100000000000000 : ℝ)*(lower1) + (33869413/25000000000000 : ℝ)*(lower3) + (39974071/20000000000000 : ℝ)*(lower4) + (14354241/12500000000000 : ℝ)*(lower5) + (3022224758136843/50000000000000 : ℝ)*(major0) + (3022224758136843/50000000000000 : ℝ)*(major1) + (3022224758136843/50000000000000 : ℝ)*(major2) + (14844667617/50000000000000 : ℝ)*(sp1) + (2023157308488577/25000000000000 : ℝ)*(sp4) + (404629915821873/5000000000000 : ℝ)*(sp5) + (8092628665663069/100000000000000 : ℝ)*(sp6) + (499533705937849/12500000000000 : ℝ)*(sp7) + (499533705937849/12500000000000 : ℝ)*(f.failure) + (2023157308488577/25000000000000 : ℝ)*(f.sum) + (11433555260583/1645625000000000000000000000 : ℝ)*base66 + (5480917330464508961/1316500000000000000000000000000000 : ℝ)*base68 + (2011763475589491039/1316500000000000000000000000000000 : ℝ)*base69 + (5387663214409491039/1316500000000000000000000000000000 : ℝ)*base71 + (28270454369067/6582500000000000000000000000 : ℝ)*base74 + (10339182875321508961/1316500000000000000000000000000000 : ℝ)*base76 + (6241872313854508961/1316500000000000000000000000000000 : ℝ)*base78 + (3329825430916508961/1316500000000000000000000000000000 : ℝ)*base80 + (38530886570493/6582500000000000000000000000 : ℝ)*base81 + (3837803/625000000000000000000 : ℝ)*base89 + (3837803/625000000000000000000 : ℝ)*base91 + (3837803/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1233_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1233_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1233_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1233_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1233_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1233_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1233_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
