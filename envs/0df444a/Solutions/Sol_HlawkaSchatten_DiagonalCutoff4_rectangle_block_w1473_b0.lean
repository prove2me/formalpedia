-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1473_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:11:00.229965+00:00
-- url     : https://prove2.me/submissions/f7fe5c6e-deed-48e9-99d3-52d48aae2f63

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
theorem support_rectangle_w1473_s0_0 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1727991477/10000000000 : ℝ)*x 0 + (1188699001/2000000000 : ℝ)*x 1 + (1209571029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1727991477/10000000000 : ℝ)^4443 ≤ (10213702071013/100000000000000 : ℝ)^3419 := by
    have hnat : (1727991477 : ℕ)^4443*100000000000000^3419 ≤ 10213702071013^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727991477 10000000000 10213702071013 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1188699001/2000000000 : ℝ)^4443 ≤ (25429441864441/50000000000000 : ℝ)^3419 := by
    have hnat : (1188699001 : ℕ)^4443*50000000000000^3419 ≤ 25429441864441^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188699001 2000000000 25429441864441 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1209571029/2500000000 : ℝ)^4443 ≤ (38927414196613/100000000000000 : ℝ)^3419 := by
    have hnat : (1209571029 : ℕ)^4443*100000000000000^3419 ≤ 38927414196613^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209571029 2500000000 38927414196613 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1727991477/10000000000 : ℝ), (1188699001/2000000000 : ℝ), (1209571029/2500000000 : ℝ)] ![(10213702071013/100000000000000 : ℝ), (25429441864441/50000000000000 : ℝ), (38927414196613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1727991477/10000000000 : ℝ)|^4443 ≤ (10213702071013/100000000000000 : ℝ)^3419
        have hw : |(-1727991477/10000000000 : ℝ)|=(1727991477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1188699001/2000000000 : ℝ)|^4443 ≤ (25429441864441/50000000000000 : ℝ)^3419
        have hw : |(1188699001/2000000000 : ℝ)|=(1188699001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1209571029/2500000000 : ℝ)|^4443 ≤ (38927414196613/100000000000000 : ℝ)^3419
        have hw : |(1209571029/2500000000 : ℝ)|=(1209571029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s0_1 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (685814257/1250000000 : ℝ)*x 0 + (-470134587/2000000000 : ℝ)*x 1 + (96765681/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685814257/1250000000 : ℝ)^4443 ≤ (22918441252481/50000000000000 : ℝ)^3419 := by
    have hnat : (685814257 : ℕ)^4443*50000000000000^3419 ≤ 22918441252481^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685814257 1250000000 22918441252481 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (470134587/2000000000 : ℝ)^4443 ≤ (3047140794571/20000000000000 : ℝ)^3419 := by
    have hnat : (470134587 : ℕ)^4443*20000000000000^3419 ≤ 3047140794571^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470134587 2000000000 3047140794571 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96765681/200000000 : ℝ)^4443 ≤ (7785482701311/20000000000000 : ℝ)^3419 := by
    have hnat : (96765681 : ℕ)^4443*20000000000000^3419 ≤ 7785482701311^3419*200000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96765681 200000000 7785482701311 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685814257/1250000000 : ℝ), (-470134587/2000000000 : ℝ), (96765681/200000000 : ℝ)] ![(22918441252481/50000000000000 : ℝ), (3047140794571/20000000000000 : ℝ), (7785482701311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685814257/1250000000 : ℝ)|^4443 ≤ (22918441252481/50000000000000 : ℝ)^3419
        have hw : |(685814257/1250000000 : ℝ)|=(685814257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-470134587/2000000000 : ℝ)|^4443 ≤ (3047140794571/20000000000000 : ℝ)^3419
        have hw : |(-470134587/2000000000 : ℝ)|=(470134587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(96765681/200000000 : ℝ)|^4443 ≤ (7785482701311/20000000000000 : ℝ)^3419
        have hw : |(96765681/200000000 : ℝ)|=(96765681/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s0_2 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5486514187/10000000000 : ℝ)*x 0 + (4838283883/10000000000 : ℝ)*x 1 + (-2350672973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5486514187/10000000000 : ℝ)^4443 ≤ (45836883927183/100000000000000 : ℝ)^3419 := by
    have hnat : (5486514187 : ℕ)^4443*100000000000000^3419 ≤ 45836883927183^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486514187 10000000000 45836883927183 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4838283883/10000000000 : ℝ)^4443 ≤ (77854823521/200000000000 : ℝ)^3419 := by
    have hnat : (4838283883 : ℕ)^4443*200000000000^3419 ≤ 77854823521^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838283883 10000000000 77854823521 200000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2350672973/10000000000 : ℝ)^4443 ≤ (3047140858583/20000000000000 : ℝ)^3419 := by
    have hnat : (2350672973 : ℕ)^4443*20000000000000^3419 ≤ 3047140858583^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350672973 10000000000 3047140858583 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5486514187/10000000000 : ℝ), (4838283883/10000000000 : ℝ), (-2350672973/10000000000 : ℝ)] ![(45836883927183/100000000000000 : ℝ), (77854823521/200000000000 : ℝ), (3047140858583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5486514187/10000000000 : ℝ)|^4443 ≤ (45836883927183/100000000000000 : ℝ)^3419
        have hw : |(5486514187/10000000000 : ℝ)|=(5486514187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4838283883/10000000000 : ℝ)|^4443 ≤ (77854823521/200000000000 : ℝ)^3419
        have hw : |(4838283883/10000000000 : ℝ)|=(4838283883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2350672973/10000000000 : ℝ)|^4443 ≤ (3047140858583/20000000000000 : ℝ)^3419
        have hw : |(-2350672973/10000000000 : ℝ)|=(2350672973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s0_3 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4155832357/10000000000 : ℝ)*x 0 + (3091655943/10000000000 : ℝ)*x 1 + (5529100011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4155832357/10000000000 : ℝ)^4443 ≤ (15974050089869/50000000000000 : ℝ)^3419 := by
    have hnat : (4155832357 : ℕ)^4443*50000000000000^3419 ≤ 15974050089869^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155832357 10000000000 15974050089869 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091655943/10000000000 : ℝ)^4443 ≤ (21752140122099/100000000000000 : ℝ)^3419 := by
    have hnat : (3091655943 : ℕ)^4443*100000000000000^3419 ≤ 21752140122099^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091655943 10000000000 21752140122099 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5529100011/10000000000 : ℝ)^4443 ≤ (46299759697431/100000000000000 : ℝ)^3419 := by
    have hnat : (5529100011 : ℕ)^4443*100000000000000^3419 ≤ 46299759697431^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529100011 10000000000 46299759697431 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4155832357/10000000000 : ℝ), (3091655943/10000000000 : ℝ), (5529100011/10000000000 : ℝ)] ![(15974050089869/50000000000000 : ℝ), (21752140122099/100000000000000 : ℝ), (46299759697431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4155832357/10000000000 : ℝ)|^4443 ≤ (15974050089869/50000000000000 : ℝ)^3419
        have hw : |(4155832357/10000000000 : ℝ)|=(4155832357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091655943/10000000000 : ℝ)|^4443 ≤ (21752140122099/100000000000000 : ℝ)^3419
        have hw : |(3091655943/10000000000 : ℝ)|=(3091655943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5529100011/10000000000 : ℝ)|^4443 ≤ (46299759697431/100000000000000 : ℝ)^3419
        have hw : |(5529100011/10000000000 : ℝ)|=(5529100011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s0_4 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-173185969/1000000000 : ℝ)*x 0 + (4866670733/10000000000 : ℝ)*x 1 + (5914086667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173185969/1000000000 : ℝ)^4443 ≤ (5121711920507/50000000000000 : ℝ)^3419 := by
    have hnat : (173185969 : ℕ)^4443*50000000000000^3419 ≤ 5121711920507^3419*1000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173185969 1000000000 5121711920507 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4866670733/10000000000 : ℝ)^4443 ≤ (313795748411/800000000000 : ℝ)^3419 := by
    have hnat : (4866670733 : ℕ)^4443*800000000000^3419 ≤ 313795748411^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4866670733 10000000000 313795748411 800000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5914086667/10000000000 : ℝ)^4443 ≤ (50532107598937/100000000000000 : ℝ)^3419 := by
    have hnat : (5914086667 : ℕ)^4443*100000000000000^3419 ≤ 50532107598937^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5914086667 10000000000 50532107598937 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-173185969/1000000000 : ℝ), (4866670733/10000000000 : ℝ), (5914086667/10000000000 : ℝ)] ![(5121711920507/50000000000000 : ℝ), (313795748411/800000000000 : ℝ), (50532107598937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-173185969/1000000000 : ℝ)|^4443 ≤ (5121711920507/50000000000000 : ℝ)^3419
        have hw : |(-173185969/1000000000 : ℝ)|=(173185969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4866670733/10000000000 : ℝ)|^4443 ≤ (313795748411/800000000000 : ℝ)^3419
        have hw : |(4866670733/10000000000 : ℝ)|=(4866670733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5914086667/10000000000 : ℝ)|^4443 ≤ (50532107598937/100000000000000 : ℝ)^3419
        have hw : |(5914086667/10000000000 : ℝ)|=(5914086667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s0_5 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184789009/10000000000 : ℝ)*x 0 + (-254974039/2000000000 : ℝ)*x 1 + (739260849/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184789009/10000000000 : ℝ)^4443 ≤ (21294245675507/50000000000000 : ℝ)^3419 := by
    have hnat : (5184789009 : ℕ)^4443*50000000000000^3419 ≤ 21294245675507^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184789009 10000000000 21294245675507 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254974039/2000000000 : ℝ)^4443 ≤ (3439699823557/50000000000000 : ℝ)^3419 := by
    have hnat : (254974039 : ℕ)^4443*50000000000000^3419 ≤ 3439699823557^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254974039 2000000000 3439699823557 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739260849/1250000000 : ℝ)^4443 ≤ (10106421797373/20000000000000 : ℝ)^3419 := by
    have hnat : (739260849 : ℕ)^4443*20000000000000^3419 ≤ 10106421797373^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739260849 1250000000 10106421797373 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184789009/10000000000 : ℝ), (-254974039/2000000000 : ℝ), (739260849/1250000000 : ℝ)] ![(21294245675507/50000000000000 : ℝ), (3439699823557/50000000000000 : ℝ), (10106421797373/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184789009/10000000000 : ℝ)|^4443 ≤ (21294245675507/50000000000000 : ℝ)^3419
        have hw : |(5184789009/10000000000 : ℝ)|=(5184789009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-254974039/2000000000 : ℝ)|^4443 ≤ (3439699823557/50000000000000 : ℝ)^3419
        have hw : |(-254974039/2000000000 : ℝ)|=(254974039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(739260849/1250000000 : ℝ)|^4443 ≤ (10106421797373/20000000000000 : ℝ)^3419
        have hw : |(739260849/1250000000 : ℝ)|=(739260849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s0_6 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103695779/200000000 : ℝ)*x 0 + (118281733/200000000 : ℝ)*x 1 + (-1274870509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103695779/200000000 : ℝ)^4443 ≤ (2661780670077/6250000000000 : ℝ)^3419 := by
    have hnat : (103695779 : ℕ)^4443*6250000000000^3419 ≤ 2661780670077^3419*200000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103695779 200000000 2661780670077 6250000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118281733/200000000 : ℝ)^4443 ≤ (25266053705089/50000000000000 : ℝ)^3419 := by
    have hnat : (118281733 : ℕ)^4443*50000000000000^3419 ≤ 25266053705089^3419*200000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118281733 200000000 25266053705089 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1274870509/10000000000 : ℝ)^4443 ≤ (6879401848983/100000000000000 : ℝ)^3419 := by
    have hnat : (1274870509 : ℕ)^4443*100000000000000^3419 ≤ 6879401848983^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274870509 10000000000 6879401848983 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103695779/200000000 : ℝ), (118281733/200000000 : ℝ), (-1274870509/10000000000 : ℝ)] ![(2661780670077/6250000000000 : ℝ), (25266053705089/50000000000000 : ℝ), (6879401848983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103695779/200000000 : ℝ)|^4443 ≤ (2661780670077/6250000000000 : ℝ)^3419
        have hw : |(103695779/200000000 : ℝ)|=(103695779/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118281733/200000000 : ℝ)|^4443 ≤ (25266053705089/50000000000000 : ℝ)^3419
        have hw : |(118281733/200000000 : ℝ)|=(118281733/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1274870509/10000000000 : ℝ)|^4443 ≤ (6879401848983/100000000000000 : ℝ)^3419
        have hw : |(-1274870509/10000000000 : ℝ)|=(1274870509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s0_7 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4164362769/10000000000 : ℝ)*x 0 + (683311969/1250000000 : ℝ)*x 1 + (1578256733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164362769/10000000000 : ℝ)^4443 ≤ (32033344931079/100000000000000 : ℝ)^3419 := by
    have hnat : (4164362769 : ℕ)^4443*100000000000000^3419 ≤ 32033344931079^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164362769 10000000000 32033344931079 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683311969/1250000000 : ℝ)^4443 ≤ (4561966965799/10000000000000 : ℝ)^3419 := by
    have hnat : (683311969 : ℕ)^4443*10000000000000^3419 ≤ 4561966965799^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683311969 1250000000 4561966965799 10000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1578256733/5000000000 : ℝ)^4443 ≤ (22346985387573/100000000000000 : ℝ)^3419 := by
    have hnat : (1578256733 : ℕ)^4443*100000000000000^3419 ≤ 22346985387573^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578256733 5000000000 22346985387573 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164362769/10000000000 : ℝ), (683311969/1250000000 : ℝ), (1578256733/5000000000 : ℝ)] ![(32033344931079/100000000000000 : ℝ), (4561966965799/10000000000000 : ℝ), (22346985387573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164362769/10000000000 : ℝ)|^4443 ≤ (32033344931079/100000000000000 : ℝ)^3419
        have hw : |(4164362769/10000000000 : ℝ)|=(4164362769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683311969/1250000000 : ℝ)|^4443 ≤ (4561966965799/10000000000000 : ℝ)^3419
        have hw : |(683311969/1250000000 : ℝ)|=(683311969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1578256733/5000000000 : ℝ)|^4443 ≤ (22346985387573/100000000000000 : ℝ)^3419
        have hw : |(1578256733/5000000000 : ℝ)|=(1578256733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1473_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25999/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4441/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4441 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4441*1^1024 ≤ 0^1024*1^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4441/1024 : ℝ) ≤ (940022794094588793/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4441 ≤ (940022794094588793/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4441*50000000000000000000^1024 ≤ 940022794094588793^1024*5^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 940022794094588793 50000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (940022794094588793/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4441 := by
      have hnat : (1 : ℕ)^1024*1^4441 ≤ 1^4441*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50940022794094588793/50000000000000000000 : ℝ) ≤ (10043039740591819/10000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (50940022794094588793/50000000000000000000 : ℝ)^1024 ≤ (10043039740591819/10000000000000000 : ℝ)^4441 := by
      have hnat : (50940022794094588793 : ℕ)^1024*10000000000000000^4441 ≤ 10043039740591819^4441*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50940022794094588793 50000000000000000000 10043039740591819 10000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10043039740591819/10000000000000000 : ℝ)) (X := (50940022794094588793/50000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25940022794094588793/25000000000000000000 : ℝ) ≤ (5043039740591819/5000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (25940022794094588793/25000000000000000000 : ℝ)^1024 ≤ (5043039740591819/5000000000000000 : ℝ)^4441 := by
      have hnat : (25940022794094588793 : ℕ)^1024*5000000000000000^4441 ≤ 5043039740591819^4441*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25940022794094588793 25000000000000000000 5043039740591819 5000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5043039740591819/5000000000000000 : ℝ)) (X := (25940022794094588793/25000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(43039740591819/4000000000000000 : ℝ)*(0 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(43039740591819/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(940022794094588793/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(43039740591819/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4441/1024 : ℝ) := by
    rw [show (1 : ℝ)+(43039740591819/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10043039740591819/10000000000000000 : ℝ) by norm_num, show 1+(940022794094588793/50000000000000000000 : ℝ)+(0 : ℝ)=(50940022794094588793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(940022794094588793/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(43039740591819/4000000000000000 : ℝ)*(2/5 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(43039740591819/4000000000000000 : ℝ)*(2/5 : ℝ)=(5043039740591819/5000000000000000 : ℝ) by norm_num, show 1+2*(940022794094588793/50000000000000000000 : ℝ)=(25940022794094588793/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(43039740591819/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43039740591819/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(43039740591819/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43039740591819/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(43039740591819/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43039740591819/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1727991477/10000000000 : ℝ)*X 0 0+(1188699001/2000000000 : ℝ)*X 0 1+(1209571029/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((685814257/1250000000 : ℝ)*X 1 0+(-470134587/2000000000 : ℝ)*X 1 1+(96765681/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5486514187/10000000000 : ℝ)*X 2 0+(4838283883/10000000000 : ℝ)*X 2 1+(-2350672973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4155832357/10000000000 : ℝ)*X 0 0+(3091655943/10000000000 : ℝ)*X 0 1+(5529100011/10000000000 : ℝ)*X 0 2+(4155832357/10000000000 : ℝ)*X 1 0+(3091655943/10000000000 : ℝ)*X 1 1+(5529100011/10000000000 : ℝ)*X 1 2+(4155832357/10000000000 : ℝ)*X 2 0+(3091655943/10000000000 : ℝ)*X 2 1+(5529100011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-173185969/1000000000 : ℝ)*X 0 0+(4866670733/10000000000 : ℝ)*X 0 1+(5914086667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5184789009/10000000000 : ℝ)*X 1 0+(-254974039/2000000000 : ℝ)*X 1 1+(739260849/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((103695779/200000000 : ℝ)*X 2 0+(118281733/200000000 : ℝ)*X 2 1+(-1274870509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4164362769/10000000000 : ℝ)*X 0 0+(683311969/1250000000 : ℝ)*X 0 1+(1578256733/5000000000 : ℝ)*X 0 2+(4164362769/10000000000 : ℝ)*X 1 0+(683311969/1250000000 : ℝ)*X 1 1+(1578256733/5000000000 : ℝ)*X 1 2+(4164362769/10000000000 : ℝ)*X 2 0+(683311969/1250000000 : ℝ)*X 2 1+(1578256733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (892910050492015275188637/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117405443/100000000000000 : ℝ)*(base1) + (63487743/6250000000000 : ℝ)*(base19) + (207481557/20000000000000 : ℝ)*(base23) + (114924923/100000000000000 : ℝ)*(upper3) + (27765017/25000000000000 : ℝ)*(upper5) + (657539839424259/100000000000000 : ℝ)*(major0) + (657539839424259/100000000000000 : ℝ)*(major1) + (657539839424259/100000000000000 : ℝ)*(major2) + (904807746496107/100000000000000 : ℝ)*(sp0) + (56550614708193/6250000000000 : ℝ)*(sp1) + (904809813727191/100000000000000 : ℝ)*(sp2) + (82053428921693/20000000000000 : ℝ)*(sp3) + (402755539/12500000000000 : ℝ)*(sp4) + (1416881289/100000000000000 : ℝ)*(sp7) + (410268678895197/100000000000000 : ℝ)*(f.failure) + (1767208693623/195312500000 : ℝ)*(f.sum) + (9047300137121/200000000000000000000000000000 : ℝ)*base65 + (963962336062879/400000000000000000000000000000 : ℝ)*base68 + (783098763537121/400000000000000000000000000000 : ℝ)*base69 + (557999215937121/400000000000000000000000000000 : ℝ)*base71 + (234006823062879/200000000000000000000000000000 : ℝ)*base74 + (938189990062879/400000000000000000000000000000 : ℝ)*base76 + (140644900337121/400000000000000000000000000000 : ℝ)*base77 + (375240904862879/400000000000000000000000000000 : ℝ)*base80 + (708236496337121/200000000000000000000000000000 : ℝ)*base81 + (36718029/10000000000000000000000 : ℝ)*base90 + (36718029/10000000000000000000000 : ℝ)*base92 + (36718029/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1422591417777972939599943/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (163466111/10000000000000 : ℝ)*(base19) + (1625819471/100000000000000 : ℝ)*(base23) + (29511491/20000000000000 : ℝ)*(base32) + (61200481/25000000000000 : ℝ)*(upper3) + (1898503/1250000000000 : ℝ)*(upper5) + (693816810587801/100000000000000 : ℝ)*(major0) + (693816810587801/100000000000000 : ℝ)*(major1) + (693816810587801/100000000000000 : ℝ)*(major2) + (4043869059/100000000000000 : ℝ)*(sp1) + (127456971/3125000000000 : ℝ)*(sp2) + (119341233912969/12500000000000 : ℝ)*(sp4) + (477362096386791/50000000000000 : ℝ)*(sp5) + (954724166861209/100000000000000 : ℝ)*(sp6) + (432903365215819/100000000000000 : ℝ)*(sp7) + (216451756386637/50000000000000 : ℝ)*(f.failure) + (119341233912969/12500000000000 : ℝ)*(f.sum) + (81459815600019/200000000000000000000000000000 : ℝ)*base65 + (2357960560200019/400000000000000000000000000000 : ℝ)*base67 + (3538760293399981/400000000000000000000000000000 : ℝ)*base70 + (453398460600019/400000000000000000000000000000 : ℝ)*base71 + (1097978155200019/200000000000000000000000000000 : ℝ)*base73 + (2064974382600019/400000000000000000000000000000 : ℝ)*base75 + (568285328199981/400000000000000000000000000000 : ℝ)*base78 + (133166723799981/400000000000000000000000000000 : ℝ)*base80 + (989743041599981/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (20066109/5000000000000000000000 : ℝ)*base90 + (20066109/5000000000000000000000 : ℝ)*base92 + (20066109/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1473_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25999/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1473_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1473_s1_0 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1892326723/10000000000 : ℝ)*x 0 + (5597864361/10000000000 : ℝ)*x 1 + (2539230177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1892326723/10000000000 : ℝ)^4443 ≤ (11493556952021/100000000000000 : ℝ)^3419 := by
    have hnat : (1892326723 : ℕ)^4443*100000000000000^3419 ≤ 11493556952021^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892326723 10000000000 11493556952021 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5597864361/10000000000 : ℝ)^4443 ≤ (147029470353/312500000000 : ℝ)^3419 := by
    have hnat : (5597864361 : ℕ)^4443*312500000000^3419 ≤ 147029470353^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597864361 10000000000 147029470353 312500000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539230177/5000000000 : ℝ)^4443 ≤ (20728506256417/50000000000000 : ℝ)^3419 := by
    have hnat : (2539230177 : ℕ)^4443*50000000000000^3419 ≤ 20728506256417^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539230177 5000000000 20728506256417 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1892326723/10000000000 : ℝ), (5597864361/10000000000 : ℝ), (2539230177/5000000000 : ℝ)] ![(11493556952021/100000000000000 : ℝ), (147029470353/312500000000 : ℝ), (20728506256417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1892326723/10000000000 : ℝ)|^4443 ≤ (11493556952021/100000000000000 : ℝ)^3419
        have hw : |(-1892326723/10000000000 : ℝ)|=(1892326723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5597864361/10000000000 : ℝ)|^4443 ≤ (147029470353/312500000000 : ℝ)^3419
        have hw : |(5597864361/10000000000 : ℝ)|=(5597864361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539230177/5000000000 : ℝ)|^4443 ≤ (20728506256417/50000000000000 : ℝ)^3419
        have hw : |(2539230177/5000000000 : ℝ)|=(2539230177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s1_1 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696947487/5000000000 : ℝ)*x 0 + (-135452427/625000000 : ℝ)*x 1 + (5078458823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696947487/5000000000 : ℝ)^4443 ≤ (22416950863483/50000000000000 : ℝ)^3419 := by
    have hnat : (2696947487 : ℕ)^4443*50000000000000^3419 ≤ 22416950863483^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696947487 5000000000 22416950863483 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135452427/625000000 : ℝ)^4443 ≤ (548364079253/4000000000000 : ℝ)^3419 := by
    have hnat : (135452427 : ℕ)^4443*4000000000000^3419 ≤ 548364079253^3419*625000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135452427 625000000 548364079253 4000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078458823/10000000000 : ℝ)^4443 ≤ (41456996271627/100000000000000 : ℝ)^3419 := by
    have hnat : (5078458823 : ℕ)^4443*100000000000000^3419 ≤ 41456996271627^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078458823 10000000000 41456996271627 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696947487/5000000000 : ℝ), (-135452427/625000000 : ℝ), (5078458823/10000000000 : ℝ)] ![(22416950863483/50000000000000 : ℝ), (548364079253/4000000000000 : ℝ), (41456996271627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696947487/5000000000 : ℝ)|^4443 ≤ (22416950863483/50000000000000 : ℝ)^3419
        have hw : |(2696947487/5000000000 : ℝ)|=(2696947487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135452427/625000000 : ℝ)|^4443 ≤ (548364079253/4000000000000 : ℝ)^3419
        have hw : |(-135452427/625000000 : ℝ)|=(135452427/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078458823/10000000000 : ℝ)|^4443 ≤ (41456996271627/100000000000000 : ℝ)^3419
        have hw : |(5078458823/10000000000 : ℝ)|=(5078458823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s1_2 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696947079/5000000000 : ℝ)*x 0 + (5078459673/10000000000 : ℝ)*x 1 + (-270904851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696947079/5000000000 : ℝ)^4443 ≤ (44833892912999/100000000000000 : ℝ)^3419 := by
    have hnat : (2696947079 : ℕ)^4443*100000000000000^3419 ≤ 44833892912999^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696947079 5000000000 44833892912999 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5078459673/10000000000 : ℝ)^4443 ≤ (20728502644313/50000000000000 : ℝ)^3419 := by
    have hnat : (5078459673 : ℕ)^4443*50000000000000^3419 ≤ 20728502644313^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078459673 10000000000 20728502644313 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270904851/1250000000 : ℝ)^4443 ≤ (6854550892021/50000000000000 : ℝ)^3419 := by
    have hnat : (270904851 : ℕ)^4443*50000000000000^3419 ≤ 6854550892021^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270904851 1250000000 6854550892021 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696947079/5000000000 : ℝ), (5078459673/10000000000 : ℝ), (-270904851/1250000000 : ℝ)] ![(44833892912999/100000000000000 : ℝ), (20728502644313/50000000000000 : ℝ), (6854550892021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696947079/5000000000 : ℝ)|^4443 ≤ (44833892912999/100000000000000 : ℝ)^3419
        have hw : |(2696947079/5000000000 : ℝ)|=(2696947079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5078459673/10000000000 : ℝ)|^4443 ≤ (20728502644313/50000000000000 : ℝ)^3419
        have hw : |(5078459673/10000000000 : ℝ)|=(5078459673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270904851/1250000000 : ℝ)|^4443 ≤ (6854550892021/50000000000000 : ℝ)^3419
        have hw : |(-270904851/1250000000 : ℝ)|=(270904851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s1_3 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4263806083/10000000000 : ℝ)*x 0 + (1862298063/5000000000 : ℝ)*x 1 + (2435049059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4263806083/10000000000 : ℝ)^4443 ≤ (1032216442059/3125000000000 : ℝ)^3419 := by
    have hnat : (4263806083 : ℕ)^4443*3125000000000^3419 ≤ 1032216442059^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4263806083 10000000000 1032216442059 3125000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1862298063/5000000000 : ℝ)^4443 ≤ (6927175979099/25000000000000 : ℝ)^3419 := by
    have hnat : (1862298063 : ℕ)^4443*25000000000000^3419 ≤ 6927175979099^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862298063 5000000000 6927175979099 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2435049059/5000000000 : ℝ)^4443 ≤ (39260369919631/100000000000000 : ℝ)^3419 := by
    have hnat : (2435049059 : ℕ)^4443*100000000000000^3419 ≤ 39260369919631^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435049059 5000000000 39260369919631 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4263806083/10000000000 : ℝ), (1862298063/5000000000 : ℝ), (2435049059/5000000000 : ℝ)] ![(1032216442059/3125000000000 : ℝ), (6927175979099/25000000000000 : ℝ), (39260369919631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4263806083/10000000000 : ℝ)|^4443 ≤ (1032216442059/3125000000000 : ℝ)^3419
        have hw : |(4263806083/10000000000 : ℝ)|=(4263806083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1862298063/5000000000 : ℝ)|^4443 ≤ (6927175979099/25000000000000 : ℝ)^3419
        have hw : |(1862298063/5000000000 : ℝ)|=(1862298063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2435049059/5000000000 : ℝ)|^4443 ≤ (39260369919631/100000000000000 : ℝ)^3419
        have hw : |(2435049059/5000000000 : ℝ)|=(2435049059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s1_4 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1892713281/10000000000 : ℝ)*x 0 + (2542298847/5000000000 : ℝ)*x 1 + (1397905489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1892713281/10000000000 : ℝ)^4443 ≤ (5748304050777/50000000000000 : ℝ)^3419 := by
    have hnat : (1892713281 : ℕ)^4443*50000000000000^3419 ≤ 5748304050777^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892713281 10000000000 5748304050777 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542298847/5000000000 : ℝ)^4443 ≤ (41522130639651/100000000000000 : ℝ)^3419 := by
    have hnat : (2542298847 : ℕ)^4443*100000000000000^3419 ≤ 41522130639651^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542298847 5000000000 41522130639651 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1397905489/2500000000 : ℝ)^4443 ≤ (46981261249013/100000000000000 : ℝ)^3419 := by
    have hnat : (1397905489 : ℕ)^4443*100000000000000^3419 ≤ 46981261249013^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397905489 2500000000 46981261249013 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1892713281/10000000000 : ℝ), (2542298847/5000000000 : ℝ), (1397905489/2500000000 : ℝ)] ![(5748304050777/50000000000000 : ℝ), (41522130639651/100000000000000 : ℝ), (46981261249013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1892713281/10000000000 : ℝ)|^4443 ≤ (5748304050777/50000000000000 : ℝ)^3419
        have hw : |(-1892713281/10000000000 : ℝ)|=(1892713281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2542298847/5000000000 : ℝ)|^4443 ≤ (41522130639651/100000000000000 : ℝ)^3419
        have hw : |(2542298847/5000000000 : ℝ)|=(2542298847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1397905489/2500000000 : ℝ)|^4443 ≤ (46981261249013/100000000000000 : ℝ)^3419
        have hw : |(1397905489/2500000000 : ℝ)|=(1397905489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s1_5 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257766397/10000000000 : ℝ)*x 0 + (-827038009/5000000000 : ℝ)*x 1 + (5591621979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257766397/10000000000 : ℝ)^4443 ≤ (5421138576699/12500000000000 : ℝ)^3419 := by
    have hnat : (5257766397 : ℕ)^4443*12500000000000^3419 ≤ 5421138576699^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257766397 10000000000 5421138576699 12500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (827038009/5000000000 : ℝ)^4443 ≤ (9649629868927/100000000000000 : ℝ)^3419 := by
    have hnat : (827038009 : ℕ)^4443*100000000000000^3419 ≤ 9649629868927^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827038009 5000000000 9649629868927 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5591621979/10000000000 : ℝ)^4443 ≤ (46981261500139/100000000000000 : ℝ)^3419 := by
    have hnat : (5591621979 : ℕ)^4443*100000000000000^3419 ≤ 46981261500139^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591621979 10000000000 46981261500139 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257766397/10000000000 : ℝ), (-827038009/5000000000 : ℝ), (5591621979/10000000000 : ℝ)] ![(5421138576699/12500000000000 : ℝ), (9649629868927/100000000000000 : ℝ), (46981261500139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257766397/10000000000 : ℝ)|^4443 ≤ (5421138576699/12500000000000 : ℝ)^3419
        have hw : |(5257766397/10000000000 : ℝ)|=(5257766397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-827038009/5000000000 : ℝ)|^4443 ≤ (9649629868927/100000000000000 : ℝ)^3419
        have hw : |(-827038009/5000000000 : ℝ)|=(827038009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5591621979/10000000000 : ℝ)|^4443 ≤ (46981261500139/100000000000000 : ℝ)^3419
        have hw : |(5591621979/10000000000 : ℝ)|=(5591621979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s1_6 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257766447/10000000000 : ℝ)*x 0 + (2795810971/5000000000 : ℝ)*x 1 + (-413519/2500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257766447/10000000000 : ℝ)^4443 ≤ (5421138643693/12500000000000 : ℝ)^3419 := by
    have hnat : (5257766447 : ℕ)^4443*12500000000000^3419 ≤ 5421138643693^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257766447 10000000000 5421138643693 12500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2795810971/5000000000 : ℝ)^4443 ≤ (23490630548077/50000000000000 : ℝ)^3419 := by
    have hnat : (2795810971 : ℕ)^4443*50000000000000^3419 ≤ 23490630548077^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795810971 5000000000 23490630548077 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413519/2500000 : ℝ)^4443 ≤ (9649629732467/100000000000000 : ℝ)^3419 := by
    have hnat : (413519 : ℕ)^4443*100000000000000^3419 ≤ 9649629732467^3419*2500000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413519 2500000 9649629732467 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257766447/10000000000 : ℝ), (2795810971/5000000000 : ℝ), (-413519/2500000 : ℝ)] ![(5421138643693/12500000000000 : ℝ), (23490630548077/50000000000000 : ℝ), (9649629732467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257766447/10000000000 : ℝ)|^4443 ≤ (5421138643693/12500000000000 : ℝ)^3419
        have hw : |(5257766447/10000000000 : ℝ)|=(5257766447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2795810971/5000000000 : ℝ)|^4443 ≤ (23490630548077/50000000000000 : ℝ)^3419
        have hw : |(2795810971/5000000000 : ℝ)|=(2795810971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413519/2500000 : ℝ)|^4443 ≤ (9649629732467/100000000000000 : ℝ)^3419
        have hw : |(-413519/2500000 : ℝ)|=(413519/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s1_7 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4264657587/10000000000 : ℝ)*x 0 + (971312297/2000000000 : ℝ)*x 1 + (1869182169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4264657587/10000000000 : ℝ)^4443 ≤ (33039498501883/100000000000000 : ℝ)^3419 := by
    have hnat : (4264657587 : ℕ)^4443*100000000000000^3419 ≤ 33039498501883^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4264657587 10000000000 33039498501883 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971312297/2000000000 : ℝ)^4443 ≤ (39118619740147/100000000000000 : ℝ)^3419 := by
    have hnat : (971312297 : ℕ)^4443*100000000000000^3419 ≤ 39118619740147^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971312297 2000000000 39118619740147 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1869182169/5000000000 : ℝ)^4443 ≤ (27841881741647/100000000000000 : ℝ)^3419 := by
    have hnat : (1869182169 : ℕ)^4443*100000000000000^3419 ≤ 27841881741647^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869182169 5000000000 27841881741647 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4264657587/10000000000 : ℝ), (971312297/2000000000 : ℝ), (1869182169/5000000000 : ℝ)] ![(33039498501883/100000000000000 : ℝ), (39118619740147/100000000000000 : ℝ), (27841881741647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4264657587/10000000000 : ℝ)|^4443 ≤ (33039498501883/100000000000000 : ℝ)^3419
        have hw : |(4264657587/10000000000 : ℝ)|=(4264657587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(971312297/2000000000 : ℝ)|^4443 ≤ (39118619740147/100000000000000 : ℝ)^3419
        have hw : |(971312297/2000000000 : ℝ)|=(971312297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1869182169/5000000000 : ℝ)|^4443 ≤ (27841881741647/100000000000000 : ℝ)^3419
        have hw : |(1869182169/5000000000 : ℝ)|=(1869182169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1473_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7801/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18781/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2311/100000 : ℝ) ^ (4441/1024 : ℝ) ≤ (8015691137073/100000000000000000000 : ℝ) := by
    have hpowers : (2311/100000 : ℝ)^4441 ≤ (8015691137073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2311 : ℕ)^4441*100000000000000000000^1024 ≤ 8015691137073^1024*100000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2311 100000 8015691137073 100000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2311/100000 : ℝ)) (X := (8015691137073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25999/100000 : ℝ) ^ (4441/1024 : ℝ) ≤ (14510662684448241/5000000000000000000 : ℝ) := by
    have hpowers : (25999/100000 : ℝ)^4441 ≤ (14510662684448241/5000000000000000000 : ℝ)^1024 := by
      have hnat : (25999 : ℕ)^4441*5000000000000000000^1024 ≤ 14510662684448241^1024*100000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25999 100000 14510662684448241 5000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25999/100000 : ℝ)) (X := (14510662684448241/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000008015691137073/50000000000000000000 : ℝ) ≤ (312500011551547/312500000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (50000008015691137073/50000000000000000000 : ℝ)^1024 ≤ (312500011551547/312500000000000 : ℝ)^4441 := by
      have hnat : (50000008015691137073 : ℕ)^1024*312500000000000^4441 ≤ 312500011551547^4441*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000008015691137073 50000000000000000000 312500011551547 312500000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312500011551547/312500000000000 : ℝ)) (X := (50000008015691137073/50000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100290221269380101893/100000000000000000000 : ℝ) ≤ (1000668442545063/1000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (100290221269380101893/100000000000000000000 : ℝ)^1024 ≤ (1000668442545063/1000000000000000 : ℝ)^4441 := by
      have hnat : (100290221269380101893 : ℕ)^1024*1000000000000000^4441 ≤ 1000668442545063^4441*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100290221269380101893 100000000000000000000 1000668442545063 1000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000668442545063/1000000000000000 : ℝ)) (X := (100290221269380101893/100000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2514510662684448241/2500000000000000000 : ℝ) ≤ (2503342120312939/2500000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (2514510662684448241/2500000000000000000 : ℝ)^1024 ≤ (2503342120312939/2500000000000000 : ℝ)^4441 := by
      have hnat : (2514510662684448241 : ℕ)^1024*2500000000000000^4441 ≤ 2503342120312939^4441*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2514510662684448241 2500000000000000000 2503342120312939 2500000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503342120312939/2500000000000000 : ℝ)) (X := (2514510662684448241/2500000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8015691137073/100000000000000000000 : ℝ) ≤ ((11842455752517232319/11844000000000000000 : ℝ)+2*(3342027900563/1184400000000000 : ℝ)*(2311/100000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (11842455752517232319/11844000000000000000 : ℝ)+2*(3342027900563/1184400000000000 : ℝ)*(2311/100000 : ℝ)=(312500011551547/312500000000000 : ℝ) by norm_num, show 1+2*(8015691137073/100000000000000000000 : ℝ)=(50000008015691137073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14510662684448241/5000000000000000000 : ℝ)+(8015691137073/100000000000000000000 : ℝ) ≤ ((11842455752517232319/11844000000000000000 : ℝ)+(3342027900563/1184400000000000 : ℝ)*((25999/100000 : ℝ)+(2311/100000 : ℝ)))^(4441/1024 : ℝ) := by
    rw [show (11842455752517232319/11844000000000000000 : ℝ)+(3342027900563/1184400000000000 : ℝ)*((25999/100000 : ℝ)+(2311/100000 : ℝ))=(1000668442545063/1000000000000000 : ℝ) by norm_num, show 1+(14510662684448241/5000000000000000000 : ℝ)+(8015691137073/100000000000000000000 : ℝ)=(100290221269380101893/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14510662684448241/5000000000000000000 : ℝ) ≤ ((11842455752517232319/11844000000000000000 : ℝ)+2*(3342027900563/1184400000000000 : ℝ)*(25999/100000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (11842455752517232319/11844000000000000000 : ℝ)+2*(3342027900563/1184400000000000 : ℝ)*(25999/100000 : ℝ)=(2503342120312939/2500000000000000 : ℝ) by norm_num, show 1+2*(14510662684448241/5000000000000000000 : ℝ)=(2514510662684448241/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11842455752517232319/11844000000000000000 : ℝ)*(X 1 0+X 2 0)+(3342027900563/1184400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (2311/100000 : ℝ)) (hi := (25999/100000 : ℝ)) (c := (11842455752517232319/11844000000000000000 : ℝ)) (alpha := (3342027900563/1184400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11842455752517232319/11844000000000000000 : ℝ)*(X 0 1+X 2 1)+(3342027900563/1184400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (2311/100000 : ℝ)) (hi := (25999/100000 : ℝ)) (c := (11842455752517232319/11844000000000000000 : ℝ)) (alpha := (3342027900563/1184400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11842455752517232319/11844000000000000000 : ℝ)*(X 0 2+X 1 2)+(3342027900563/1184400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (2311/100000 : ℝ)) (hi := (25999/100000 : ℝ)) (c := (11842455752517232319/11844000000000000000 : ℝ)) (alpha := (3342027900563/1184400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1892326723/10000000000 : ℝ)*X 0 0+(5597864361/10000000000 : ℝ)*X 0 1+(2539230177/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2696947487/5000000000 : ℝ)*X 1 0+(-135452427/625000000 : ℝ)*X 1 1+(5078458823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2696947079/5000000000 : ℝ)*X 2 0+(5078459673/10000000000 : ℝ)*X 2 1+(-270904851/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4263806083/10000000000 : ℝ)*X 0 0+(1862298063/5000000000 : ℝ)*X 0 1+(2435049059/5000000000 : ℝ)*X 0 2+(4263806083/10000000000 : ℝ)*X 1 0+(1862298063/5000000000 : ℝ)*X 1 1+(2435049059/5000000000 : ℝ)*X 1 2+(4263806083/10000000000 : ℝ)*X 2 0+(1862298063/5000000000 : ℝ)*X 2 1+(2435049059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1892713281/10000000000 : ℝ)*X 0 0+(2542298847/5000000000 : ℝ)*X 0 1+(1397905489/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257766397/10000000000 : ℝ)*X 1 0+(-827038009/5000000000 : ℝ)*X 1 1+(5591621979/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257766447/10000000000 : ℝ)*X 2 0+(2795810971/5000000000 : ℝ)*X 2 1+(-413519/2500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4264657587/10000000000 : ℝ)*X 0 0+(971312297/2000000000 : ℝ)*X 0 1+(1869182169/5000000000 : ℝ)*X 0 2+(4264657587/10000000000 : ℝ)*X 1 0+(971312297/2000000000 : ℝ)*X 1 1+(1869182169/5000000000 : ℝ)*X 1 2+(4264657587/10000000000 : ℝ)*X 2 0+(971312297/2000000000 : ℝ)*X 2 1+(1869182169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54564764888547780561597409/6580000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216373269/100000000000000 : ℝ)*(base1) + (1548958267/100000000000000 : ℝ)*(base19) + (1257696253/100000000000000 : ℝ)*(base23) + (185880171/100000000000000 : ℝ)*(upper3) + (3356519/2500000000000 : ℝ)*(upper5) + (139913854790111/10000000000000 : ℝ)*(major0) + (139913854790111/10000000000000 : ℝ)*(major1) + (139913854790111/10000000000000 : ℝ)*(major2) + (962644110562043/50000000000000 : ℝ)*(sp0) + (385057960731621/20000000000000 : ℝ)*(sp1) + (1925290094920119/100000000000000 : ℝ)*(sp2) + (872982478613033/100000000000000 : ℝ)*(sp3) + (669573111/20000000000000 : ℝ)*(sp4) + (2771782293/100000000000000 : ℝ)*(sp7) + (436492733384297/50000000000000 : ℝ)*(f.failure) + (481322838154093/25000000000000 : ℝ)*(f.sum) + (457629197059/5922000000000000000000000000 : ℝ)*base65 + (101852387597032591/118440000000000000000000000000000 : ℝ)*base68 + (244729695059152591/118440000000000000000000000000000 : ℝ)*base70 + (1299651092744272591/118440000000000000000000000000000 : ℝ)*base72 + (24911572942927/5922000000000000000000000000 : ℝ)*base73 + (466579468489192591/118440000000000000000000000000000 : ℝ)*base76 + (823155191754352591/118440000000000000000000000000000 : ℝ)*base78 + (971762430398272591/118440000000000000000000000000000 : ℝ)*base80 + (26026692217021/5922000000000000000000000000 : ℝ)*base81 + (7863271/5000000000000000000000 : ℝ)*base89 + (7863271/5000000000000000000000 : ℝ)*base91 + (7863271/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (305053774911222306053628181/28200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2057758049/100000000000000 : ℝ)*(base19) + (2221747531/100000000000000 : ℝ)*(base23) + (276614619/100000000000000 : ℝ)*(upper3) + (30109411/50000000000000 : ℝ)*(lower4) + (239552521/100000000000000 : ℝ)*(upper5) + (1433294249258831/100000000000000 : ℝ)*(major0) + (1433294249258831/100000000000000 : ℝ)*(major1) + (1433294249258831/100000000000000 : ℝ)*(major2) + (12375385477/100000000000000 : ℝ)*(sp1) + (13561230921/100000000000000 : ℝ)*(sp2) + (1972291392924013/100000000000000 : ℝ)*(sp4) + (1972276959780487/100000000000000 : ℝ)*(sp5) + (1972275609945561/100000000000000 : ℝ)*(sp6) + (894296745009987/100000000000000 : ℝ)*(sp7) + (894296745009987/100000000000000 : ℝ)*(f.failure) + (1972291392924013/100000000000000 : ℝ)*(f.sum) + (54933869659667/59220000000000000000000000000 : ℝ)*base66 + (8238793226206910911/1184400000000000000000000000000000 : ℝ)*base68 + (1272029624061710911/1184400000000000000000000000000000 : ℝ)*base70 + (9322084064618510911/1184400000000000000000000000000000 : ℝ)*base72 + (135996713567447/59220000000000000000000000000 : ℝ)*base74 + (905822519772110911/1184400000000000000000000000000000 : ℝ)*base76 + (8665290853989710911/1184400000000000000000000000000000 : ℝ)*base78 + (4016670486348110911/1184400000000000000000000000000000 : ℝ)*base80 + (49540827183493/59220000000000000000000000000 : ℝ)*base81 + (56912941/10000000000000000000000 : ℝ)*base89 + (56912941/10000000000000000000000 : ℝ)*base91 + (56912941/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1473_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7801/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18781/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1473_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1473_s2_0 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-24021227/125000000 : ℝ)*x 0 + (85492931/156250000 : ℝ)*x 1 + (5185831329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24021227/125000000 : ℝ)^4443 ≤ (366434971973/3125000000000 : ℝ)^3419 := by
    have hnat : (24021227 : ℕ)^4443*3125000000000^3419 ≤ 366434971973^3419*125000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24021227 125000000 366434971973 3125000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85492931/156250000 : ℝ)^4443 ≤ (365395705543/800000000000 : ℝ)^3419 := by
    have hnat : (85492931 : ℕ)^4443*800000000000^3419 ≤ 365395705543^3419*156250000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85492931 156250000 365395705543 800000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185831329/10000000000 : ℝ)^4443 ≤ (8519923539219/20000000000000 : ℝ)^3419 := by
    have hnat : (5185831329 : ℕ)^4443*20000000000000^3419 ≤ 8519923539219^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185831329 10000000000 8519923539219 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24021227/125000000 : ℝ), (85492931/156250000 : ℝ), (5185831329/10000000000 : ℝ)] ![(366434971973/3125000000000 : ℝ), (365395705543/800000000000 : ℝ), (8519923539219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24021227/125000000 : ℝ)|^4443 ≤ (366434971973/3125000000000 : ℝ)^3419
        have hw : |(-24021227/125000000 : ℝ)|=(24021227/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85492931/156250000 : ℝ)|^4443 ≤ (365395705543/800000000000 : ℝ)^3419
        have hw : |(85492931/156250000 : ℝ)|=(85492931/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185831329/10000000000 : ℝ)|^4443 ≤ (8519923539219/20000000000000 : ℝ)^3419
        have hw : |(5185831329/10000000000 : ℝ)|=(5185831329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s2_1 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134055317/250000000 : ℝ)*x 0 + (-2069157169/10000000000 : ℝ)*x 1 + (5185832611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134055317/250000000 : ℝ)^4443 ≤ (44491989066143/100000000000000 : ℝ)^3419 := by
    have hnat : (134055317 : ℕ)^4443*100000000000000^3419 ≤ 44491989066143^3419*250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134055317 250000000 44491989066143 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069157169/10000000000 : ℝ)^4443 ≤ (3227094884159/25000000000000 : ℝ)^3419 := by
    have hnat : (2069157169 : ℕ)^4443*25000000000000^3419 ≤ 3227094884159^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069157169 10000000000 3227094884159 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185832611/10000000000 : ℝ)^4443 ≤ (2129981569067/5000000000000 : ℝ)^3419 := by
    have hnat : (5185832611 : ℕ)^4443*5000000000000^3419 ≤ 2129981569067^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185832611 10000000000 2129981569067 5000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134055317/250000000 : ℝ), (-2069157169/10000000000 : ℝ), (5185832611/10000000000 : ℝ)] ![(44491989066143/100000000000000 : ℝ), (3227094884159/25000000000000 : ℝ), (2129981569067/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134055317/250000000 : ℝ)|^4443 ≤ (44491989066143/100000000000000 : ℝ)^3419
        have hw : |(134055317/250000000 : ℝ)|=(134055317/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069157169/10000000000 : ℝ)|^4443 ≤ (3227094884159/25000000000000 : ℝ)^3419
        have hw : |(-2069157169/10000000000 : ℝ)|=(2069157169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185832611/10000000000 : ℝ)|^4443 ≤ (2129981569067/5000000000000 : ℝ)^3419
        have hw : |(5185832611/10000000000 : ℝ)|=(5185832611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s2_2 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16756917/31250000 : ℝ)*x 0 + (259291601/500000000 : ℝ)*x 1 + (-258644617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16756917/31250000 : ℝ)^4443 ≤ (22245998630379/50000000000000 : ℝ)^3419 := by
    have hnat : (16756917 : ℕ)^4443*50000000000000^3419 ≤ 22245998630379^3419*31250000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16756917 31250000 22245998630379 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259291601/500000000 : ℝ)^4443 ≤ (42599625072463/100000000000000 : ℝ)^3419 := by
    have hnat : (259291601 : ℕ)^4443*100000000000000^3419 ≤ 42599625072463^3419*500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259291601 500000000 42599625072463 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258644617/1250000000 : ℝ)^4443 ≤ (6454188823863/50000000000000 : ℝ)^3419 := by
    have hnat : (258644617 : ℕ)^4443*50000000000000^3419 ≤ 6454188823863^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258644617 1250000000 6454188823863 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16756917/31250000 : ℝ), (259291601/500000000 : ℝ), (-258644617/1250000000 : ℝ)] ![(22245998630379/50000000000000 : ℝ), (42599625072463/100000000000000 : ℝ), (6454188823863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16756917/31250000 : ℝ)|^4443 ≤ (22245998630379/50000000000000 : ℝ)^3419
        have hw : |(16756917/31250000 : ℝ)|=(16756917/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259291601/500000000 : ℝ)|^4443 ≤ (42599625072463/100000000000000 : ℝ)^3419
        have hw : |(259291601/500000000 : ℝ)|=(259291601/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258644617/1250000000 : ℝ)|^4443 ≤ (6454188823863/50000000000000 : ℝ)^3419
        have hw : |(-258644617/1250000000 : ℝ)|=(258644617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s2_3 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4284737459/10000000000 : ℝ)*x 0 + (795965449/2000000000 : ℝ)*x 1 + (4609947837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284737459/10000000000 : ℝ)^4443 ≤ (2077612328477/6250000000000 : ℝ)^3419 := by
    have hnat : (4284737459 : ℕ)^4443*6250000000000^3419 ≤ 2077612328477^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284737459 10000000000 2077612328477 6250000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795965449/2000000000 : ℝ)^4443 ≤ (30201077868057/100000000000000 : ℝ)^3419 := by
    have hnat : (795965449 : ℕ)^4443*100000000000000^3419 ≤ 30201077868057^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795965449 2000000000 30201077868057 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4609947837/10000000000 : ℝ)^4443 ≤ (9139281216811/25000000000000 : ℝ)^3419 := by
    have hnat : (4609947837 : ℕ)^4443*25000000000000^3419 ≤ 9139281216811^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609947837 10000000000 9139281216811 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284737459/10000000000 : ℝ), (795965449/2000000000 : ℝ), (4609947837/10000000000 : ℝ)] ![(2077612328477/6250000000000 : ℝ), (30201077868057/100000000000000 : ℝ), (9139281216811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284737459/10000000000 : ℝ)|^4443 ≤ (2077612328477/6250000000000 : ℝ)^3419
        have hw : |(4284737459/10000000000 : ℝ)|=(4284737459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(795965449/2000000000 : ℝ)|^4443 ≤ (30201077868057/100000000000000 : ℝ)^3419
        have hw : |(795965449/2000000000 : ℝ)|=(795965449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4609947837/10000000000 : ℝ)|^4443 ≤ (9139281216811/25000000000000 : ℝ)^3419
        have hw : |(4609947837/10000000000 : ℝ)|=(4609947837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s2_4 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1921762317/10000000000 : ℝ)*x 0 + (5187698737/10000000000 : ℝ)*x 1 + (5469662839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1921762317/10000000000 : ℝ)^4443 ≤ (5863213915281/50000000000000 : ℝ)^3419 := by
    have hnat : (1921762317 : ℕ)^4443*50000000000000^3419 ≤ 5863213915281^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921762317 10000000000 5863213915281 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187698737/10000000000 : ℝ)^4443 ≤ (2663722074831/6250000000000 : ℝ)^3419 := by
    have hnat : (5187698737 : ℕ)^4443*6250000000000^3419 ≤ 2663722074831^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187698737 10000000000 2663722074831 6250000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469662839/10000000000 : ℝ)^4443 ≤ (9130803793323/20000000000000 : ℝ)^3419 := by
    have hnat : (5469662839 : ℕ)^4443*20000000000000^3419 ≤ 9130803793323^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469662839 10000000000 9130803793323 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1921762317/10000000000 : ℝ), (5187698737/10000000000 : ℝ), (5469662839/10000000000 : ℝ)] ![(5863213915281/50000000000000 : ℝ), (2663722074831/6250000000000 : ℝ), (9130803793323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1921762317/10000000000 : ℝ)|^4443 ≤ (5863213915281/50000000000000 : ℝ)^3419
        have hw : |(-1921762317/10000000000 : ℝ)|=(1921762317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187698737/10000000000 : ℝ)|^4443 ≤ (2663722074831/6250000000000 : ℝ)^3419
        have hw : |(5187698737/10000000000 : ℝ)|=(5187698737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469662839/10000000000 : ℝ)|^4443 ≤ (9130803793323/20000000000000 : ℝ)^3419
        have hw : |(5469662839/10000000000 : ℝ)|=(5469662839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s2_5 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643825451/5000000000 : ℝ)*x 0 + (-892663339/5000000000 : ℝ)*x 1 + (2734831429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643825451/5000000000 : ℝ)^4443 ≤ (43689714506211/100000000000000 : ℝ)^3419 := by
    have hnat : (2643825451 : ℕ)^4443*100000000000000^3419 ≤ 43689714506211^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643825451 5000000000 43689714506211 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (892663339/5000000000 : ℝ)^4443 ≤ (10656266301633/100000000000000 : ℝ)^3419 := by
    have hnat : (892663339 : ℕ)^4443*100000000000000^3419 ≤ 10656266301633^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892663339 5000000000 10656266301633 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734831429/5000000000 : ℝ)^4443 ≤ (45654019172701/100000000000000 : ℝ)^3419 := by
    have hnat : (2734831429 : ℕ)^4443*100000000000000^3419 ≤ 45654019172701^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734831429 5000000000 45654019172701 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643825451/5000000000 : ℝ), (-892663339/5000000000 : ℝ), (2734831429/5000000000 : ℝ)] ![(43689714506211/100000000000000 : ℝ), (10656266301633/100000000000000 : ℝ), (45654019172701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643825451/5000000000 : ℝ)|^4443 ≤ (43689714506211/100000000000000 : ℝ)^3419
        have hw : |(2643825451/5000000000 : ℝ)|=(2643825451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-892663339/5000000000 : ℝ)|^4443 ≤ (10656266301633/100000000000000 : ℝ)^3419
        have hw : |(-892663339/5000000000 : ℝ)|=(892663339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734831429/5000000000 : ℝ)|^4443 ≤ (45654019172701/100000000000000 : ℝ)^3419
        have hw : |(2734831429/5000000000 : ℝ)|=(2734831429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s2_6 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20654887/39062500 : ℝ)*x 0 + (1367415721/2500000000 : ℝ)*x 1 + (-892663203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20654887/39062500 : ℝ)^4443 ≤ (21844858165773/50000000000000 : ℝ)^3419 := by
    have hnat : (20654887 : ℕ)^4443*50000000000000^3419 ≤ 21844858165773^3419*39062500^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20654887 39062500 21844858165773 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367415721/2500000000 : ℝ)^4443 ≤ (22827009727357/50000000000000 : ℝ)^3419 := by
    have hnat : (1367415721 : ℕ)^4443*50000000000000^3419 ≤ 22827009727357^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367415721 2500000000 22827009727357 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (892663203/5000000000 : ℝ)^4443 ≤ (1065626419187/10000000000000 : ℝ)^3419 := by
    have hnat : (892663203 : ℕ)^4443*10000000000000^3419 ≤ 1065626419187^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892663203 5000000000 1065626419187 10000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20654887/39062500 : ℝ), (1367415721/2500000000 : ℝ), (-892663203/5000000000 : ℝ)] ![(21844858165773/50000000000000 : ℝ), (22827009727357/50000000000000 : ℝ), (1065626419187/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20654887/39062500 : ℝ)|^4443 ≤ (21844858165773/50000000000000 : ℝ)^3419
        have hw : |(20654887/39062500 : ℝ)|=(20654887/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367415721/2500000000 : ℝ)|^4443 ≤ (22827009727357/50000000000000 : ℝ)^3419
        have hw : |(1367415721/2500000000 : ℝ)|=(1367415721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-892663203/5000000000 : ℝ)|^4443 ≤ (1065626419187/10000000000000 : ℝ)^3419
        have hw : |(-892663203/5000000000 : ℝ)|=(892663203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s2_7 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (428488039/1000000000 : ℝ)*x 0 + (4605829731/10000000000 : ℝ)*x 1 + (3983983327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428488039/1000000000 : ℝ)^4443 ≤ (8310809565661/25000000000000 : ℝ)^3419 := by
    have hnat : (428488039 : ℕ)^4443*25000000000000^3419 ≤ 8310809565661^3419*1000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428488039 1000000000 8310809565661 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4605829731/10000000000 : ℝ)^4443 ≤ (36514692951393/100000000000000 : ℝ)^3419 := by
    have hnat : (4605829731 : ℕ)^4443*100000000000000^3419 ≤ 36514692951393^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4605829731 10000000000 36514692951393 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983983327/10000000000 : ℝ)^4443 ≤ (30242068766469/100000000000000 : ℝ)^3419 := by
    have hnat : (3983983327 : ℕ)^4443*100000000000000^3419 ≤ 30242068766469^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983983327 10000000000 30242068766469 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428488039/1000000000 : ℝ), (4605829731/10000000000 : ℝ), (3983983327/10000000000 : ℝ)] ![(8310809565661/25000000000000 : ℝ), (36514692951393/100000000000000 : ℝ), (30242068766469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428488039/1000000000 : ℝ)|^4443 ≤ (8310809565661/25000000000000 : ℝ)^3419
        have hw : |(428488039/1000000000 : ℝ)|=(428488039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4605829731/10000000000 : ℝ)|^4443 ≤ (36514692951393/100000000000000 : ℝ)^3419
        have hw : |(4605829731/10000000000 : ℝ)|=(4605829731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983983327/10000000000 : ℝ)|^4443 ≤ (30242068766469/100000000000000 : ℝ)^3419
        have hw : |(3983983327/10000000000 : ℝ)|=(3983983327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1473_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5061/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4041/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7801/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7801/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7801/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7801/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7801/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7801/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7801/100000 : ℝ) ^ (4441/1024 : ℝ) ≤ (9800110632709/625000000000000000 : ℝ) := by
    have hpowers : (7801/100000 : ℝ)^4441 ≤ (9800110632709/625000000000000000 : ℝ)^1024 := by
      have hnat : (7801 : ℕ)^4441*625000000000000000^1024 ≤ 9800110632709^1024*100000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7801 100000 9800110632709 625000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7801/100000 : ℝ)) (X := (9800110632709/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18781/100000 : ℝ) ^ (4441/1024 : ℝ) ≤ (70824003344180351/100000000000000000000 : ℝ) := by
    have hpowers : (18781/100000 : ℝ)^4441 ≤ (70824003344180351/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18781 : ℕ)^4441*100000000000000000000^1024 ≤ 70824003344180351^1024*100000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18781 100000 70824003344180351 100000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18781/100000 : ℝ)) (X := (70824003344180351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (312509800110632709/312500000000000000 : ℝ) ≤ (1000007230942377/1000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (312509800110632709/312500000000000000 : ℝ)^1024 ≤ (1000007230942377/1000000000000000 : ℝ)^4441 := by
      have hnat : (312509800110632709 : ℕ)^1024*1000000000000000^4441 ≤ 1000007230942377^4441*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312509800110632709 312500000000000000 1000007230942377 1000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000007230942377/1000000000000000 : ℝ)) (X := (312509800110632709/312500000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100072392021045413791/100000000000000000000 : ℝ) ≤ (1250208592640533/1250000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (100072392021045413791/100000000000000000000 : ℝ)^1024 ≤ (1250208592640533/1250000000000000 : ℝ)^4441 := by
      have hnat : (100072392021045413791 : ℕ)^1024*1250000000000000^4441 ≤ 1250208592640533^4441*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100072392021045413791 100000000000000000000 1250208592640533 1250000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250208592640533/1250000000000000 : ℝ)) (X := (100072392021045413791/100000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50070824003344180351/50000000000000000000 : ℝ) ≤ (5001632586412379/5000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (50070824003344180351/50000000000000000000 : ℝ)^1024 ≤ (5001632586412379/5000000000000000 : ℝ)^4441 := by
      have hnat : (50070824003344180351 : ℕ)^1024*5000000000000000^4441 ≤ 5001632586412379^4441*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50070824003344180351 50000000000000000000 5001632586412379 5000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001632586412379/5000000000000000 : ℝ)) (X := (50070824003344180351/50000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9800110632709/625000000000000000 : ℝ) ≤ ((27443971607520471803/27450000000000000000 : ℝ)+2*(798215850247/549000000000000 : ℝ)*(7801/100000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (27443971607520471803/27450000000000000000 : ℝ)+2*(798215850247/549000000000000 : ℝ)*(7801/100000 : ℝ)=(1000007230942377/1000000000000000 : ℝ) by norm_num, show 1+2*(9800110632709/625000000000000000 : ℝ)=(312509800110632709/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(70824003344180351/100000000000000000000 : ℝ)+(9800110632709/625000000000000000 : ℝ) ≤ ((27443971607520471803/27450000000000000000 : ℝ)+(798215850247/549000000000000 : ℝ)*((18781/100000 : ℝ)+(7801/100000 : ℝ)))^(4441/1024 : ℝ) := by
    rw [show (27443971607520471803/27450000000000000000 : ℝ)+(798215850247/549000000000000 : ℝ)*((18781/100000 : ℝ)+(7801/100000 : ℝ))=(1250208592640533/1250000000000000 : ℝ) by norm_num, show 1+(70824003344180351/100000000000000000000 : ℝ)+(9800110632709/625000000000000000 : ℝ)=(100072392021045413791/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(70824003344180351/100000000000000000000 : ℝ) ≤ ((27443971607520471803/27450000000000000000 : ℝ)+2*(798215850247/549000000000000 : ℝ)*(18781/100000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (27443971607520471803/27450000000000000000 : ℝ)+2*(798215850247/549000000000000 : ℝ)*(18781/100000 : ℝ)=(5001632586412379/5000000000000000 : ℝ) by norm_num, show 1+2*(70824003344180351/100000000000000000000 : ℝ)=(50070824003344180351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27443971607520471803/27450000000000000000 : ℝ)*(X 1 0+X 2 0)+(798215850247/549000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (7801/100000 : ℝ)) (hi := (18781/100000 : ℝ)) (c := (27443971607520471803/27450000000000000000 : ℝ)) (alpha := (798215850247/549000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27443971607520471803/27450000000000000000 : ℝ)*(X 0 1+X 2 1)+(798215850247/549000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (7801/100000 : ℝ)) (hi := (18781/100000 : ℝ)) (c := (27443971607520471803/27450000000000000000 : ℝ)) (alpha := (798215850247/549000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27443971607520471803/27450000000000000000 : ℝ)*(X 0 2+X 1 2)+(798215850247/549000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (7801/100000 : ℝ)) (hi := (18781/100000 : ℝ)) (c := (27443971607520471803/27450000000000000000 : ℝ)) (alpha := (798215850247/549000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-24021227/125000000 : ℝ)*X 0 0+(85492931/156250000 : ℝ)*X 0 1+(5185831329/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((134055317/250000000 : ℝ)*X 1 0+(-2069157169/10000000000 : ℝ)*X 1 1+(5185832611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((16756917/31250000 : ℝ)*X 2 0+(259291601/500000000 : ℝ)*X 2 1+(-258644617/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4284737459/10000000000 : ℝ)*X 0 0+(795965449/2000000000 : ℝ)*X 0 1+(4609947837/10000000000 : ℝ)*X 0 2+(4284737459/10000000000 : ℝ)*X 1 0+(795965449/2000000000 : ℝ)*X 1 1+(4609947837/10000000000 : ℝ)*X 1 2+(4284737459/10000000000 : ℝ)*X 2 0+(795965449/2000000000 : ℝ)*X 2 1+(4609947837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1921762317/10000000000 : ℝ)*X 0 0+(5187698737/10000000000 : ℝ)*X 0 1+(5469662839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643825451/5000000000 : ℝ)*X 1 0+(-892663339/5000000000 : ℝ)*X 1 1+(2734831429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20654887/39062500 : ℝ)*X 2 0+(1367415721/2500000000 : ℝ)*X 2 1+(-892663203/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((428488039/1000000000 : ℝ)*X 0 0+(4605829731/10000000000 : ℝ)*X 0 1+(3983983327/10000000000 : ℝ)*X 0 2+(428488039/1000000000 : ℝ)*X 1 0+(4605829731/10000000000 : ℝ)*X 1 1+(3983983327/10000000000 : ℝ)*X 1 2+(428488039/1000000000 : ℝ)*X 2 0+(4605829731/10000000000 : ℝ)*X 2 1+(3983983327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (134667713374397141442197587/22875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (450815977/50000000000000 : ℝ)*(base19) + (207987643/20000000000000 : ℝ)*(base23) + (119976637/100000000000000 : ℝ)*(upper3) + (38367799/20000000000000 : ℝ)*(upper4) + (12727683/10000000000000 : ℝ)*(upper5) + (127176030079871/5000000000000 : ℝ)*(major0) + (127176030079871/5000000000000 : ℝ)*(major1) + (127176030079871/5000000000000 : ℝ)*(major2) + (3499997233267929/100000000000000 : ℝ)*(sp0) + (5600037130053/160000000000 : ℝ)*(sp1) + (109375720874277/3125000000000 : ℝ)*(sp2) + (793503235078919/50000000000000 : ℝ)*(sp3) + (537492943/2000000000000 : ℝ)*(sp4) + (5214442407/50000000000000 : ℝ)*(sp7) + (396754224760663/25000000000000 : ℝ)*(f.failure) + (3500024107915079/100000000000000 : ℝ)*(f.sum) + (4855342316083/1372500000000000000000000000 : ℝ)*base66 + (991151615582727413/137250000000000000000000000000000 : ℝ)*base67 + (298558655556477413/137250000000000000000000000000000 : ℝ)*base69 + (393483908600727413/137250000000000000000000000000000 : ℝ)*base71 + (6883703304881/2745000000000000000000000000 : ℝ)*base74 + (370203345272522587/137250000000000000000000000000000 : ℝ)*base76 + (1051621380890727413/137250000000000000000000000000000 : ℝ)*base77 + (275679910543772587/137250000000000000000000000000000 : ℝ)*base80 + (9209420097163/1372500000000000000000000000 : ℝ)*base82 + (4050009/2500000000000000000000 : ℝ)*base89 + (4050009/2500000000000000000000 : ℝ)*base91 + (4050009/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1324227102032707242593/381250000000000000000000000 : ℝ) := by norm_num
    linear_combination (308124983/100000000000000 : ℝ)*(base19) + (256042921/50000000000000 : ℝ)*(base23) + (54088017/100000000000000 : ℝ)*(upper3) + (20992381/100000000000000 : ℝ)*(lower4) + (45900661/50000000000000 : ℝ)*(upper5) + (1288666561649899/50000000000000 : ℝ)*(major0) + (1288666561649899/50000000000000 : ℝ)*(major1) + (1288666561649899/50000000000000 : ℝ)*(major2) + (3249880403/100000000000000 : ℝ)*(sp1) + (212889359/3125000000000 : ℝ)*(sp2) + (709310415751543/20000000000000 : ℝ)*(sp4) + (354654852075233/10000000000000 : ℝ)*(sp5) + (110829523569137/3125000000000 : ℝ)*(sp6) + (804057026031227/50000000000000 : ℝ)*(sp7) + (804057026031227/50000000000000 : ℝ)*(f.failure) + (709310415751543/20000000000000 : ℝ)*(f.sum) + (16220991535357/3431250000000000000000000000 : ℝ)*base65 + (1938216689962552103/1372500000000000000000000000000000 : ℝ)*base68 + (5089214557072447897/1372500000000000000000000000000000 : ℝ)*base69 + (2612632437239947897/1372500000000000000000000000000000 : ℝ)*base71 + (21994172539739/6862500000000000000000000000 : ℝ)*base73 + (25552024292707552103/1372500000000000000000000000000000 : ℝ)*base76 + (8254729225409947897/1372500000000000000000000000000000 : ℝ)*base77 + (8260851035685052103/1372500000000000000000000000000000 : ℝ)*base80 + (42138451712203/13725000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (13753739/5000000000000000000000 : ℝ)*base90 + (13753739/5000000000000000000000 : ℝ)*base92 + (13753739/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1473_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5061/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1473_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1473_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5061/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1473_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1473_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1473_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5061/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1473_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
