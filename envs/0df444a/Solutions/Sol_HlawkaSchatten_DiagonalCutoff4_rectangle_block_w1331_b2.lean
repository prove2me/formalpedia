-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1331_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:29.291216+00:00
-- url     : https://prove2.me/submissions/94054d55-1c17-482a-a8bd-b0d7c64485ab

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
theorem support_rectangle_w1331_s6_0 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026753949/5000000000 : ℝ)*x 0 + (2706646301/5000000000 : ℝ)*x 1 + (2622124273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026753949/5000000000 : ℝ)^4291 ≤ (12502792588361/100000000000000 : ℝ)^3267 := by
    have hnat : (1026753949 : ℕ)^4291*100000000000000^3267 ≤ 12502792588361^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026753949 5000000000 12502792588361 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706646301/5000000000 : ℝ)^4291 ≤ (44659963890601/100000000000000 : ℝ)^3267 := by
    have hnat : (2706646301 : ℕ)^4291*100000000000000^3267 ≤ 44659963890601^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706646301 5000000000 44659963890601 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622124273/5000000000 : ℝ)^4291 ≤ (42837243512403/100000000000000 : ℝ)^3267 := by
    have hnat : (2622124273 : ℕ)^4291*100000000000000^3267 ≤ 42837243512403^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622124273 5000000000 42837243512403 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026753949/5000000000 : ℝ), (2706646301/5000000000 : ℝ), (2622124273/5000000000 : ℝ)] ![(12502792588361/100000000000000 : ℝ), (44659963890601/100000000000000 : ℝ), (42837243512403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026753949/5000000000 : ℝ)|^4291 ≤ (12502792588361/100000000000000 : ℝ)^3267
        have hw : |(-1026753949/5000000000 : ℝ)|=(1026753949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706646301/5000000000 : ℝ)|^4291 ≤ (44659963890601/100000000000000 : ℝ)^3267
        have hw : |(2706646301/5000000000 : ℝ)|=(2706646301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622124273/5000000000 : ℝ)|^4291 ≤ (42837243512403/100000000000000 : ℝ)^3267
        have hw : |(2622124273/5000000000 : ℝ)|=(2622124273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s6_1 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674595049/5000000000 : ℝ)*x 0 + (-427929271/2000000000 : ℝ)*x 1 + (1311061999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674595049/5000000000 : ℝ)^4291 ≤ (10991661533899/25000000000000 : ℝ)^3267 := by
    have hnat : (2674595049 : ℕ)^4291*25000000000000^3267 ≤ 10991661533899^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674595049 5000000000 10991661533899 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427929271/2000000000 : ℝ)^4291 ≤ (13196116237287/100000000000000 : ℝ)^3267 := by
    have hnat : (427929271 : ℕ)^4291*100000000000000^3267 ≤ 13196116237287^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427929271 2000000000 13196116237287 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311061999/2500000000 : ℝ)^4291 ≤ (42837237611611/100000000000000 : ℝ)^3267 := by
    have hnat : (1311061999 : ℕ)^4291*100000000000000^3267 ≤ 42837237611611^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311061999 2500000000 42837237611611 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674595049/5000000000 : ℝ), (-427929271/2000000000 : ℝ), (1311061999/2500000000 : ℝ)] ![(10991661533899/25000000000000 : ℝ), (13196116237287/100000000000000 : ℝ), (42837237611611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674595049/5000000000 : ℝ)|^4291 ≤ (10991661533899/25000000000000 : ℝ)^3267
        have hw : |(2674595049/5000000000 : ℝ)|=(2674595049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427929271/2000000000 : ℝ)|^4291 ≤ (13196116237287/100000000000000 : ℝ)^3267
        have hw : |(-427929271/2000000000 : ℝ)|=(427929271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311061999/2500000000 : ℝ)|^4291 ≤ (42837237611611/100000000000000 : ℝ)^3267
        have hw : |(1311061999/2500000000 : ℝ)|=(1311061999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s6_2 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349189439/10000000000 : ℝ)*x 0 + (524424891/1000000000 : ℝ)*x 1 + (-2139646023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349189439/10000000000 : ℝ)^4291 ≤ (43966639021331/100000000000000 : ℝ)^3267 := by
    have hnat : (5349189439 : ℕ)^4291*100000000000000^3267 ≤ 43966639021331^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349189439 10000000000 43966639021331 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524424891/1000000000 : ℝ)^4291 ≤ (8567449483531/20000000000000 : ℝ)^3267 := by
    have hnat : (524424891 : ℕ)^4291*20000000000000^3267 ≤ 8567449483531^3267*1000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524424891 1000000000 8567449483531 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139646023/10000000000 : ℝ)^4291 ≤ (13196113547911/100000000000000 : ℝ)^3267 := by
    have hnat : (2139646023 : ℕ)^4291*100000000000000^3267 ≤ 13196113547911^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139646023 10000000000 13196113547911 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349189439/10000000000 : ℝ), (524424891/1000000000 : ℝ), (-2139646023/10000000000 : ℝ)] ![(43966639021331/100000000000000 : ℝ), (8567449483531/20000000000000 : ℝ), (13196113547911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349189439/10000000000 : ℝ)|^4291 ≤ (43966639021331/100000000000000 : ℝ)^3267
        have hw : |(5349189439/10000000000 : ℝ)|=(5349189439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524424891/1000000000 : ℝ)|^4291 ≤ (8567449483531/20000000000000 : ℝ)^3267
        have hw : |(524424891/1000000000 : ℝ)|=(524424891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2139646023/10000000000 : ℝ)|^4291 ≤ (13196113547911/100000000000000 : ℝ)^3267
        have hw : |(-2139646023/10000000000 : ℝ)|=(2139646023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s6_3 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135296933/312500000 : ℝ)*x 0 + (4156567627/10000000000 : ℝ)*x 1 + (2254589377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135296933/312500000 : ℝ)^4291 ≤ (16651523821277/50000000000000 : ℝ)^3267 := by
    have hnat : (135296933 : ℕ)^4291*50000000000000^3267 ≤ 16651523821277^3267*312500000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135296933 312500000 16651523821277 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4156567627/10000000000 : ℝ)^4291 ≤ (631338229151/2000000000000 : ℝ)^3267 := by
    have hnat : (4156567627 : ℕ)^4291*2000000000000^3267 ≤ 631338229151^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156567627 10000000000 631338229151 2000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254589377/5000000000 : ℝ)^4291 ≤ (35130040888499/100000000000000 : ℝ)^3267 := by
    have hnat : (2254589377 : ℕ)^4291*100000000000000^3267 ≤ 35130040888499^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254589377 5000000000 35130040888499 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135296933/312500000 : ℝ), (4156567627/10000000000 : ℝ), (2254589377/5000000000 : ℝ)] ![(16651523821277/50000000000000 : ℝ), (631338229151/2000000000000 : ℝ), (35130040888499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135296933/312500000 : ℝ)|^4291 ≤ (16651523821277/50000000000000 : ℝ)^3267
        have hw : |(135296933/312500000 : ℝ)|=(135296933/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4156567627/10000000000 : ℝ)|^4291 ≤ (631338229151/2000000000000 : ℝ)^3267
        have hw : |(4156567627/10000000000 : ℝ)|=(4156567627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254589377/5000000000 : ℝ)|^4291 ≤ (35130040888499/100000000000000 : ℝ)^3267
        have hw : |(2254589377/5000000000 : ℝ)|=(2254589377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s6_4 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026760351/5000000000 : ℝ)*x 0 + (655606609/1250000000 : ℝ)*x 1 + (338292799/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026760351/5000000000 : ℝ)^4291 ≤ (6251447490191/50000000000000 : ℝ)^3267 := by
    have hnat : (1026760351 : ℕ)^4291*50000000000000^3267 ≤ 6251447490191^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026760351 5000000000 6251447490191 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655606609/1250000000 : ℝ)^4291 ≤ (10710931817437/25000000000000 : ℝ)^3267 := by
    have hnat : (655606609 : ℕ)^4291*25000000000000^3267 ≤ 10710931817437^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655606609 1250000000 10710931817437 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338292799/625000000 : ℝ)^4291 ≤ (5581672216547/12500000000000 : ℝ)^3267 := by
    have hnat : (338292799 : ℕ)^4291*12500000000000^3267 ≤ 5581672216547^3267*625000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338292799 625000000 5581672216547 12500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026760351/5000000000 : ℝ), (655606609/1250000000 : ℝ), (338292799/625000000 : ℝ)] ![(6251447490191/50000000000000 : ℝ), (10710931817437/25000000000000 : ℝ), (5581672216547/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026760351/5000000000 : ℝ)|^4291 ≤ (6251447490191/50000000000000 : ℝ)^3267
        have hw : |(-1026760351/5000000000 : ℝ)|=(1026760351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655606609/1250000000 : ℝ)|^4291 ≤ (10710931817437/25000000000000 : ℝ)^3267
        have hw : |(655606609/1250000000 : ℝ)|=(655606609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338292799/625000000 : ℝ)|^4291 ≤ (5581672216547/12500000000000 : ℝ)^3267
        have hw : |(338292799/625000000 : ℝ)|=(338292799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s6_5 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652852117/5000000000 : ℝ)*x 0 + (-985604719/5000000000 : ℝ)*x 1 + (541268441/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652852117/5000000000 : ℝ)^4291 ≤ (21748895813537/50000000000000 : ℝ)^3267 := by
    have hnat : (2652852117 : ℕ)^4291*50000000000000^3267 ≤ 21748895813537^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652852117 5000000000 21748895813537 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985604719/5000000000 : ℝ)^4291 ≤ (11848834674959/100000000000000 : ℝ)^3267 := by
    have hnat : (985604719 : ℕ)^4291*100000000000000^3267 ≤ 11848834674959^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985604719 5000000000 11848834674959 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541268441/1000000000 : ℝ)^4291 ≤ (1116334341997/2500000000000 : ℝ)^3267 := by
    have hnat : (541268441 : ℕ)^4291*2500000000000^3267 ≤ 1116334341997^3267*1000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541268441 1000000000 1116334341997 2500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652852117/5000000000 : ℝ), (-985604719/5000000000 : ℝ), (541268441/1000000000 : ℝ)] ![(21748895813537/50000000000000 : ℝ), (11848834674959/100000000000000 : ℝ), (1116334341997/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652852117/5000000000 : ℝ)|^4291 ≤ (21748895813537/50000000000000 : ℝ)^3267
        have hw : |(2652852117/5000000000 : ℝ)|=(2652852117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-985604719/5000000000 : ℝ)|^4291 ≤ (11848834674959/100000000000000 : ℝ)^3267
        have hw : |(-985604719/5000000000 : ℝ)|=(985604719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541268441/1000000000 : ℝ)|^4291 ≤ (1116334341997/2500000000000 : ℝ)^3267
        have hw : |(541268441/1000000000 : ℝ)|=(541268441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s6_6 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305703921/10000000000 : ℝ)*x 0 + (5412684351/10000000000 : ℝ)*x 1 + (-985604973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305703921/10000000000 : ℝ)^4291 ≤ (21748894128351/50000000000000 : ℝ)^3267 := by
    have hnat : (5305703921 : ℕ)^4291*50000000000000^3267 ≤ 21748894128351^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305703921 10000000000 21748894128351 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412684351/10000000000 : ℝ)^4291 ≤ (44653373040583/100000000000000 : ℝ)^3267 := by
    have hnat : (5412684351 : ℕ)^4291*100000000000000^3267 ≤ 44653373040583^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412684351 10000000000 44653373040583 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985604973/5000000000 : ℝ)^4291 ≤ (592441934281/5000000000000 : ℝ)^3267 := by
    have hnat : (985604973 : ℕ)^4291*5000000000000^3267 ≤ 592441934281^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985604973 5000000000 592441934281 5000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305703921/10000000000 : ℝ), (5412684351/10000000000 : ℝ), (-985604973/5000000000 : ℝ)] ![(21748894128351/50000000000000 : ℝ), (44653373040583/100000000000000 : ℝ), (592441934281/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305703921/10000000000 : ℝ)|^4291 ≤ (21748894128351/50000000000000 : ℝ)^3267
        have hw : |(5305703921/10000000000 : ℝ)|=(5305703921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412684351/10000000000 : ℝ)|^4291 ≤ (44653373040583/100000000000000 : ℝ)^3267
        have hw : |(5412684351/10000000000 : ℝ)|=(5412684351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-985604973/5000000000 : ℝ)|^4291 ≤ (592441934281/5000000000000 : ℝ)^3267
        have hw : |(-985604973/5000000000 : ℝ)|=(985604973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s6_7 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (17318109/40000000 : ℝ)*x 0 + (2253958561/5000000000 : ℝ)*x 1 + (831567207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17318109/40000000 : ℝ)^4291 ≤ (3330330420137/10000000000000 : ℝ)^3267 := by
    have hnat : (17318109 : ℕ)^4291*10000000000000^3267 ≤ 3330330420137^3267*40000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17318109 40000000 3330330420137 10000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253958561/5000000000 : ℝ)^4291 ≤ (351171315427/1000000000000 : ℝ)^3267 := by
    have hnat : (2253958561 : ℕ)^4291*1000000000000^3267 ≤ 351171315427^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253958561 5000000000 351171315427 1000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831567207/2000000000 : ℝ)^4291 ≤ (15789782124671/50000000000000 : ℝ)^3267 := by
    have hnat : (831567207 : ℕ)^4291*50000000000000^3267 ≤ 15789782124671^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831567207 2000000000 15789782124671 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17318109/40000000 : ℝ), (2253958561/5000000000 : ℝ), (831567207/2000000000 : ℝ)] ![(3330330420137/10000000000000 : ℝ), (351171315427/1000000000000 : ℝ), (15789782124671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17318109/40000000 : ℝ)|^4291 ≤ (3330330420137/10000000000000 : ℝ)^3267
        have hw : |(17318109/40000000 : ℝ)|=(17318109/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253958561/5000000000 : ℝ)|^4291 ≤ (351171315427/1000000000000 : ℝ)^3267
        have hw : |(2253958561/5000000000 : ℝ)|=(2253958561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831567207/2000000000 : ℝ)|^4291 ≤ (15789782124671/50000000000000 : ℝ)^3267
        have hw : |(831567207/2000000000 : ℝ)|=(831567207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1331_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5557/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5561/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14701/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5557/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5557/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5557/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5557/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5557/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5557/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5557/50000 : ℝ) ^ (2145/512 : ℝ) ≤ (10062797518421899/100000000000000000000 : ℝ) := by
    have hpowers : (5557/50000 : ℝ)^2145 ≤ (10062797518421899/100000000000000000000 : ℝ)^512 := by
      have hnat : (5557 : ℕ)^2145*100000000000000000000^512 ≤ 10062797518421899^512*50000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5557 50000 10062797518421899 100000000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5557/50000 : ℝ)) (X := (10062797518421899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14709/100000 : ℝ) ^ (2145/512 : ℝ) ≤ (8138954612558007/25000000000000000000 : ℝ) := by
    have hpowers : (14709/100000 : ℝ)^2145 ≤ (8138954612558007/25000000000000000000 : ℝ)^512 := by
      have hnat : (14709 : ℕ)^2145*25000000000000000000^512 ≤ 8138954612558007^512*100000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14709 100000 8138954612558007 25000000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14709/100000 : ℝ)) (X := (8138954612558007/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010062797518421899/50000000000000000000 : ℝ) ≤ (2000096070073227/2000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (50010062797518421899/50000000000000000000 : ℝ)^512 ≤ (2000096070073227/2000000000000000 : ℝ)^2145 := by
      have hnat : (50010062797518421899 : ℕ)^512*2000000000000000^2145 ≤ 2000096070073227^2145*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010062797518421899 50000000000000000000 2000096070073227 2000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000096070073227/2000000000000000 : ℝ)) (X := (50010062797518421899/50000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042618615968653927/100000000000000000000 : ℝ) ≤ (10001017118522523/10000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (100042618615968653927/100000000000000000000 : ℝ)^512 ≤ (10001017118522523/10000000000000000 : ℝ)^2145 := by
      have hnat : (100042618615968653927 : ℕ)^512*10000000000000000^2145 ≤ 10001017118522523^2145*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042618615968653927 100000000000000000000 10001017118522523 10000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001017118522523/10000000000000000 : ℝ)) (X := (100042618615968653927/100000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508138954612558007/12500000000000000000 : ℝ) ≤ (10001553886678911/10000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (12508138954612558007/12500000000000000000 : ℝ)^512 ≤ (10001553886678911/10000000000000000 : ℝ)^2145 := by
      have hnat : (12508138954612558007 : ℕ)^512*10000000000000000^2145 ≤ 10001553886678911^2145*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508138954612558007 12500000000000000000 10001553886678911 10000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001553886678911/10000000000000000 : ℝ)) (X := (12508138954612558007/12500000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10062797518421899/100000000000000000000 : ℝ) ≤ ((35939795576986062861/35950000000000000000 : ℝ)+2*(134192039097/89875000000000 : ℝ)*(5557/50000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (35939795576986062861/35950000000000000000 : ℝ)+2*(134192039097/89875000000000 : ℝ)*(5557/50000 : ℝ)=(2000096070073227/2000000000000000 : ℝ) by norm_num, show 1+2*(10062797518421899/100000000000000000000 : ℝ)=(50010062797518421899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8138954612558007/25000000000000000000 : ℝ)+(10062797518421899/100000000000000000000 : ℝ) ≤ ((35939795576986062861/35950000000000000000 : ℝ)+(134192039097/89875000000000 : ℝ)*((14709/100000 : ℝ)+(5557/50000 : ℝ)))^(2145/512 : ℝ) := by
    rw [show (35939795576986062861/35950000000000000000 : ℝ)+(134192039097/89875000000000 : ℝ)*((14709/100000 : ℝ)+(5557/50000 : ℝ))=(10001017118522523/10000000000000000 : ℝ) by norm_num, show 1+(8138954612558007/25000000000000000000 : ℝ)+(10062797518421899/100000000000000000000 : ℝ)=(100042618615968653927/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8138954612558007/25000000000000000000 : ℝ) ≤ ((35939795576986062861/35950000000000000000 : ℝ)+2*(134192039097/89875000000000 : ℝ)*(14709/100000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (35939795576986062861/35950000000000000000 : ℝ)+2*(134192039097/89875000000000 : ℝ)*(14709/100000 : ℝ)=(10001553886678911/10000000000000000 : ℝ) by norm_num, show 1+2*(8138954612558007/25000000000000000000 : ℝ)=(12508138954612558007/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35939795576986062861/35950000000000000000 : ℝ)*(X 1 0+X 2 0)+(134192039097/89875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (5557/50000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (35939795576986062861/35950000000000000000 : ℝ)) (alpha := (134192039097/89875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35939795576986062861/35950000000000000000 : ℝ)*(X 0 1+X 2 1)+(134192039097/89875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (5557/50000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (35939795576986062861/35950000000000000000 : ℝ)) (alpha := (134192039097/89875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35939795576986062861/35950000000000000000 : ℝ)*(X 0 2+X 1 2)+(134192039097/89875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (5557/50000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (35939795576986062861/35950000000000000000 : ℝ)) (alpha := (134192039097/89875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1026753949/5000000000 : ℝ)*X 0 0+(2706646301/5000000000 : ℝ)*X 0 1+(2622124273/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674595049/5000000000 : ℝ)*X 1 0+(-427929271/2000000000 : ℝ)*X 1 1+(1311061999/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349189439/10000000000 : ℝ)*X 2 0+(524424891/1000000000 : ℝ)*X 2 1+(-2139646023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135296933/312500000 : ℝ)*X 0 0+(4156567627/10000000000 : ℝ)*X 0 1+(2254589377/5000000000 : ℝ)*X 0 2+(135296933/312500000 : ℝ)*X 1 0+(4156567627/10000000000 : ℝ)*X 1 1+(2254589377/5000000000 : ℝ)*X 1 2+(135296933/312500000 : ℝ)*X 2 0+(4156567627/10000000000 : ℝ)*X 2 1+(2254589377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1026760351/5000000000 : ℝ)*X 0 0+(655606609/1250000000 : ℝ)*X 0 1+(338292799/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652852117/5000000000 : ℝ)*X 1 0+(-985604719/5000000000 : ℝ)*X 1 1+(541268441/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305703921/10000000000 : ℝ)*X 2 0+(5412684351/10000000000 : ℝ)*X 2 1+(-985604973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((17318109/40000000 : ℝ)*X 0 0+(2253958561/5000000000 : ℝ)*X 0 1+(831567207/2000000000 : ℝ)*X 0 2+(17318109/40000000 : ℝ)*X 1 0+(2253958561/5000000000 : ℝ)*X 1 1+(831567207/2000000000 : ℝ)*X 1 2+(17318109/40000000 : ℝ)*X 2 0+(2253958561/5000000000 : ℝ)*X 2 1+(831567207/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3785803763692192349813814753/449375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2377812911/100000000000000 : ℝ)*(base19) + (1542557359/100000000000000 : ℝ)*(base23) + (2847487/5000000000000 : ℝ)*(lower2) + (53917457/50000000000000 : ℝ)*(upper3) + (76050391/25000000000000 : ℝ)*(upper5) + (1093966083662003/25000000000000 : ℝ)*(major0) + (1093966083662003/25000000000000 : ℝ)*(major1) + (1093966083662003/25000000000000 : ℝ)*(major2) + (118313112681927/2000000000000 : ℝ)*(sp0) + (2957847337182937/50000000000000 : ℝ)*(sp1) + (2957847754810713/50000000000000 : ℝ)*(sp2) + (44312669012477/1562500000000 : ℝ)*(sp3) + (20709041217/50000000000000 : ℝ)*(sp4) + (512987469/2500000000000 : ℝ)*(sp7) + (354503917037161/12500000000000 : ℝ)*(f.failure) + (1183139410435757/20000000000000 : ℝ)*(f.sum) + (4457260346793/2246875000000000000000000000 : ℝ)*base66 + (21778964092606570583/898750000000000000000000000000000 : ℝ)*base67 + (13019650296936570583/898750000000000000000000000000000 : ℝ)*base69 + (3016552414576570583/898750000000000000000000000000000 : ℝ)*base71 + (4176173752653/8987500000000000000000000000 : ℝ)*base73 + (1502710860171570583/898750000000000000000000000000000 : ℝ)*base75 + (14504910244229070583/898750000000000000000000000000000 : ℝ)*base77 + (12157582447446570583/898750000000000000000000000000000 : ℝ)*base79 + (2636975051747/8987500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3136891/250000000000000000000 : ℝ)*base90 + (3136891/250000000000000000000 : ℝ)*base92 + (3136891/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (581546947206168976481825301/112343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3192608403/100000000000000 : ℝ)*(base19) + (3375418139/100000000000000 : ℝ)*(base23) + (340614571/100000000000000 : ℝ)*(upper2) + (38619263/25000000000000 : ℝ)*(upper3) + (359055607/100000000000000 : ℝ)*(upper5) + (550925789233097/12500000000000 : ℝ)*(major0) + (550925789233097/12500000000000 : ℝ)*(major1) + (550925789233097/12500000000000 : ℝ)*(major2) + (12909694433/20000000000000 : ℝ)*(sp1) + (10282474571/20000000000000 : ℝ)*(sp2) + (5958338519517677/100000000000000 : ℝ)*(sp4) + (595827077843711/10000000000000 : ℝ)*(sp5) + (1489570932931671/25000000000000 : ℝ)*(sp6) + (285647393566201/10000000000000 : ℝ)*(sp7) + (285647393566201/10000000000000 : ℝ)*(f.failure) + (5958338519517677/100000000000000 : ℝ)*(f.sum) + (22909296121119/8987500000000000000000000000 : ℝ)*base65 + (502586295335189483/449375000000000000000000000000000 : ℝ)*base68 + (1607016829913939483/449375000000000000000000000000000 : ℝ)*base70 + (1169239314493560517/449375000000000000000000000000000 : ℝ)*base71 + (114286100280713/17975000000000000000000000000 : ℝ)*base73 + (846925832518939483/449375000000000000000000000000000 : ℝ)*base76 + (97575952307064483/449375000000000000000000000000000 : ℝ)*base78 + (6692745699716439483/449375000000000000000000000000000 : ℝ)*base80 + (27845347051613/17975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (726869/200000000000000000000 : ℝ)*base89 + (726869/200000000000000000000 : ℝ)*base91 + (726869/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1331_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5557/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5561/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1331_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1331_s7_0 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-128344653/625000000 : ℝ)*x 0 + (169163293/312500000 : ℝ)*x 1 + (5244311561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128344653/625000000 : ℝ)^4291 ≤ (3125711241971/25000000000000 : ℝ)^3267 := by
    have hnat : (128344653 : ℕ)^4291*25000000000000^3267 ≤ 3125711241971^3267*625000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128344653 625000000 3125711241971 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169163293/312500000 : ℝ)^4291 ≤ (22329617717849/50000000000000 : ℝ)^3267 := by
    have hnat : (169163293 : ℕ)^4291*50000000000000^3267 ≤ 22329617717849^3267*312500000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169163293 312500000 22329617717849 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244311561/10000000000 : ℝ)^4291 ≤ (42837919583531/100000000000000 : ℝ)^3267 := by
    have hnat : (5244311561 : ℕ)^4291*100000000000000^3267 ≤ 42837919583531^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244311561 10000000000 42837919583531 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128344653/625000000 : ℝ), (169163293/312500000 : ℝ), (5244311561/10000000000 : ℝ)] ![(3125711241971/25000000000000 : ℝ), (22329617717849/50000000000000 : ℝ), (42837919583531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128344653/625000000 : ℝ)|^4291 ≤ (3125711241971/25000000000000 : ℝ)^3267
        have hw : |(-128344653/625000000 : ℝ)|=(128344653/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169163293/312500000 : ℝ)|^4291 ≤ (22329617717849/50000000000000 : ℝ)^3267
        have hw : |(169163293/312500000 : ℝ)|=(169163293/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244311561/10000000000 : ℝ)|^4291 ≤ (42837919583531/100000000000000 : ℝ)^3267
        have hw : |(5244311561/10000000000 : ℝ)|=(5244311561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s7_1 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349174509/10000000000 : ℝ)*x 0 + (-2139583543/10000000000 : ℝ)*x 1 + (5244311107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349174509/10000000000 : ℝ)^4291 ≤ (21983238921939/50000000000000 : ℝ)^3267 := by
    have hnat : (5349174509 : ℕ)^4291*50000000000000^3267 ≤ 21983238921939^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349174509 10000000000 21983238921939 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2139583543/10000000000 : ℝ)^4291 ≤ (2639121485809/20000000000000 : ℝ)^3267 := by
    have hnat : (2139583543 : ℕ)^4291*20000000000000^3267 ≤ 2639121485809^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139583543 10000000000 2639121485809 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244311107/10000000000 : ℝ)^4291 ≤ (42837914712677/100000000000000 : ℝ)^3267 := by
    have hnat : (5244311107 : ℕ)^4291*100000000000000^3267 ≤ 42837914712677^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244311107 10000000000 42837914712677 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349174509/10000000000 : ℝ), (-2139583543/10000000000 : ℝ), (5244311107/10000000000 : ℝ)] ![(21983238921939/50000000000000 : ℝ), (2639121485809/20000000000000 : ℝ), (42837914712677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349174509/10000000000 : ℝ)|^4291 ≤ (21983238921939/50000000000000 : ℝ)^3267
        have hw : |(5349174509/10000000000 : ℝ)|=(5349174509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2139583543/10000000000 : ℝ)|^4291 ≤ (2639121485809/20000000000000 : ℝ)^3267
        have hw : |(-2139583543/10000000000 : ℝ)|=(2139583543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244311107/10000000000 : ℝ)|^4291 ≤ (42837914712677/100000000000000 : ℝ)^3267
        have hw : |(5244311107/10000000000 : ℝ)|=(5244311107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s7_2 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349172637/10000000000 : ℝ)*x 0 + (1048862301/2000000000 : ℝ)*x 1 + (-2139585511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349172637/10000000000 : ℝ)^4291 ≤ (5495807204329/12500000000000 : ℝ)^3267 := by
    have hnat : (5349172637 : ℕ)^4291*12500000000000^3267 ≤ 5495807204329^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349172637 10000000000 5495807204329 12500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048862301/2000000000 : ℝ)^4291 ≤ (133868496821/312500000000 : ℝ)^3267 := by
    have hnat : (1048862301 : ℕ)^4291*312500000000^3267 ≤ 133868496821^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048862301 2000000000 133868496821 312500000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139585511/10000000000 : ℝ)^4291 ≤ (6597811685373/50000000000000 : ℝ)^3267 := by
    have hnat : (2139585511 : ℕ)^4291*50000000000000^3267 ≤ 6597811685373^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139585511 10000000000 6597811685373 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349172637/10000000000 : ℝ), (1048862301/2000000000 : ℝ), (-2139585511/10000000000 : ℝ)] ![(5495807204329/12500000000000 : ℝ), (133868496821/312500000000 : ℝ), (6597811685373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349172637/10000000000 : ℝ)|^4291 ≤ (5495807204329/12500000000000 : ℝ)^3267
        have hw : |(5349172637/10000000000 : ℝ)|=(5349172637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048862301/2000000000 : ℝ)|^4291 ≤ (133868496821/312500000000 : ℝ)^3267
        have hw : |(1048862301/2000000000 : ℝ)|=(1048862301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2139585511/10000000000 : ℝ)|^4291 ≤ (6597811685373/50000000000000 : ℝ)^3267
        have hw : |(-2139585511/10000000000 : ℝ)|=(2139585511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s7_3 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541188161/1250000000 : ℝ)*x 0 + (1039175789/2500000000 : ℝ)*x 1 + (18036173/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541188161/1250000000 : ℝ)^4291 ≤ (1665154115823/5000000000000 : ℝ)^3267 := by
    have hnat : (541188161 : ℕ)^4291*5000000000000^3267 ≤ 1665154115823^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541188161 1250000000 1665154115823 5000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039175789/2500000000 : ℝ)^4291 ≤ (1262730533867/4000000000000 : ℝ)^3267 := by
    have hnat : (1039175789 : ℕ)^4291*4000000000000^3267 ≤ 1262730533867^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039175789 2500000000 1262730533867 4000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18036173/40000000 : ℝ)^4291 ≤ (17564327161079/50000000000000 : ℝ)^3267 := by
    have hnat : (18036173 : ℕ)^4291*50000000000000^3267 ≤ 17564327161079^3267*40000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18036173 40000000 17564327161079 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541188161/1250000000 : ℝ), (1039175789/2500000000 : ℝ), (18036173/40000000 : ℝ)] ![(1665154115823/5000000000000 : ℝ), (1262730533867/4000000000000 : ℝ), (17564327161079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541188161/1250000000 : ℝ)|^4291 ≤ (1665154115823/5000000000000 : ℝ)^3267
        have hw : |(541188161/1250000000 : ℝ)|=(541188161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039175789/2500000000 : ℝ)|^4291 ≤ (1262730533867/4000000000000 : ℝ)^3267
        have hw : |(1039175789/2500000000 : ℝ)|=(1039175789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18036173/40000000 : ℝ)|^4291 ≤ (17564327161079/50000000000000 : ℝ)^3267
        have hw : |(18036173/40000000 : ℝ)|=(18036173/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s7_4 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-256690827/1250000000 : ℝ)*x 0 + (5244915431/10000000000 : ℝ)*x 1 + (216504739/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256690827/1250000000 : ℝ)^4291 ≤ (2500588454797/20000000000000 : ℝ)^3267 := by
    have hnat : (256690827 : ℕ)^4291*20000000000000^3267 ≤ 2500588454797^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256690827 1250000000 2500588454797 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244915431/10000000000 : ℝ)^4291 ≤ (8568879694561/20000000000000 : ℝ)^3267 := by
    have hnat : (5244915431 : ℕ)^4291*20000000000000^3267 ≤ 8568879694561^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244915431 10000000000 8568879694561 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216504739/400000000 : ℝ)^4291 ≤ (44652659239271/100000000000000 : ℝ)^3267 := by
    have hnat : (216504739 : ℕ)^4291*100000000000000^3267 ≤ 44652659239271^3267*400000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216504739 400000000 44652659239271 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256690827/1250000000 : ℝ), (5244915431/10000000000 : ℝ), (216504739/400000000 : ℝ)] ![(2500588454797/20000000000000 : ℝ), (8568879694561/20000000000000 : ℝ), (44652659239271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256690827/1250000000 : ℝ)|^4291 ≤ (2500588454797/20000000000000 : ℝ)^3267
        have hw : |(-256690827/1250000000 : ℝ)|=(256690827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244915431/10000000000 : ℝ)|^4291 ≤ (8568879694561/20000000000000 : ℝ)^3267
        have hw : |(5244915431/10000000000 : ℝ)|=(5244915431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216504739/400000000 : ℝ)|^4291 ≤ (44652659239271/100000000000000 : ℝ)^3267
        have hw : |(216504739/400000000 : ℝ)|=(216504739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s7_5 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652860143/5000000000 : ℝ)*x 0 + (-1971278119/10000000000 : ℝ)*x 1 + (1082523683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652860143/5000000000 : ℝ)^4291 ≤ (43497964474497/100000000000000 : ℝ)^3267 := by
    have hnat : (2652860143 : ℕ)^4291*100000000000000^3267 ≤ 43497964474497^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652860143 5000000000 43497964474497 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1971278119/10000000000 : ℝ)^4291 ≤ (11849376914559/100000000000000 : ℝ)^3267 := by
    have hnat : (1971278119 : ℕ)^4291*100000000000000^3267 ≤ 11849376914559^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971278119 10000000000 11849376914559 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082523683/2000000000 : ℝ)^4291 ≤ (44652658589141/100000000000000 : ℝ)^3267 := by
    have hnat : (1082523683 : ℕ)^4291*100000000000000^3267 ≤ 44652658589141^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082523683 2000000000 44652658589141 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652860143/5000000000 : ℝ), (-1971278119/10000000000 : ℝ), (1082523683/2000000000 : ℝ)] ![(43497964474497/100000000000000 : ℝ), (11849376914559/100000000000000 : ℝ), (44652658589141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652860143/5000000000 : ℝ)|^4291 ≤ (43497964474497/100000000000000 : ℝ)^3267
        have hw : |(2652860143/5000000000 : ℝ)|=(2652860143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1971278119/10000000000 : ℝ)|^4291 ≤ (11849376914559/100000000000000 : ℝ)^3267
        have hw : |(-1971278119/10000000000 : ℝ)|=(1971278119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082523683/2000000000 : ℝ)|^4291 ≤ (44652658589141/100000000000000 : ℝ)^3267
        have hw : |(1082523683/2000000000 : ℝ)|=(1082523683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s7_6 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305720163/10000000000 : ℝ)*x 0 + (2706309257/5000000000 : ℝ)*x 1 + (-1971278151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305720163/10000000000 : ℝ)^4291 ≤ (43497963150037/100000000000000 : ℝ)^3267 := by
    have hnat : (5305720163 : ℕ)^4291*100000000000000^3267 ≤ 43497963150037^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305720163 10000000000 43497963150037 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706309257/5000000000 : ℝ)^4291 ≤ (1395395614433/3125000000000 : ℝ)^3267 := by
    have hnat : (2706309257 : ℕ)^4291*3125000000000^3267 ≤ 1395395614433^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706309257 5000000000 1395395614433 3125000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1971278151/10000000000 : ℝ)^4291 ≤ (5924688583601/50000000000000 : ℝ)^3267 := by
    have hnat : (1971278151 : ℕ)^4291*50000000000000^3267 ≤ 5924688583601^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971278151 10000000000 5924688583601 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305720163/10000000000 : ℝ), (2706309257/5000000000 : ℝ), (-1971278151/10000000000 : ℝ)] ![(43497963150037/100000000000000 : ℝ), (1395395614433/3125000000000 : ℝ), (5924688583601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305720163/10000000000 : ℝ)|^4291 ≤ (43497963150037/100000000000000 : ℝ)^3267
        have hw : |(5305720163/10000000000 : ℝ)|=(5305720163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706309257/5000000000 : ℝ)|^4291 ≤ (1395395614433/3125000000000 : ℝ)^3267
        have hw : |(2706309257/5000000000 : ℝ)|=(2706309257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1971278151/10000000000 : ℝ)|^4291 ≤ (5924688583601/50000000000000 : ℝ)^3267
        have hw : |(-1971278151/10000000000 : ℝ)|=(1971278151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s7_7 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4329531911/10000000000 : ℝ)*x 0 + (281736403/625000000 : ℝ)*x 1 + (2078984721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329531911/10000000000 : ℝ)^4291 ≤ (16651675646049/50000000000000 : ℝ)^3267 := by
    have hnat : (4329531911 : ℕ)^4291*50000000000000^3267 ≤ 16651675646049^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329531911 10000000000 16651675646049 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281736403/625000000 : ℝ)^4291 ≤ (35115753590293/100000000000000 : ℝ)^3267 := by
    have hnat : (281736403 : ℕ)^4291*100000000000000^3267 ≤ 35115753590293^3267*625000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281736403 625000000 35115753590293 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078984721/5000000000 : ℝ)^4291 ≤ (15790447549437/50000000000000 : ℝ)^3267 := by
    have hnat : (2078984721 : ℕ)^4291*50000000000000^3267 ≤ 15790447549437^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078984721 5000000000 15790447549437 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329531911/10000000000 : ℝ), (281736403/625000000 : ℝ), (2078984721/5000000000 : ℝ)] ![(16651675646049/50000000000000 : ℝ), (35115753590293/100000000000000 : ℝ), (15790447549437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329531911/10000000000 : ℝ)|^4291 ≤ (16651675646049/50000000000000 : ℝ)^3267
        have hw : |(4329531911/10000000000 : ℝ)|=(4329531911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281736403/625000000 : ℝ)|^4291 ≤ (35115753590293/100000000000000 : ℝ)^3267
        have hw : |(281736403/625000000 : ℝ)|=(281736403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2078984721/5000000000 : ℝ)|^4291 ≤ (15790447549437/50000000000000 : ℝ)^3267
        have hw : |(2078984721/5000000000 : ℝ)|=(2078984721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s7_8 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-40820881/10000000000 : ℝ)*x 0 + (737012451/1250000000 : ℝ)*x 1 + (1179230443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40820881/10000000000 : ℝ)^4291 ≤ (72785278137/100000000000000 : ℝ)^3267 := by
    have hnat : (40820881 : ℕ)^4291*100000000000000^3267 ≤ 72785278137^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40820881 10000000000 72785278137 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (737012451/1250000000 : ℝ)^4291 ≤ (49963314593093/100000000000000 : ℝ)^3267 := by
    have hnat : (737012451 : ℕ)^4291*100000000000000^3267 ≤ 49963314593093^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737012451 1250000000 49963314593093 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1179230443/2000000000 : ℝ)^4291 ≤ (49963900110693/100000000000000 : ℝ)^3267 := by
    have hnat : (1179230443 : ℕ)^4291*100000000000000^3267 ≤ 49963900110693^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179230443 2000000000 49963900110693 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40820881/10000000000 : ℝ), (737012451/1250000000 : ℝ), (1179230443/2000000000 : ℝ)] ![(72785278137/100000000000000 : ℝ), (49963314593093/100000000000000 : ℝ), (49963900110693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40820881/10000000000 : ℝ)|^4291 ≤ (72785278137/100000000000000 : ℝ)^3267
        have hw : |(-40820881/10000000000 : ℝ)|=(40820881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(737012451/1250000000 : ℝ)|^4291 ≤ (49963314593093/100000000000000 : ℝ)^3267
        have hw : |(737012451/1250000000 : ℝ)|=(737012451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1179230443/2000000000 : ℝ)|^4291 ≤ (49963900110693/100000000000000 : ℝ)^3267
        have hw : |(1179230443/2000000000 : ℝ)|=(1179230443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s7_9 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1542124099/10000000000 : ℝ)*x 0 + (5509198547/10000000000 : ℝ)*x 1 + (2755183737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1542124099/10000000000 : ℝ)^4291 ≤ (4291563635173/50000000000000 : ℝ)^3267 := by
    have hnat : (1542124099 : ℕ)^4291*50000000000000^3267 ≤ 4291563635173^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542124099 10000000000 4291563635173 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509198547/10000000000 : ℝ)^4291 ≤ (1428189624533/3125000000000 : ℝ)^3267 := by
    have hnat : (5509198547 : ℕ)^4291*3125000000000^3267 ≤ 1428189624533^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509198547 10000000000 1428189624533 3125000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755183737/5000000000 : ℝ)^4291 ≤ (2285740236773/5000000000000 : ℝ)^3267 := by
    have hnat : (2755183737 : ℕ)^4291*5000000000000^3267 ≤ 2285740236773^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755183737 5000000000 2285740236773 5000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1542124099/10000000000 : ℝ), (5509198547/10000000000 : ℝ), (2755183737/5000000000 : ℝ)] ![(4291563635173/50000000000000 : ℝ), (1428189624533/3125000000000 : ℝ), (2285740236773/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1542124099/10000000000 : ℝ)|^4291 ≤ (4291563635173/50000000000000 : ℝ)^3267
        have hw : |(1542124099/10000000000 : ℝ)|=(1542124099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509198547/10000000000 : ℝ)|^4291 ≤ (1428189624533/3125000000000 : ℝ)^3267
        have hw : |(5509198547/10000000000 : ℝ)|=(5509198547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755183737/5000000000 : ℝ)|^4291 ≤ (2285740236773/5000000000000 : ℝ)^3267
        have hw : |(2755183737/5000000000 : ℝ)|=(2755183737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1331_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5561/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2781/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14699/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5561/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5561/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5561/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5561/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5561/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5561/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5561/50000 : ℝ) ^ (2145/512 : ℝ) ≤ (10093177966048137/100000000000000000000 : ℝ) := by
    have hpowers : (5561/50000 : ℝ)^2145 ≤ (10093177966048137/100000000000000000000 : ℝ)^512 := by
      have hnat : (5561 : ℕ)^2145*100000000000000000000^512 ≤ 10093177966048137^512*50000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5561 50000 10093177966048137 100000000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5561/50000 : ℝ)) (X := (10093177966048137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14701/100000 : ℝ) ^ (2145/512 : ℝ) ≤ (16240850873398877/50000000000000000000 : ℝ) := by
    have hpowers : (14701/100000 : ℝ)^2145 ≤ (16240850873398877/50000000000000000000 : ℝ)^512 := by
      have hnat : (14701 : ℕ)^2145*50000000000000000000^512 ≤ 16240850873398877^512*100000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14701 100000 16240850873398877 50000000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14701/100000 : ℝ)) (X := (16240850873398877/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010093177966048137/50000000000000000000 : ℝ) ≤ (5000240900236809/5000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (50010093177966048137/50000000000000000000 : ℝ)^512 ≤ (5000240900236809/5000000000000000 : ℝ)^2145 := by
      have hnat : (50010093177966048137 : ℕ)^512*5000000000000000^2145 ≤ 5000240900236809^2145*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010093177966048137 50000000000000000000 5000240900236809 5000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000240900236809/5000000000000000 : ℝ)) (X := (50010093177966048137/50000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042574879712845891/100000000000000000000 : ℝ) ≤ (2000203214979993/2000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (100042574879712845891/100000000000000000000 : ℝ)^512 ≤ (2000203214979993/2000000000000000 : ℝ)^2145 := by
      have hnat : (100042574879712845891 : ℕ)^512*2000000000000000^2145 ≤ 2000203214979993^2145*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042574879712845891 100000000000000000000 2000203214979993 2000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000203214979993/2000000000000000 : ℝ)) (X := (100042574879712845891/100000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016240850873398877/25000000000000000000 : ℝ) ≤ (1250193793665789/1250000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (25016240850873398877/25000000000000000000 : ℝ)^512 ≤ (1250193793665789/1250000000000000 : ℝ)^2145 := by
      have hnat : (25016240850873398877 : ℕ)^512*1250000000000000^2145 ≤ 1250193793665789^2145*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016240850873398877 25000000000000000000 1250193793665789 1250000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250193793665789/1250000000000000 : ℝ)) (X := (25016240850873398877/25000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10093177966048137/100000000000000000000 : ℝ) ≤ ((5963306660592569359/5965000000000000000 : ℝ)+2*(178091475449/119300000000000 : ℝ)*(5561/50000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (5963306660592569359/5965000000000000000 : ℝ)+2*(178091475449/119300000000000 : ℝ)*(5561/50000 : ℝ)=(5000240900236809/5000000000000000 : ℝ) by norm_num, show 1+2*(10093177966048137/100000000000000000000 : ℝ)=(50010093177966048137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16240850873398877/50000000000000000000 : ℝ)+(10093177966048137/100000000000000000000 : ℝ) ≤ ((5963306660592569359/5965000000000000000 : ℝ)+(178091475449/119300000000000 : ℝ)*((14701/100000 : ℝ)+(5561/50000 : ℝ)))^(2145/512 : ℝ) := by
    rw [show (5963306660592569359/5965000000000000000 : ℝ)+(178091475449/119300000000000 : ℝ)*((14701/100000 : ℝ)+(5561/50000 : ℝ))=(2000203214979993/2000000000000000 : ℝ) by norm_num, show 1+(16240850873398877/50000000000000000000 : ℝ)+(10093177966048137/100000000000000000000 : ℝ)=(100042574879712845891/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16240850873398877/50000000000000000000 : ℝ) ≤ ((5963306660592569359/5965000000000000000 : ℝ)+2*(178091475449/119300000000000 : ℝ)*(14701/100000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (5963306660592569359/5965000000000000000 : ℝ)+2*(178091475449/119300000000000 : ℝ)*(14701/100000 : ℝ)=(1250193793665789/1250000000000000 : ℝ) by norm_num, show 1+2*(16240850873398877/50000000000000000000 : ℝ)=(25016240850873398877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5963306660592569359/5965000000000000000 : ℝ)*(X 1 0+X 2 0)+(178091475449/119300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (5561/50000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (5963306660592569359/5965000000000000000 : ℝ)) (alpha := (178091475449/119300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5963306660592569359/5965000000000000000 : ℝ)*(X 0 1+X 2 1)+(178091475449/119300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (5561/50000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (5963306660592569359/5965000000000000000 : ℝ)) (alpha := (178091475449/119300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5963306660592569359/5965000000000000000 : ℝ)*(X 0 2+X 1 2)+(178091475449/119300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (5561/50000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (5963306660592569359/5965000000000000000 : ℝ)) (alpha := (178091475449/119300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-128344653/625000000 : ℝ)*X 0 0+(169163293/312500000 : ℝ)*X 0 1+(5244311561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349174509/10000000000 : ℝ)*X 1 0+(-2139583543/10000000000 : ℝ)*X 1 1+(5244311107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349172637/10000000000 : ℝ)*X 2 0+(1048862301/2000000000 : ℝ)*X 2 1+(-2139585511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((541188161/1250000000 : ℝ)*X 0 0+(1039175789/2500000000 : ℝ)*X 0 1+(18036173/40000000 : ℝ)*X 0 2+(541188161/1250000000 : ℝ)*X 1 0+(1039175789/2500000000 : ℝ)*X 1 1+(18036173/40000000 : ℝ)*X 1 2+(541188161/1250000000 : ℝ)*X 2 0+(1039175789/2500000000 : ℝ)*X 2 1+(18036173/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-256690827/1250000000 : ℝ)*X 0 0+(5244915431/10000000000 : ℝ)*X 0 1+(216504739/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652860143/5000000000 : ℝ)*X 1 0+(-1971278119/10000000000 : ℝ)*X 1 1+(1082523683/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305720163/10000000000 : ℝ)*X 2 0+(2706309257/5000000000 : ℝ)*X 2 1+(-1971278151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4329531911/10000000000 : ℝ)*X 0 0+(281736403/625000000 : ℝ)*X 0 1+(2078984721/5000000000 : ℝ)*X 0 2+(4329531911/10000000000 : ℝ)*X 1 0+(281736403/625000000 : ℝ)*X 1 1+(2078984721/5000000000 : ℝ)*X 1 2+(4329531911/10000000000 : ℝ)*X 2 0+(281736403/625000000 : ℝ)*X 2 1+(2078984721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-40820881/10000000000 : ℝ)*X 0 0+(737012451/1250000000 : ℝ)*X 0 1+(1179230443/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1542124099/10000000000 : ℝ)*X 0 0+(5509198547/10000000000 : ℝ)*X 0 1+(2755183737/5000000000 : ℝ)*X 0 2+(1542124099/10000000000 : ℝ)*X 1 0+(5509198547/10000000000 : ℝ)*X 1 1+(2755183737/5000000000 : ℝ)*X 1 2+(1542124099/10000000000 : ℝ)*X 2 0+(5509198547/10000000000 : ℝ)*X 2 1+(2755183737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s7_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (404794780859639660778974601/149125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12218167/5000000000000 : ℝ)*(upper2) + (628697469/100000000000000 : ℝ)*(lower3) + (1033936087/100000000000000 : ℝ)*(lower4) + (181124959/50000000000000 : ℝ)*(lower5) + (2189605498045187/50000000000000 : ℝ)*(major0) + (2189605498045187/50000000000000 : ℝ)*(major1) + (2189605498045187/50000000000000 : ℝ)*(major2) + (236808641871631/4000000000000 : ℝ)*(sp0) + (370013848023531/6250000000000 : ℝ)*(sp1) + (5920182437359279/100000000000000 : ℝ)*(sp2) + (141909728780157/5000000000000 : ℝ)*(sp3) + (39131017217/100000000000000 : ℝ)*(sp6) + (719714861/12500000000000 : ℝ)*(sp7) + (5521585721/100000000000000 : ℝ)*(sp8) + (709550083330507/25000000000000 : ℝ)*(f.failure) + (370013848023531/6250000000000 : ℝ)*(f.sum) + (42267679271971/5965000000000000000000000000 : ℝ)*base65 + (4905905393317775133/298250000000000000000000000000000 : ℝ)*base67 + (16787825747362275133/298250000000000000000000000000000 : ℝ)*base69 + (2970217473122224867/298250000000000000000000000000000 : ℝ)*base72 + (8623757203157/2982500000000000000000000000 : ℝ)*base74 + (1737125859005775133/298250000000000000000000000000000 : ℝ)*base75 + (1269718058480275133/298250000000000000000000000000000 : ℝ)*base77 + (267526182018474867/298250000000000000000000000000000 : ℝ)*base80 + (9620461264263/2982500000000000000000000000 : ℝ)*base81 + (4682017/500000000000000000000 : ℝ)*base90 + (4682017/500000000000000000000 : ℝ)*base92 + (4682017/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56841707357748703584219291/9320312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (6718967/10000000000000 : ℝ)*(lower1) + (1212819/625000000000 : ℝ)*(lower3) + (2761713/4000000000000 : ℝ)*(lower4) + (195228533/100000000000000 : ℝ)*(lower5) + (275674531948283/6250000000000 : ℝ)*(major0) + (275674531948283/6250000000000 : ℝ)*(major1) + (275674531948283/6250000000000 : ℝ)*(major2) + (494915439/50000000000000 : ℝ)*(sp2) + (1490728594789291/25000000000000 : ℝ)*(sp4) + (5962916262870089/100000000000000 : ℝ)*(sp5) + (5962915273039211/100000000000000 : ℝ)*(sp6) + (357333406292623/12500000000000 : ℝ)*(sp7) + (75348517/4000000000000 : ℝ)*(sp8) + (326461063/25000000000000 : ℝ)*(sp9) + (714667139046309/25000000000000 : ℝ)*(f.failure) + (5962916262870089/100000000000000 : ℝ)*(f.sum) + (31284476583123/5965000000000000000000000000 : ℝ)*base66 + (1612525629458189403/37281250000000000000000000000000 : ℝ)*base68 + (1358587093910158153/37281250000000000000000000000000 : ℝ)*base70 + (5390641124049998097/37281250000000000000000000000000 : ℝ)*base71 + (7527615138047/5965000000000000000000000000 : ℝ)*base73 + (184831867531408153/37281250000000000000000000000000 : ℝ)*base76 + (207424556307033153/37281250000000000000000000000000 : ℝ)*base78 + (12838370166939403/37281250000000000000000000000000 : ℝ)*base80 + (66393726023067/5965000000000000000000000000 : ℝ)*base81 + (3626321/500000000000000000000 : ℝ)*base89 + (3626321/500000000000000000000 : ℝ)*base91 + (3626321/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1331_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5561/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1331_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1331_box_0 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885380901/10000000000 : ℝ)*x 0 + (5390399081/10000000000 : ℝ)*x 1 + (5390399017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885380901/10000000000 : ℝ)^4291 ≤ (5587944492733/50000000000000 : ℝ)^3267 := by
    have hnat : (1885380901 : ℕ)^4291*50000000000000^3267 ≤ 5587944492733^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885380901 10000000000 5587944492733 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390399081/10000000000 : ℝ)^4291 ≤ (4441205584647/10000000000000 : ℝ)^3267 := by
    have hnat : (5390399081 : ℕ)^4291*10000000000000^3267 ≤ 4441205584647^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390399081 10000000000 4441205584647 10000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390399017/10000000000 : ℝ)^4291 ≤ (44412055153891/100000000000000 : ℝ)^3267 := by
    have hnat : (5390399017 : ℕ)^4291*100000000000000^3267 ≤ 44412055153891^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390399017 10000000000 44412055153891 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885380901/10000000000 : ℝ), (5390399081/10000000000 : ℝ), (5390399017/10000000000 : ℝ)] ![(5587944492733/50000000000000 : ℝ), (4441205584647/10000000000000 : ℝ), (44412055153891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885380901/10000000000 : ℝ)|^4291 ≤ (5587944492733/50000000000000 : ℝ)^3267
        have hw : |(-1885380901/10000000000 : ℝ)|=(1885380901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390399081/10000000000 : ℝ)|^4291 ≤ (4441205584647/10000000000000 : ℝ)^3267
        have hw : |(5390399081/10000000000 : ℝ)|=(5390399081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390399017/10000000000 : ℝ)|^4291 ≤ (44412055153891/100000000000000 : ℝ)^3267
        have hw : |(5390399017/10000000000 : ℝ)|=(5390399017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_1 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321252141/2500000000 : ℝ)*x 0 + (-253714309/1250000000 : ℝ)*x 1 + (2695199553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321252141/2500000000 : ℝ)^4291 ≤ (4327507777067/10000000000000 : ℝ)^3267 := by
    have hnat : (1321252141 : ℕ)^4291*10000000000000^3267 ≤ 4327507777067^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321252141 2500000000 4327507777067 10000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253714309/1250000000 : ℝ)^4291 ≤ (12312866085737/100000000000000 : ℝ)^3267 := by
    have hnat : (253714309 : ℕ)^4291*100000000000000^3267 ≤ 12312866085737^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253714309 1250000000 12312866085737 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695199553/5000000000 : ℝ)^4291 ≤ (2775753507313/6250000000000 : ℝ)^3267 := by
    have hnat : (2695199553 : ℕ)^4291*6250000000000^3267 ≤ 2775753507313^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695199553 5000000000 2775753507313 6250000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321252141/2500000000 : ℝ), (-253714309/1250000000 : ℝ), (2695199553/5000000000 : ℝ)] ![(4327507777067/10000000000000 : ℝ), (12312866085737/100000000000000 : ℝ), (2775753507313/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321252141/2500000000 : ℝ)|^4291 ≤ (4327507777067/10000000000000 : ℝ)^3267
        have hw : |(1321252141/2500000000 : ℝ)|=(1321252141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253714309/1250000000 : ℝ)|^4291 ≤ (12312866085737/100000000000000 : ℝ)^3267
        have hw : |(-253714309/1250000000 : ℝ)|=(253714309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695199553/5000000000 : ℝ)|^4291 ≤ (2775753507313/6250000000000 : ℝ)^3267
        have hw : |(2695199553/5000000000 : ℝ)|=(2695199553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_2 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057001687/2000000000 : ℝ)*x 0 + (5390399197/10000000000 : ℝ)*x 1 + (-507428631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057001687/2000000000 : ℝ)^4291 ≤ (5409384547913/12500000000000 : ℝ)^3267 := by
    have hnat : (1057001687 : ℕ)^4291*12500000000000^3267 ≤ 5409384547913^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057001687 2000000000 5409384547913 12500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390399197/10000000000 : ℝ)^4291 ≤ (44412057101769/100000000000000 : ℝ)^3267 := by
    have hnat : (5390399197 : ℕ)^4291*100000000000000^3267 ≤ 44412057101769^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390399197 10000000000 44412057101769 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507428631/2500000000 : ℝ)^4291 ≤ (6156433250029/50000000000000 : ℝ)^3267 := by
    have hnat : (507428631 : ℕ)^4291*50000000000000^3267 ≤ 6156433250029^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507428631 2500000000 6156433250029 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057001687/2000000000 : ℝ), (5390399197/10000000000 : ℝ), (-507428631/2500000000 : ℝ)] ![(5409384547913/12500000000000 : ℝ), (44412057101769/100000000000000 : ℝ), (6156433250029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057001687/2000000000 : ℝ)|^4291 ≤ (5409384547913/12500000000000 : ℝ)^3267
        have hw : |(1057001687/2000000000 : ℝ)|=(1057001687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390399197/10000000000 : ℝ)|^4291 ≤ (44412057101769/100000000000000 : ℝ)^3267
        have hw : |(5390399197/10000000000 : ℝ)|=(5390399197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-507428631/2500000000 : ℝ)|^4291 ≤ (6156433250029/50000000000000 : ℝ)^3267
        have hw : |(-507428631/2500000000 : ℝ)|=(507428631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_3 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4477956901/10000000000 : ℝ)*x 0 + (532399423/1250000000 : ℝ)*x 1 + (2129597737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4477956901/10000000000 : ℝ)^4291 ≤ (34810904015053/100000000000000 : ℝ)^3267 := by
    have hnat : (4477956901 : ℕ)^4291*100000000000000^3267 ≤ 34810904015053^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477956901 10000000000 34810904015053 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532399423/1250000000 : ℝ)^4291 ≤ (32594547529791/100000000000000 : ℝ)^3267 := by
    have hnat : (532399423 : ℕ)^4291*100000000000000^3267 ≤ 32594547529791^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532399423 1250000000 32594547529791 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129597737/5000000000 : ℝ)^4291 ≤ (16297274217209/50000000000000 : ℝ)^3267 := by
    have hnat : (2129597737 : ℕ)^4291*50000000000000^3267 ≤ 16297274217209^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129597737 5000000000 16297274217209 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4477956901/10000000000 : ℝ), (532399423/1250000000 : ℝ), (2129597737/5000000000 : ℝ)] ![(34810904015053/100000000000000 : ℝ), (32594547529791/100000000000000 : ℝ), (16297274217209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4477956901/10000000000 : ℝ)|^4291 ≤ (34810904015053/100000000000000 : ℝ)^3267
        have hw : |(4477956901/10000000000 : ℝ)|=(4477956901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(532399423/1250000000 : ℝ)|^4291 ≤ (32594547529791/100000000000000 : ℝ)^3267
        have hw : |(532399423/1250000000 : ℝ)|=(532399423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2129597737/5000000000 : ℝ)|^4291 ≤ (16297274217209/50000000000000 : ℝ)^3267
        have hw : |(2129597737/5000000000 : ℝ)|=(2129597737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_4 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2224402249/10000000000 : ℝ)*x 0 + (5264676669/10000000000 : ℝ)*x 1 + (5264676899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2224402249/10000000000 : ℝ)^4291 ≤ (13886908202101/100000000000000 : ℝ)^3267 := by
    have hnat : (2224402249 : ℕ)^4291*100000000000000^3267 ≤ 13886908202101^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224402249 10000000000 13886908202101 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264676669/10000000000 : ℝ)^4291 ≤ (538206808241/1250000000000 : ℝ)^3267 := by
    have hnat : (5264676669 : ℕ)^4291*1250000000000^3267 ≤ 538206808241^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264676669 10000000000 538206808241 1250000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264676899/10000000000 : ℝ)^4291 ≤ (10764136782473/25000000000000 : ℝ)^3267 := by
    have hnat : (5264676899 : ℕ)^4291*25000000000000^3267 ≤ 10764136782473^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264676899 10000000000 10764136782473 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2224402249/10000000000 : ℝ), (5264676669/10000000000 : ℝ), (5264676899/10000000000 : ℝ)] ![(13886908202101/100000000000000 : ℝ), (538206808241/1250000000000 : ℝ), (10764136782473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2224402249/10000000000 : ℝ)|^4291 ≤ (13886908202101/100000000000000 : ℝ)^3267
        have hw : |(-2224402249/10000000000 : ℝ)|=(2224402249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264676669/10000000000 : ℝ)|^4291 ≤ (538206808241/1250000000000 : ℝ)^3267
        have hw : |(5264676669/10000000000 : ℝ)|=(5264676669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264676899/10000000000 : ℝ)|^4291 ≤ (10764136782473/25000000000000 : ℝ)^3267
        have hw : |(5264676899/10000000000 : ℝ)|=(5264676899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_5 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537335463/1000000000 : ℝ)*x 0 + (-2080084851/10000000000 : ℝ)*x 1 + (1052935343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537335463/1000000000 : ℝ)^4291 ≤ (44227699992247/100000000000000 : ℝ)^3267 := by
    have hnat : (537335463 : ℕ)^4291*100000000000000^3267 ≤ 44227699992247^3267*1000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537335463 1000000000 44227699992247 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080084851/10000000000 : ℝ)^4291 ≤ (12715754830257/100000000000000 : ℝ)^3267 := by
    have hnat : (2080084851 : ℕ)^4291*100000000000000^3267 ≤ 12715754830257^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080084851 10000000000 12715754830257 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052935343/2000000000 : ℝ)^4291 ≤ (21528272576701/50000000000000 : ℝ)^3267 := by
    have hnat : (1052935343 : ℕ)^4291*50000000000000^3267 ≤ 21528272576701^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052935343 2000000000 21528272576701 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537335463/1000000000 : ℝ), (-2080084851/10000000000 : ℝ), (1052935343/2000000000 : ℝ)] ![(44227699992247/100000000000000 : ℝ), (12715754830257/100000000000000 : ℝ), (21528272576701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537335463/1000000000 : ℝ)|^4291 ≤ (44227699992247/100000000000000 : ℝ)^3267
        have hw : |(537335463/1000000000 : ℝ)|=(537335463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080084851/10000000000 : ℝ)|^4291 ≤ (12715754830257/100000000000000 : ℝ)^3267
        have hw : |(-2080084851/10000000000 : ℝ)|=(2080084851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052935343/2000000000 : ℝ)|^4291 ≤ (21528272576701/50000000000000 : ℝ)^3267
        have hw : |(1052935343/2000000000 : ℝ)|=(1052935343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_6 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671669339/1250000000 : ℝ)*x 0 + (5264676561/10000000000 : ℝ)*x 1 + (-520021237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671669339/1250000000 : ℝ)^4291 ≤ (44227700878733/100000000000000 : ℝ)^3267 := by
    have hnat : (671669339 : ℕ)^4291*100000000000000^3267 ≤ 44227700878733^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671669339 1250000000 44227700878733 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264676561/10000000000 : ℝ)^4291 ≤ (21528271749583/50000000000000 : ℝ)^3267 := by
    have hnat : (5264676561 : ℕ)^4291*50000000000000^3267 ≤ 21528271749583^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264676561 10000000000 21528271749583 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520021237/2500000000 : ℝ)^4291 ≤ (6357877804543/50000000000000 : ℝ)^3267 := by
    have hnat : (520021237 : ℕ)^4291*50000000000000^3267 ≤ 6357877804543^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520021237 2500000000 6357877804543 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671669339/1250000000 : ℝ), (5264676561/10000000000 : ℝ), (-520021237/2500000000 : ℝ)] ![(44227700878733/100000000000000 : ℝ), (21528271749583/50000000000000 : ℝ), (6357877804543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671669339/1250000000 : ℝ)|^4291 ≤ (44227700878733/100000000000000 : ℝ)^3267
        have hw : |(671669339/1250000000 : ℝ)|=(671669339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264676561/10000000000 : ℝ)|^4291 ≤ (21528271749583/50000000000000 : ℝ)^3267
        have hw : |(5264676561/10000000000 : ℝ)|=(5264676561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520021237/2500000000 : ℝ)|^4291 ≤ (6357877804543/50000000000000 : ℝ)^3267
        have hw : |(-520021237/2500000000 : ℝ)|=(520021237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_7 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045036823/2500000000 : ℝ)*x 0 + (68875723/156250000 : ℝ)*x 1 + (551005783/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045036823/2500000000 : ℝ)^4291 ≤ (3180232404899/10000000000000 : ℝ)^3267 := by
    have hnat : (1045036823 : ℕ)^4291*10000000000000^3267 ≤ 3180232404899^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045036823 2500000000 3180232404899 10000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68875723/156250000 : ℝ)^4291 ≤ (4262354751303/12500000000000 : ℝ)^3267 := by
    have hnat : (68875723 : ℕ)^4291*12500000000000^3267 ≤ 4262354751303^3267*156250000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68875723 156250000 4262354751303 12500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551005783/1250000000 : ℝ)^4291 ≤ (17049418964571/50000000000000 : ℝ)^3267 := by
    have hnat : (551005783 : ℕ)^4291*50000000000000^3267 ≤ 17049418964571^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551005783 1250000000 17049418964571 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045036823/2500000000 : ℝ), (68875723/156250000 : ℝ), (551005783/1250000000 : ℝ)] ![(3180232404899/10000000000000 : ℝ), (4262354751303/12500000000000 : ℝ), (17049418964571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045036823/2500000000 : ℝ)|^4291 ≤ (3180232404899/10000000000000 : ℝ)^3267
        have hw : |(1045036823/2500000000 : ℝ)|=(1045036823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68875723/156250000 : ℝ)|^4291 ≤ (4262354751303/12500000000000 : ℝ)^3267
        have hw : |(68875723/156250000 : ℝ)|=(68875723/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551005783/1250000000 : ℝ)|^4291 ≤ (17049418964571/50000000000000 : ℝ)^3267
        have hw : |(551005783/1250000000 : ℝ)|=(551005783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_8 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-430647583/2000000000 : ℝ)*x 0 + (2589089051/5000000000 : ℝ)*x 1 + (337776443/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430647583/2000000000 : ℝ)^4291 ≤ (3326581135797/25000000000000 : ℝ)^3267 := by
    have hnat : (430647583 : ℕ)^4291*25000000000000^3267 ≤ 3326581135797^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430647583 2000000000 3326581135797 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589089051/5000000000 : ℝ)^4291 ≤ (42129796319299/100000000000000 : ℝ)^3267 := by
    have hnat : (2589089051 : ℕ)^4291*100000000000000^3267 ≤ 42129796319299^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589089051 5000000000 42129796319299 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337776443/625000000 : ℝ)^4291 ≤ (8912775826771/20000000000000 : ℝ)^3267 := by
    have hnat : (337776443 : ℕ)^4291*20000000000000^3267 ≤ 8912775826771^3267*625000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337776443 625000000 8912775826771 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430647583/2000000000 : ℝ), (2589089051/5000000000 : ℝ), (337776443/625000000 : ℝ)] ![(3326581135797/25000000000000 : ℝ), (42129796319299/100000000000000 : ℝ), (8912775826771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430647583/2000000000 : ℝ)|^4291 ≤ (3326581135797/25000000000000 : ℝ)^3267
        have hw : |(-430647583/2000000000 : ℝ)|=(430647583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589089051/5000000000 : ℝ)|^4291 ≤ (42129796319299/100000000000000 : ℝ)^3267
        have hw : |(2589089051/5000000000 : ℝ)|=(2589089051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337776443/625000000 : ℝ)|^4291 ≤ (8912775826771/20000000000000 : ℝ)^3267
        have hw : |(337776443/625000000 : ℝ)|=(337776443/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_9 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275148057/10000000000 : ℝ)*x 0 + (-505990533/2500000000 : ℝ)*x 1 + (2702211829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275148057/10000000000 : ℝ)^4291 ≤ (21584530602953/50000000000000 : ℝ)^3267 := by
    have hnat : (5275148057 : ℕ)^4291*50000000000000^3267 ≤ 21584530602953^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275148057 10000000000 21584530602953 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505990533/2500000000 : ℝ)^4291 ≤ (1226705347147/10000000000000 : ℝ)^3267 := by
    have hnat : (505990533 : ℕ)^4291*10000000000000^3267 ≤ 1226705347147^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505990533 2500000000 1226705347147 10000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702211829/5000000000 : ℝ)^4291 ≤ (22281942653581/50000000000000 : ℝ)^3267 := by
    have hnat : (2702211829 : ℕ)^4291*50000000000000^3267 ≤ 22281942653581^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702211829 5000000000 22281942653581 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275148057/10000000000 : ℝ), (-505990533/2500000000 : ℝ), (2702211829/5000000000 : ℝ)] ![(21584530602953/50000000000000 : ℝ), (1226705347147/10000000000000 : ℝ), (22281942653581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275148057/10000000000 : ℝ)|^4291 ≤ (21584530602953/50000000000000 : ℝ)^3267
        have hw : |(5275148057/10000000000 : ℝ)|=(5275148057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505990533/2500000000 : ℝ)|^4291 ≤ (1226705347147/10000000000000 : ℝ)^3267
        have hw : |(-505990533/2500000000 : ℝ)|=(505990533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702211829/5000000000 : ℝ)|^4291 ≤ (22281942653581/50000000000000 : ℝ)^3267
        have hw : |(2702211829/5000000000 : ℝ)|=(2702211829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_10 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329696787/625000000 : ℝ)*x 0 + (337776447/625000000 : ℝ)*x 1 + (-1011981049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329696787/625000000 : ℝ)^4291 ≤ (21584533478173/50000000000000 : ℝ)^3267 := by
    have hnat : (329696787 : ℕ)^4291*50000000000000^3267 ≤ 21584533478173^3267*625000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329696787 625000000 21584533478173 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337776447/625000000 : ℝ)^4291 ≤ (22281939913499/50000000000000 : ℝ)^3267 := by
    have hnat : (337776447 : ℕ)^4291*50000000000000^3267 ≤ 22281939913499^3267*625000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337776447 625000000 22281939913499 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011981049/5000000000 : ℝ)^4291 ≤ (1533381650101/12500000000000 : ℝ)^3267 := by
    have hnat : (1011981049 : ℕ)^4291*12500000000000^3267 ≤ 1533381650101^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011981049 5000000000 1533381650101 12500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329696787/625000000 : ℝ), (337776447/625000000 : ℝ), (-1011981049/5000000000 : ℝ)] ![(21584533478173/50000000000000 : ℝ), (22281939913499/50000000000000 : ℝ), (1533381650101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329696787/625000000 : ℝ)|^4291 ≤ (21584533478173/50000000000000 : ℝ)^3267
        have hw : |(329696787/625000000 : ℝ)|=(329696787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337776447/625000000 : ℝ)|^4291 ≤ (22281939913499/50000000000000 : ℝ)^3267
        have hw : |(337776447/625000000 : ℝ)|=(337776447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1011981049/5000000000 : ℝ)|^4291 ≤ (1533381650101/12500000000000 : ℝ)^3267
        have hw : |(-1011981049/5000000000 : ℝ)|=(1011981049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_11 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4510617907/10000000000 : ℝ)*x 0 + (530322163/1250000000 : ℝ)*x 1 + (2121288777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4510617907/10000000000 : ℝ)^4291 ≤ (17572384028761/50000000000000 : ℝ)^3267 := by
    have hnat : (4510617907 : ℕ)^4291*50000000000000^3267 ≤ 17572384028761^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510617907 10000000000 17572384028761 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530322163/1250000000 : ℝ)^4291 ≤ (3242761470493/10000000000000 : ℝ)^3267 := by
    have hnat : (530322163 : ℕ)^4291*10000000000000^3267 ≤ 3242761470493^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530322163 1250000000 3242761470493 10000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121288777/5000000000 : ℝ)^4291 ≤ (2026726075919/6250000000000 : ℝ)^3267 := by
    have hnat : (2121288777 : ℕ)^4291*6250000000000^3267 ≤ 2026726075919^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121288777 5000000000 2026726075919 6250000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4510617907/10000000000 : ℝ), (530322163/1250000000 : ℝ), (2121288777/5000000000 : ℝ)] ![(17572384028761/50000000000000 : ℝ), (3242761470493/10000000000000 : ℝ), (2026726075919/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4510617907/10000000000 : ℝ)|^4291 ≤ (17572384028761/50000000000000 : ℝ)^3267
        have hw : |(4510617907/10000000000 : ℝ)|=(4510617907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530322163/1250000000 : ℝ)|^4291 ≤ (3242761470493/10000000000000 : ℝ)^3267
        have hw : |(530322163/1250000000 : ℝ)|=(530322163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121288777/5000000000 : ℝ)|^4291 ≤ (2026726075919/6250000000000 : ℝ)^3267
        have hw : |(2121288777/5000000000 : ℝ)|=(2121288777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_12 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-489226181/2500000000 : ℝ)*x 0 + (5474667239/10000000000 : ℝ)*x 1 + (2626808287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489226181/2500000000 : ℝ)^4291 ≤ (5868013790657/50000000000000 : ℝ)^3267 := by
    have hnat : (489226181 : ℕ)^4291*50000000000000^3267 ≤ 5868013790657^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489226181 2500000000 5868013790657 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474667239/10000000000 : ℝ)^4291 ≤ (22663096941159/50000000000000 : ℝ)^3267 := by
    have hnat : (5474667239 : ℕ)^4291*50000000000000^3267 ≤ 22663096941159^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474667239 10000000000 22663096941159 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626808287/5000000000 : ℝ)^4291 ≤ (8587555704523/20000000000000 : ℝ)^3267 := by
    have hnat : (2626808287 : ℕ)^4291*20000000000000^3267 ≤ 8587555704523^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626808287 5000000000 8587555704523 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489226181/2500000000 : ℝ), (5474667239/10000000000 : ℝ), (2626808287/5000000000 : ℝ)] ![(5868013790657/50000000000000 : ℝ), (22663096941159/50000000000000 : ℝ), (8587555704523/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489226181/2500000000 : ℝ)|^4291 ≤ (5868013790657/50000000000000 : ℝ)^3267
        have hw : |(-489226181/2500000000 : ℝ)|=(489226181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474667239/10000000000 : ℝ)|^4291 ≤ (22663096941159/50000000000000 : ℝ)^3267
        have hw : |(5474667239/10000000000 : ℝ)|=(5474667239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626808287/5000000000 : ℝ)|^4291 ≤ (8587555704523/20000000000000 : ℝ)^3267
        have hw : |(2626808287/5000000000 : ℝ)|=(2626808287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_13 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690562127/5000000000 : ℝ)*x 0 + (-1042205817/5000000000 : ℝ)*x 1 + (1050723313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690562127/5000000000 : ℝ)^4291 ≤ (44311714948233/100000000000000 : ℝ)^3267 := by
    have hnat : (2690562127 : ℕ)^4291*100000000000000^3267 ≤ 44311714948233^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690562127 5000000000 44311714948233 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042205817/5000000000 : ℝ)^4291 ≤ (12750506611911/100000000000000 : ℝ)^3267 := by
    have hnat : (1042205817 : ℕ)^4291*100000000000000^3267 ≤ 12750506611911^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042205817 5000000000 12750506611911 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050723313/2000000000 : ℝ)^4291 ≤ (42937778426003/100000000000000 : ℝ)^3267 := by
    have hnat : (1050723313 : ℕ)^4291*100000000000000^3267 ≤ 42937778426003^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050723313 2000000000 42937778426003 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690562127/5000000000 : ℝ), (-1042205817/5000000000 : ℝ), (1050723313/2000000000 : ℝ)] ![(44311714948233/100000000000000 : ℝ), (12750506611911/100000000000000 : ℝ), (42937778426003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690562127/5000000000 : ℝ)|^4291 ≤ (44311714948233/100000000000000 : ℝ)^3267
        have hw : |(2690562127/5000000000 : ℝ)|=(2690562127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1042205817/5000000000 : ℝ)|^4291 ≤ (12750506611911/100000000000000 : ℝ)^3267
        have hw : |(-1042205817/5000000000 : ℝ)|=(1042205817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050723313/2000000000 : ℝ)|^4291 ≤ (42937778426003/100000000000000 : ℝ)^3267
        have hw : |(1050723313/2000000000 : ℝ)|=(1050723313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_14 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690562403/5000000000 : ℝ)*x 0 + (656702009/1250000000 : ℝ)*x 1 + (-41688231/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690562403/5000000000 : ℝ)^4291 ≤ (44311720918503/100000000000000 : ℝ)^3267 := by
    have hnat : (2690562403 : ℕ)^4291*100000000000000^3267 ≤ 44311720918503^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690562403 5000000000 44311720918503 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656702009/1250000000 : ℝ)^4291 ≤ (10734443283447/25000000000000 : ℝ)^3267 := by
    have hnat : (656702009 : ℕ)^4291*25000000000000^3267 ≤ 10734443283447^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656702009 1250000000 10734443283447 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41688231/200000000 : ℝ)^4291 ≤ (12750505937021/100000000000000 : ℝ)^3267 := by
    have hnat : (41688231 : ℕ)^4291*100000000000000^3267 ≤ 12750505937021^3267*200000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41688231 200000000 12750505937021 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690562403/5000000000 : ℝ), (656702009/1250000000 : ℝ), (-41688231/200000000 : ℝ)] ![(44311720918503/100000000000000 : ℝ), (10734443283447/25000000000000 : ℝ), (12750505937021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690562403/5000000000 : ℝ)|^4291 ≤ (44311720918503/100000000000000 : ℝ)^3267
        have hw : |(2690562403/5000000000 : ℝ)|=(2690562403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656702009/1250000000 : ℝ)|^4291 ≤ (10734443283447/25000000000000 : ℝ)^3267
        have hw : |(656702009/1250000000 : ℝ)|=(656702009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41688231/200000000 : ℝ)|^4291 ≤ (12750505937021/100000000000000 : ℝ)^3267
        have hw : |(-41688231/200000000 : ℝ)|=(41688231/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_box_15 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4153500171/10000000000 : ℝ)*x 0 + (1105282651/2500000000 : ℝ)*x 1 + (4421130957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153500171/10000000000 : ℝ)^4291 ≤ (7884079391489/25000000000000 : ℝ)^3267 := by
    have hnat : (4153500171 : ℕ)^4291*25000000000000^3267 ≤ 7884079391489^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153500171 10000000000 7884079391489 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105282651/2500000000 : ℝ)^4291 ≤ (34231839410877/100000000000000 : ℝ)^3267 := by
    have hnat : (1105282651 : ℕ)^4291*100000000000000^3267 ≤ 34231839410877^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105282651 2500000000 34231839410877 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4421130957/10000000000 : ℝ)^4291 ≤ (17115921500383/50000000000000 : ℝ)^3267 := by
    have hnat : (4421130957 : ℕ)^4291*50000000000000^3267 ≤ 17115921500383^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4421130957 10000000000 17115921500383 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153500171/10000000000 : ℝ), (1105282651/2500000000 : ℝ), (4421130957/10000000000 : ℝ)] ![(7884079391489/25000000000000 : ℝ), (34231839410877/100000000000000 : ℝ), (17115921500383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153500171/10000000000 : ℝ)|^4291 ≤ (7884079391489/25000000000000 : ℝ)^3267
        have hw : |(4153500171/10000000000 : ℝ)|=(4153500171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105282651/2500000000 : ℝ)|^4291 ≤ (34231839410877/100000000000000 : ℝ)^3267
        have hw : |(1105282651/2500000000 : ℝ)|=(1105282651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4421130957/10000000000 : ℝ)|^4291 ≤ (17115921500383/50000000000000 : ℝ)^3267
        have hw : |(4421130957/10000000000 : ℝ)|=(4421130957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1331_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62851/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1473/2500 : ℝ) ∧ (7989/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84309/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2781/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2781/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2781/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2781/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2781/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2781/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2781/25000 : ℝ) ^ (2145/512 : ℝ) ≤ (315649499262639/3125000000000000000 : ℝ) := by
    have hpowers : (2781/25000 : ℝ)^2145 ≤ (315649499262639/3125000000000000000 : ℝ)^512 := by
      have hnat : (2781 : ℕ)^2145*3125000000000000000^512 ≤ 315649499262639^512*25000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2781 25000 315649499262639 3125000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2781/25000 : ℝ)) (X := (315649499262639/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14699/100000 : ℝ) ^ (2145/512 : ℝ) ≤ (3246319265945923/10000000000000000000 : ℝ) := by
    have hpowers : (14699/100000 : ℝ)^2145 ≤ (3246319265945923/10000000000000000000 : ℝ)^512 := by
      have hnat : (14699 : ℕ)^2145*10000000000000000000^512 ≤ 3246319265945923^512*100000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14699 100000 3246319265945923 10000000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14699/100000 : ℝ)) (X := (3246319265945923/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562815649499262639/1562500000000000000 : ℝ) ≤ (1250060270440073/1250000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (1562815649499262639/1562500000000000000 : ℝ)^512 ≤ (1250060270440073/1250000000000000 : ℝ)^2145 := by
      have hnat : (1562815649499262639 : ℕ)^512*1250000000000000^2145 ≤ 1250060270440073^2145*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562815649499262639 1562500000000000000 1250060270440073 1250000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250060270440073/1250000000000000 : ℝ)) (X := (1562815649499262639/1562500000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021281988317931839/50000000000000000000 : ℝ) ≤ (400040632589347/400000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (50021281988317931839/50000000000000000000 : ℝ)^512 ≤ (400040632589347/400000000000000 : ℝ)^2145 := by
      have hnat : (50021281988317931839 : ℕ)^512*400000000000000^2145 ≤ 400040632589347^2145*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021281988317931839 50000000000000000000 400040632589347 400000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400040632589347/400000000000000 : ℝ)) (X := (50021281988317931839/50000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003246319265945923/5000000000000000000 : ℝ) ≤ (5000774732973383/5000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (5003246319265945923/5000000000000000000 : ℝ)^512 ≤ (5000774732973383/5000000000000000 : ℝ)^2145 := by
      have hnat : (5003246319265945923 : ℕ)^512*5000000000000000^2145 ≤ 5000774732973383^2145*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003246319265945923 5000000000000000000 5000774732973383 5000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000774732973383/5000000000000000 : ℝ)) (X := (5003246319265945923/5000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(315649499262639/3125000000000000000 : ℝ) ≤ ((558435172849956863/558593750000000000 : ℝ)+2*(533651213091/357500000000000 : ℝ)*(2781/25000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (558435172849956863/558593750000000000 : ℝ)+2*(533651213091/357500000000000 : ℝ)*(2781/25000 : ℝ)=(1250060270440073/1250000000000000 : ℝ) by norm_num, show 1+2*(315649499262639/3125000000000000000 : ℝ)=(1562815649499262639/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3246319265945923/10000000000000000000 : ℝ)+(315649499262639/3125000000000000000 : ℝ) ≤ ((558435172849956863/558593750000000000 : ℝ)+(533651213091/357500000000000 : ℝ)*((14699/100000 : ℝ)+(2781/25000 : ℝ)))^(2145/512 : ℝ) := by
    rw [show (558435172849956863/558593750000000000 : ℝ)+(533651213091/357500000000000 : ℝ)*((14699/100000 : ℝ)+(2781/25000 : ℝ))=(400040632589347/400000000000000 : ℝ) by norm_num, show 1+(3246319265945923/10000000000000000000 : ℝ)+(315649499262639/3125000000000000000 : ℝ)=(50021281988317931839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3246319265945923/10000000000000000000 : ℝ) ≤ ((558435172849956863/558593750000000000 : ℝ)+2*(533651213091/357500000000000 : ℝ)*(14699/100000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (558435172849956863/558593750000000000 : ℝ)+2*(533651213091/357500000000000 : ℝ)*(14699/100000 : ℝ)=(5000774732973383/5000000000000000 : ℝ) by norm_num, show 1+2*(3246319265945923/10000000000000000000 : ℝ)=(5003246319265945923/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (558435172849956863/558593750000000000 : ℝ)*(X 1 0+X 2 0)+(533651213091/357500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (2781/25000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (558435172849956863/558593750000000000 : ℝ)) (alpha := (533651213091/357500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (558435172849956863/558593750000000000 : ℝ)*(X 0 1+X 2 1)+(533651213091/357500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (2781/25000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (558435172849956863/558593750000000000 : ℝ)) (alpha := (533651213091/357500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (558435172849956863/558593750000000000 : ℝ)*(X 0 2+X 1 2)+(533651213091/357500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (2781/25000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (558435172849956863/558593750000000000 : ℝ)) (alpha := (533651213091/357500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1885380901/10000000000 : ℝ)*X 0 0+(5390399081/10000000000 : ℝ)*X 0 1+(5390399017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321252141/2500000000 : ℝ)*X 1 0+(-253714309/1250000000 : ℝ)*X 1 1+(2695199553/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057001687/2000000000 : ℝ)*X 2 0+(5390399197/10000000000 : ℝ)*X 2 1+(-507428631/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4477956901/10000000000 : ℝ)*X 0 0+(532399423/1250000000 : ℝ)*X 0 1+(2129597737/5000000000 : ℝ)*X 0 2+(4477956901/10000000000 : ℝ)*X 1 0+(532399423/1250000000 : ℝ)*X 1 1+(2129597737/5000000000 : ℝ)*X 1 2+(4477956901/10000000000 : ℝ)*X 2 0+(532399423/1250000000 : ℝ)*X 2 1+(2129597737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2224402249/10000000000 : ℝ)*X 0 0+(5264676669/10000000000 : ℝ)*X 0 1+(5264676899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((537335463/1000000000 : ℝ)*X 1 0+(-2080084851/10000000000 : ℝ)*X 1 1+(1052935343/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((671669339/1250000000 : ℝ)*X 2 0+(5264676561/10000000000 : ℝ)*X 2 1+(-520021237/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1045036823/2500000000 : ℝ)*X 0 0+(68875723/156250000 : ℝ)*X 0 1+(551005783/1250000000 : ℝ)*X 0 2+(1045036823/2500000000 : ℝ)*X 1 0+(68875723/156250000 : ℝ)*X 1 1+(551005783/1250000000 : ℝ)*X 1 2+(1045036823/2500000000 : ℝ)*X 2 0+(68875723/156250000 : ℝ)*X 2 1+(551005783/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-430647583/2000000000 : ℝ)*X 0 0+(2589089051/5000000000 : ℝ)*X 0 1+(337776443/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275148057/10000000000 : ℝ)*X 1 0+(-505990533/2500000000 : ℝ)*X 1 1+(2702211829/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((329696787/625000000 : ℝ)*X 2 0+(337776447/625000000 : ℝ)*X 2 1+(-1011981049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4510617907/10000000000 : ℝ)*X 0 0+(530322163/1250000000 : ℝ)*X 0 1+(2121288777/5000000000 : ℝ)*X 0 2+(4510617907/10000000000 : ℝ)*X 1 0+(530322163/1250000000 : ℝ)*X 1 1+(2121288777/5000000000 : ℝ)*X 1 2+(4510617907/10000000000 : ℝ)*X 2 0+(530322163/1250000000 : ℝ)*X 2 1+(2121288777/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-489226181/2500000000 : ℝ)*X 0 0+(5474667239/10000000000 : ℝ)*X 0 1+(2626808287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2690562127/5000000000 : ℝ)*X 1 0+(-1042205817/5000000000 : ℝ)*X 1 1+(1050723313/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690562403/5000000000 : ℝ)*X 2 0+(656702009/1250000000 : ℝ)*X 2 1+(-41688231/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4153500171/10000000000 : ℝ)*X 0 0+(1105282651/2500000000 : ℝ)*X 0 1+(4421130957/10000000000 : ℝ)*X 0 2+(4153500171/10000000000 : ℝ)*X 1 0+(1105282651/2500000000 : ℝ)*X 1 1+(4421130957/10000000000 : ℝ)*X 1 2+(4153500171/10000000000 : ℝ)*X 2 0+(1105282651/2500000000 : ℝ)*X 2 1+(4421130957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62851/100000 : ℝ) ≤ (-3510685128083966713392032570073/5585937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (459231/800000000000 : ℝ)*(upper1) + (23410999/50000000000000 : ℝ)*(lower4) + (31365307/50000000000000 : ℝ)*(upper5) + (290828977236947/10000000000000 : ℝ)*(major0) + (290828977236947/10000000000000 : ℝ)*(major1) + (290828977236947/10000000000000 : ℝ)*(major2) + (1128753573/100000000000000 : ℝ)*(sp1) + (2524321803/25000000000000 : ℝ)*(sp2) + (395264308929673/10000000000000 : ℝ)*(sp4) + (3952642985664753/100000000000000 : ℝ)*(sp5) + (1976317008565557/50000000000000 : ℝ)*(sp6) + (235609221019109/12500000000000 : ℝ)*(sp7) + (256280399/25000000000000 : ℝ)*(sp12) + (5602561599/50000000000000 : ℝ)*(sp15) + (188488497327607/10000000000000 : ℝ)*(f.failure) + (1976322057209163/50000000000000 : ℝ)*(f.sum) + (7567924248623/1787500000000000000000000000 : ℝ)*base66 + (33074117365656397/11171875000000000000000000000000 : ℝ)*base67 + (185498124838000147/11171875000000000000000000000000 : ℝ)*base69 + (219924682449875147/11171875000000000000000000000000 : ℝ)*base71 + (57747543726921/3575000000000000000000000000 : ℝ)*base74 + (42416080171461011/5585937500000000000000000000000 : ℝ)*base75 + (196906298378156397/11171875000000000000000000000000 : ℝ)*base77 + (121095064844406397/11171875000000000000000000000000 : ℝ)*base79 + (1154378917981/223437500000000000000000000 : ℝ)*base82 + (17883/200000000000000000000 : ℝ)*base89 + (17883/200000000000000000000 : ℝ)*base91 + (17883/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1473/2500 : ℝ) ≤ (10532370900090132948041846931/17875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132517/6250000000000 : ℝ)*(lower0) + (44777373/100000000000000 : ℝ)*(upper2) + (5262519/100000000000000 : ℝ)*(lower5) + (2976612175064503/100000000000000 : ℝ)*(major0) + (2976612175064503/100000000000000 : ℝ)*(major1) + (2976612175064503/100000000000000 : ℝ)*(major2) + (500552266103913/12500000000000 : ℝ)*(sp0) + (800883055499247/20000000000000 : ℝ)*(sp1) + (4004414498792327/100000000000000 : ℝ)*(sp2) + (1929160640435993/100000000000000 : ℝ)*(sp3) + (3039709753/100000000000000 : ℝ)*(sp5) + (3818413661/100000000000000 : ℝ)*(sp6) + (71993621/1562500000000 : ℝ)*(sp11) + (47093671/25000000000000 : ℝ)*(sp12) + (964582624013869/50000000000000 : ℝ)*(f.failure) + (1001104579301497/25000000000000 : ℝ)*(f.sum) + (23839220911699/8937500000000000000000000000 : ℝ)*base65 + (2193059355234391197/111718750000000000000000000000000 : ℝ)*base68 + (395139309826546303/111718750000000000000000000000000 : ℝ)*base69 + (149635924413297447/111718750000000000000000000000000 : ℝ)*base72 + (114220168270301/8937500000000000000000000000 : ℝ)*base74 + (214710565683577553/111718750000000000000000000000000 : ℝ)*base75 + (106773455992203697/111718750000000000000000000000000 : ℝ)*base78 + (447742632249983803/111718750000000000000000000000000 : ℝ)*base79 + (53285605868023/17875000000000000000000000000 : ℝ)*base81 + (10427961/1000000000000000000000 : ℝ)*base89 + (10427961/1000000000000000000000 : ℝ)*base91 + (10427961/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (7989/10000 : ℝ) ≤ (22313660495696147226798192649887/27929687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (74002753/25000000000000 : ℝ)*(lower3) + (30712957/50000000000000 : ℝ)*(upper4) + (62793123/50000000000000 : ℝ)*(lower5) + (1644601730007979/50000000000000 : ℝ)*(major0) + (1644601730007979/50000000000000 : ℝ)*(major1) + (1644601730007979/50000000000000 : ℝ)*(major2) + (24230145871/100000000000000 : ℝ)*(sp0) + (3241706563/781250000000 : ℝ)*(sp1) + (237433075581/100000000000000 : ℝ)*(sp2) + (72682777573/50000000000000 : ℝ)*(sp3) + (2209996934923053/50000000000000 : ℝ)*(sp8) + (4419603161551913/100000000000000 : ℝ)*(sp9) + (1104945166729099/25000000000000 : ℝ)*(sp10) + (213161269883491/10000000000000 : ℝ)*(sp11) + (266469758048757/12500000000000 : ℝ)*(f.failure) + (2210009049995989/50000000000000 : ℝ)*(f.sum) + (108433098139447/17875000000000000000000000000 : ℝ)*base66 + (10807384288722377/27929687500000000000000000000000 : ℝ)*base67 + (108354052413621373/27929687500000000000000000000000 : ℝ)*base70 + (29298148382787249/13964843750000000000000000000000 : ℝ)*base72 + (27870468818161/8937500000000000000000000000 : ℝ)*base74 + (143348221098929129/55859375000000000000000000000000 : ℝ)*base75 + (28190615376902623/27929687500000000000000000000000 : ℝ)*base78 + (27462169547838937/6982421875000000000000000000000 : ℝ)*base80 + (46586113194161/8937500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2627233/250000000000000000000 : ℝ)*base89 + (2627233/250000000000000000000 : ℝ)*base91 + (2627233/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84309/100000 : ℝ) ≤ (-47093113664471047816283484790707/55859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46294349/100000000000000 : ℝ)*(lower0) + (25901751/12500000000000 : ℝ)*(lower1) + (33114053/20000000000000 : ℝ)*(lower2) + (3325534347334081/100000000000000 : ℝ)*(major0) + (3325534347334081/100000000000000 : ℝ)*(major1) + (3325534347334081/100000000000000 : ℝ)*(major2) + (7054332183/50000000000000 : ℝ)*(sp0) + (365516964691/100000000000000 : ℝ)*(sp5) + (236895527089/50000000000000 : ℝ)*(sp6) + (1296605913/2000000000000 : ℝ)*(sp7) + (4523852378448067/100000000000000 : ℝ)*(sp12) + (2261750485073871/50000000000000 : ℝ)*(sp13) + (904678539211651/20000000000000 : ℝ)*(sp14) + (2155239561637937/100000000000000 : ℝ)*(sp15) + (538826097983397/25000000000000 : ℝ)*(f.failure) + (4523866487112433/100000000000000 : ℝ)*(f.sum) + (422919840711/279296875000000000000000000 : ℝ)*base66 + (432987017781123931/111718750000000000000000000000000 : ℝ)*base67 + (13551997239188569/111718750000000000000000000000000 : ℝ)*base70 + (261691946886063569/111718750000000000000000000000000 : ℝ)*base72 + (174444091291377/8937500000000000000000000000 : ℝ)*base74 + (76423422335030181/111718750000000000000000000000000 : ℝ)*base75 + (801769036670438569/111718750000000000000000000000000 : ℝ)*base78 + (1491074804825907319/111718750000000000000000000000000 : ℝ)*base80 + (48231084324373/8937500000000000000000000000 : ℝ)*base81 + (3877393/500000000000000000000 : ℝ)*base89 + (3877393/500000000000000000000 : ℝ)*base91 + (3877393/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1331_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62851/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1473/2500 : ℝ) else (7989/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84309/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1331_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1331_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5557/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62851/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1473/2500 : ℝ) else (7989/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84309/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1331_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1331_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1331_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5557/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62851/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1473/2500 : ℝ) else (7989/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84309/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1331_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
