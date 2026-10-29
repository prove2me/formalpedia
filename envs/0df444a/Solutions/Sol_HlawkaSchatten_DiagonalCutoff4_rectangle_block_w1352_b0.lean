-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1352_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:08:01.309346+00:00
-- url     : https://prove2.me/submissions/fab8e6e3-3f2a-4a34-b9cd-1d2045498273

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
theorem support_rectangle_w1352_s0_0 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-450812323/2500000000 : ℝ)*x 0 + (2996304451/5000000000 : ℝ)*x 1 + (2406644681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450812323/2500000000 : ℝ)^539 ≤ (2115412691939/20000000000000 : ℝ)^411 := by
    have hnat : (450812323 : ℕ)^539*20000000000000^411 ≤ 2115412691939^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450812323 2500000000 2115412691939 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2996304451/5000000000 : ℝ)^539 ≤ (51092556927939/100000000000000 : ℝ)^411 := by
    have hnat : (2996304451 : ℕ)^539*100000000000000^411 ≤ 51092556927939^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996304451 5000000000 51092556927939 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2406644681/5000000000 : ℝ)^539 ≤ (19165189798471/50000000000000 : ℝ)^411 := by
    have hnat : (2406644681 : ℕ)^539*50000000000000^411 ≤ 19165189798471^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406644681 5000000000 19165189798471 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-450812323/2500000000 : ℝ), (2996304451/5000000000 : ℝ), (2406644681/5000000000 : ℝ)] ![(2115412691939/20000000000000 : ℝ), (51092556927939/100000000000000 : ℝ), (19165189798471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-450812323/2500000000 : ℝ)|^539 ≤ (2115412691939/20000000000000 : ℝ)^411
        have hw : |(-450812323/2500000000 : ℝ)|=(450812323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2996304451/5000000000 : ℝ)|^539 ≤ (51092556927939/100000000000000 : ℝ)^411
        have hw : |(2996304451/5000000000 : ℝ)|=(2996304451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2406644681/5000000000 : ℝ)|^539 ≤ (19165189798471/50000000000000 : ℝ)^411
        have hw : |(2406644681/5000000000 : ℝ)|=(2406644681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s0_1 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2750346511/5000000000 : ℝ)*x 0 + (-123654171/500000000 : ℝ)*x 1 + (601661227/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750346511/5000000000 : ℝ)^539 ≤ (11416005714649/25000000000000 : ℝ)^411 := by
    have hnat : (2750346511 : ℕ)^539*25000000000000^411 ≤ 11416005714649^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750346511 5000000000 11416005714649 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123654171/500000000 : ℝ)^539 ≤ (8002796395337/50000000000000 : ℝ)^411 := by
    have hnat : (123654171 : ℕ)^539*50000000000000^411 ≤ 8002796395337^411*500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123654171 500000000 8002796395337 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601661227/1250000000 : ℝ)^539 ≤ (19165192169157/50000000000000 : ℝ)^411 := by
    have hnat : (601661227 : ℕ)^539*50000000000000^411 ≤ 19165192169157^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601661227 1250000000 19165192169157 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750346511/5000000000 : ℝ), (-123654171/500000000 : ℝ), (601661227/1250000000 : ℝ)] ![(11416005714649/25000000000000 : ℝ), (8002796395337/50000000000000 : ℝ), (19165192169157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750346511/5000000000 : ℝ)|^539 ≤ (11416005714649/25000000000000 : ℝ)^411
        have hw : |(2750346511/5000000000 : ℝ)|=(2750346511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123654171/500000000 : ℝ)|^539 ≤ (8002796395337/50000000000000 : ℝ)^411
        have hw : |(-123654171/500000000 : ℝ)|=(123654171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601661227/1250000000 : ℝ)|^539 ≤ (19165192169157/50000000000000 : ℝ)^411
        have hw : |(601661227/1250000000 : ℝ)|=(601661227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s0_2 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5500692833/10000000000 : ℝ)*x 0 + (1203322361/2500000000 : ℝ)*x 1 + (-2473084121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5500692833/10000000000 : ℝ)^539 ≤ (1826560832039/4000000000000 : ℝ)^411 := by
    have hnat : (5500692833 : ℕ)^539*4000000000000^411 ≤ 1826560832039^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500692833 10000000000 1826560832039 4000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203322361/2500000000 : ℝ)^539 ≤ (38330380453313/100000000000000 : ℝ)^411 := by
    have hnat : (1203322361 : ℕ)^539*100000000000000^411 ≤ 38330380453313^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203322361 2500000000 38330380453313 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2473084121/10000000000 : ℝ)^539 ≤ (8002799370207/50000000000000 : ℝ)^411 := by
    have hnat : (2473084121 : ℕ)^539*50000000000000^411 ≤ 8002799370207^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2473084121 10000000000 8002799370207 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5500692833/10000000000 : ℝ), (1203322361/2500000000 : ℝ), (-2473084121/10000000000 : ℝ)] ![(1826560832039/4000000000000 : ℝ), (38330380453313/100000000000000 : ℝ), (8002799370207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5500692833/10000000000 : ℝ)|^539 ≤ (1826560832039/4000000000000 : ℝ)^411
        have hw : |(5500692833/10000000000 : ℝ)|=(5500692833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203322361/2500000000 : ℝ)|^539 ≤ (38330380453313/100000000000000 : ℝ)^411
        have hw : |(1203322361/2500000000 : ℝ)|=(1203322361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2473084121/10000000000 : ℝ)|^539 ≤ (8002799370207/50000000000000 : ℝ)^411
        have hw : |(-2473084121/10000000000 : ℝ)|=(2473084121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s0_3 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (417725359/1000000000 : ℝ)*x 0 + (1553042231/5000000000 : ℝ)*x 1 + (2792775423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417725359/1000000000 : ℝ)^539 ≤ (6365796884371/20000000000000 : ℝ)^411 := by
    have hnat : (417725359 : ℕ)^539*20000000000000^411 ≤ 6365796884371^411*1000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417725359 1000000000 6365796884371 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553042231/5000000000 : ℝ)^539 ≤ (21580943732231/100000000000000 : ℝ)^411 := by
    have hnat : (1553042231 : ℕ)^539*100000000000000^411 ≤ 21580943732231^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553042231 5000000000 21580943732231 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2792775423/5000000000 : ℝ)^539 ≤ (2329503591361/5000000000000 : ℝ)^411 := by
    have hnat : (2792775423 : ℕ)^539*5000000000000^411 ≤ 2329503591361^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2792775423 5000000000 2329503591361 5000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417725359/1000000000 : ℝ), (1553042231/5000000000 : ℝ), (2792775423/5000000000 : ℝ)] ![(6365796884371/20000000000000 : ℝ), (21580943732231/100000000000000 : ℝ), (2329503591361/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417725359/1000000000 : ℝ)|^539 ≤ (6365796884371/20000000000000 : ℝ)^411
        have hw : |(417725359/1000000000 : ℝ)|=(417725359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1553042231/5000000000 : ℝ)|^539 ≤ (21580943732231/100000000000000 : ℝ)^411
        have hw : |(1553042231/5000000000 : ℝ)|=(1553042231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2792775423/5000000000 : ℝ)|^539 ≤ (2329503591361/5000000000000 : ℝ)^411
        have hw : |(2792775423/5000000000 : ℝ)|=(2792775423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s0_4 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-903826859/5000000000 : ℝ)*x 0 + (121090599/250000000 : ℝ)*x 1 + (596119087/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903826859/5000000000 : ℝ)^539 ≤ (5305478255001/50000000000000 : ℝ)^411 := by
    have hnat : (903826859 : ℕ)^539*50000000000000^411 ≤ 5305478255001^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903826859 5000000000 5305478255001 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121090599/250000000 : ℝ)^539 ≤ (38647490897171/100000000000000 : ℝ)^411 := by
    have hnat : (121090599 : ℕ)^539*100000000000000^411 ≤ 38647490897171^411*250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121090599 250000000 38647490897171 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (596119087/1000000000 : ℝ)^539 ≤ (50741552581647/100000000000000 : ℝ)^411 := by
    have hnat : (596119087 : ℕ)^539*100000000000000^411 ≤ 50741552581647^411*1000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596119087 1000000000 50741552581647 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-903826859/5000000000 : ℝ), (121090599/250000000 : ℝ), (596119087/1000000000 : ℝ)] ![(5305478255001/50000000000000 : ℝ), (38647490897171/100000000000000 : ℝ), (50741552581647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-903826859/5000000000 : ℝ)|^539 ≤ (5305478255001/50000000000000 : ℝ)^411
        have hw : |(-903826859/5000000000 : ℝ)|=(903826859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121090599/250000000 : ℝ)|^539 ≤ (38647490897171/100000000000000 : ℝ)^411
        have hw : |(121090599/250000000 : ℝ)|=(121090599/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(596119087/1000000000 : ℝ)|^539 ≤ (50741552581647/100000000000000 : ℝ)^411
        have hw : |(596119087/1000000000 : ℝ)|=(596119087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s0_5 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (64740343/125000000 : ℝ)*x 0 + (-331295907/2500000000 : ℝ)*x 1 + (2980595239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64740343/125000000 : ℝ)^539 ≤ (164830274997/390625000000 : ℝ)^411 := by
    have hnat : (64740343 : ℕ)^539*390625000000^411 ≤ 164830274997^411*125000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64740343 125000000 164830274997 390625000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331295907/2500000000 : ℝ)^539 ≤ (7061901373043/100000000000000 : ℝ)^411 := by
    have hnat : (331295907 : ℕ)^539*100000000000000^411 ≤ 7061901373043^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331295907 2500000000 7061901373043 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2980595239/5000000000 : ℝ)^539 ≤ (6342693525723/12500000000000 : ℝ)^411 := by
    have hnat : (2980595239 : ℕ)^539*12500000000000^411 ≤ 6342693525723^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980595239 5000000000 6342693525723 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64740343/125000000 : ℝ), (-331295907/2500000000 : ℝ), (2980595239/5000000000 : ℝ)] ![(164830274997/390625000000 : ℝ), (7061901373043/100000000000000 : ℝ), (6342693525723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64740343/125000000 : ℝ)|^539 ≤ (164830274997/390625000000 : ℝ)^411
        have hw : |(64740343/125000000 : ℝ)|=(64740343/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-331295907/2500000000 : ℝ)|^539 ≤ (7061901373043/100000000000000 : ℝ)^411
        have hw : |(-331295907/2500000000 : ℝ)|=(331295907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2980595239/5000000000 : ℝ)|^539 ≤ (6342693525723/12500000000000 : ℝ)^411
        have hw : |(2980595239/5000000000 : ℝ)|=(2980595239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s0_6 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2589613683/5000000000 : ℝ)*x 0 + (2980595467/5000000000 : ℝ)*x 1 + (-662591507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589613683/5000000000 : ℝ)^539 ≤ (4219654960857/10000000000000 : ℝ)^411 := by
    have hnat : (2589613683 : ℕ)^539*10000000000000^411 ≤ 4219654960857^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589613683 5000000000 4219654960857 10000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2980595467/5000000000 : ℝ)^539 ≤ (25370776648037/50000000000000 : ℝ)^411 := by
    have hnat : (2980595467 : ℕ)^539*50000000000000^411 ≤ 25370776648037^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980595467 5000000000 25370776648037 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (662591507/5000000000 : ℝ)^539 ≤ (353094854101/5000000000000 : ℝ)^411 := by
    have hnat : (662591507 : ℕ)^539*5000000000000^411 ≤ 353094854101^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662591507 5000000000 353094854101 5000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589613683/5000000000 : ℝ), (2980595467/5000000000 : ℝ), (-662591507/5000000000 : ℝ)] ![(4219654960857/10000000000000 : ℝ), (25370776648037/50000000000000 : ℝ), (353094854101/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589613683/5000000000 : ℝ)|^539 ≤ (4219654960857/10000000000000 : ℝ)^411
        have hw : |(2589613683/5000000000 : ℝ)|=(2589613683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2980595467/5000000000 : ℝ)|^539 ≤ (25370776648037/50000000000000 : ℝ)^411
        have hw : |(2980595467/5000000000 : ℝ)|=(2980595467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-662591507/5000000000 : ℝ)|^539 ≤ (353094854101/5000000000000 : ℝ)^411
        have hw : |(-662591507/5000000000 : ℝ)|=(662591507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s0_7 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2093255433/5000000000 : ℝ)*x 0 + (34511093/62500000 : ℝ)*x 1 + (3172139103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093255433/5000000000 : ℝ)^539 ≤ (31921520665113/100000000000000 : ℝ)^411 := by
    have hnat : (2093255433 : ℕ)^539*100000000000000^411 ≤ 31921520665113^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093255433 5000000000 31921520665113 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34511093/62500000 : ℝ)^539 ≤ (11473418878267/25000000000000 : ℝ)^411 := by
    have hnat : (34511093 : ℕ)^539*25000000000000^411 ≤ 11473418878267^411*62500000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34511093 62500000 11473418878267 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3172139103/10000000000 : ℝ)^539 ≤ (5546200952369/25000000000000 : ℝ)^411 := by
    have hnat : (3172139103 : ℕ)^539*25000000000000^411 ≤ 5546200952369^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3172139103 10000000000 5546200952369 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093255433/5000000000 : ℝ), (34511093/62500000 : ℝ), (3172139103/10000000000 : ℝ)] ![(31921520665113/100000000000000 : ℝ), (11473418878267/25000000000000 : ℝ), (5546200952369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093255433/5000000000 : ℝ)|^539 ≤ (31921520665113/100000000000000 : ℝ)^411
        have hw : |(2093255433/5000000000 : ℝ)|=(2093255433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34511093/62500000 : ℝ)|^539 ≤ (11473418878267/25000000000000 : ℝ)^411
        have hw : |(34511093/62500000 : ℝ)|=(34511093/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3172139103/10000000000 : ℝ)|^539 ≤ (5546200952369/25000000000000 : ℝ)^411
        have hw : |(3172139103/10000000000 : ℝ)|=(3172139103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1352_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1489/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26799/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4311/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4311 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4311*1^1024 ≤ 0^1024*1^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4311/1024 : ℝ) ≤ (2111971766044703959/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4311 ≤ (2111971766044703959/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4311*100000000000000000000^1024 ≤ 2111971766044703959^1024*5^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2111971766044703959 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2111971766044703959/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4311 := by
      have hnat : (1 : ℕ)^1024*1^4311 ≤ 1^4311*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102111971766044703959/100000000000000000000 : ℝ) ≤ (1004976709040849/1000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (102111971766044703959/100000000000000000000 : ℝ)^1024 ≤ (1004976709040849/1000000000000000 : ℝ)^4311 := by
      have hnat : (102111971766044703959 : ℕ)^1024*1000000000000000^4311 ≤ 1004976709040849^4311*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102111971766044703959 100000000000000000000 1004976709040849 1000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004976709040849/1000000000000000 : ℝ)) (X := (102111971766044703959/100000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52111971766044703959/50000000000000000000 : ℝ) ≤ (504976709040849/500000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (52111971766044703959/50000000000000000000 : ℝ)^1024 ≤ (504976709040849/500000000000000 : ℝ)^4311 := by
      have hnat : (52111971766044703959 : ℕ)^1024*500000000000000^4311 ≤ 504976709040849^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52111971766044703959 50000000000000000000 504976709040849 500000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (504976709040849/500000000000000 : ℝ)) (X := (52111971766044703959/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4976709040849/400000000000000 : ℝ)*(0 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4976709040849/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2111971766044703959/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4976709040849/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4311/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4976709040849/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1004976709040849/1000000000000000 : ℝ) by norm_num, show 1+(2111971766044703959/100000000000000000000 : ℝ)+(0 : ℝ)=(102111971766044703959/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2111971766044703959/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4976709040849/400000000000000 : ℝ)*(2/5 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4976709040849/400000000000000 : ℝ)*(2/5 : ℝ)=(504976709040849/500000000000000 : ℝ) by norm_num, show 1+2*(2111971766044703959/100000000000000000000 : ℝ)=(52111971766044703959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4976709040849/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4976709040849/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4976709040849/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4976709040849/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4976709040849/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4976709040849/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-450812323/2500000000 : ℝ)*X 0 0+(2996304451/5000000000 : ℝ)*X 0 1+(2406644681/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2750346511/5000000000 : ℝ)*X 1 0+(-123654171/500000000 : ℝ)*X 1 1+(601661227/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5500692833/10000000000 : ℝ)*X 2 0+(1203322361/2500000000 : ℝ)*X 2 1+(-2473084121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((417725359/1000000000 : ℝ)*X 0 0+(1553042231/5000000000 : ℝ)*X 0 1+(2792775423/5000000000 : ℝ)*X 0 2+(417725359/1000000000 : ℝ)*X 1 0+(1553042231/5000000000 : ℝ)*X 1 1+(2792775423/5000000000 : ℝ)*X 1 2+(417725359/1000000000 : ℝ)*X 2 0+(1553042231/5000000000 : ℝ)*X 2 1+(2792775423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-903826859/5000000000 : ℝ)*X 0 0+(121090599/250000000 : ℝ)*X 0 1+(596119087/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((64740343/125000000 : ℝ)*X 1 0+(-331295907/2500000000 : ℝ)*X 1 1+(2980595239/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2589613683/5000000000 : ℝ)*X 2 0+(2980595467/5000000000 : ℝ)*X 2 1+(-662591507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2093255433/5000000000 : ℝ)*X 0 0+(34511093/62500000 : ℝ)*X 0 1+(3172139103/10000000000 : ℝ)*X 0 2+(2093255433/5000000000 : ℝ)*X 1 0+(34511093/62500000 : ℝ)*X 1 1+(3172139103/10000000000 : ℝ)*X 1 2+(2093255433/5000000000 : ℝ)*X 2 0+(34511093/62500000 : ℝ)*X 2 1+(3172139103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49625019888242227532997/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126256271/100000000000000 : ℝ)*(base1) + (1161408561/100000000000000 : ℝ)*(base19) + (1132273489/100000000000000 : ℝ)*(base23) + (210789829/100000000000000 : ℝ)*(upper3) + (5488207/25000000000000 : ℝ)*(upper5) + (312817534282649/50000000000000 : ℝ)*(major0) + (312817534282649/50000000000000 : ℝ)*(major1) + (312817534282649/50000000000000 : ℝ)*(major2) + (423975429709407/50000000000000 : ℝ)*(sp0) + (211988197287653/25000000000000 : ℝ)*(sp1) + (847952818285683/100000000000000 : ℝ)*(sp2) + (100828485774939/25000000000000 : ℝ)*(sp3) + (321739663/10000000000000 : ℝ)*(sp4) + (975899329/50000000000000 : ℝ)*(sp7) + (80663204230937/20000000000000 : ℝ)*(f.failure) + (211988487639793/25000000000000 : ℝ)*(f.sum) + (20648134529001/10000000000000000000000000000 : ℝ)*base65 + (48792733870999/20000000000000000000000000000 : ℝ)*base68 + (70050789430999/20000000000000000000000000000 : ℝ)*base70 + (52235373710999/20000000000000000000000000000 : ℝ)*base72 + (47583560209001/10000000000000000000000000000 : ℝ)*base73 + (173573641910999/20000000000000000000000000000 : ℝ)*base76 + (34018983210999/20000000000000000000000000000 : ℝ)*base78 + (12281401649001/20000000000000000000000000000 : ℝ)*base79 + (39840275859001/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4014833/2000000000000000000000 : ℝ)*base90 + (4014833/2000000000000000000000 : ℝ)*base92 + (4014833/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16293710174879968184847/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158226279/50000000000000 : ℝ)*(base19) + (571587099/100000000000000 : ℝ)*(base23) + (275525447/100000000000000 : ℝ)*(base39) + (1633931/50000000000000 : ℝ)*(upper3) + (18122997/12500000000000 : ℝ)*(upper5) + (330099352489083/50000000000000 : ℝ)*(major0) + (330099352489083/50000000000000 : ℝ)*(major1) + (660198429452719/100000000000000 : ℝ)*(major2) + (779380651/100000000000000 : ℝ)*(sp1) + (152694663/20000000000000 : ℝ)*(sp2) + (111849941970593/12500000000000 : ℝ)*(sp4) + (55924902495721/6250000000000 : ℝ)*(sp5) + (447399238114889/50000000000000 : ℝ)*(sp6) + (2127987450207/500000000000 : ℝ)*(sp7) + (2127987450207/500000000000 : ℝ)*(f.failure) + (55924988205637/6250000000000 : ℝ)*(f.sum) + (15839107219727/8000000000000000000000000000 : ℝ)*base66 + (168301444481569/40000000000000000000000000000 : ℝ)*base68 + (131626643951467/20000000000000000000000000000 : ℝ)*base69 + (314630217361569/40000000000000000000000000000 : ℝ)*base72 + (11439897331727/8000000000000000000000000000 : ℝ)*base74 + (12776898928533/20000000000000000000000000000 : ℝ)*base76 + (112158497308533/20000000000000000000000000000 : ℝ)*base78 + (172975356688533/20000000000000000000000000000 : ℝ)*base80 + (6932251621467/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (367737/50000000000000000000 : ℝ)*base89 + (367737/50000000000000000000 : ℝ)*base91 + (367737/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1352_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1489/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26799/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1352_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1352_s1_0 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986625367/10000000000 : ℝ)*x 0 + (1127533901/2000000000 : ℝ)*x 1 + (1010156493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986625367/10000000000 : ℝ)^539 ≤ (750592768591/6250000000000 : ℝ)^411 := by
    have hnat : (1986625367 : ℕ)^539*6250000000000^411 ≤ 750592768591^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986625367 10000000000 750592768591 6250000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127533901/2000000000 : ℝ)^539 ≤ (47161020113741/100000000000000 : ℝ)^411 := by
    have hnat : (1127533901 : ℕ)^539*100000000000000^411 ≤ 47161020113741^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127533901 2000000000 47161020113741 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010156493/2000000000 : ℝ)^539 ≤ (20414747782913/50000000000000 : ℝ)^411 := by
    have hnat : (1010156493 : ℕ)^539*50000000000000^411 ≤ 20414747782913^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010156493 2000000000 20414747782913 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986625367/10000000000 : ℝ), (1127533901/2000000000 : ℝ), (1010156493/2000000000 : ℝ)] ![(750592768591/6250000000000 : ℝ), (47161020113741/100000000000000 : ℝ), (20414747782913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986625367/10000000000 : ℝ)|^539 ≤ (750592768591/6250000000000 : ℝ)^411
        have hw : |(-1986625367/10000000000 : ℝ)|=(1986625367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127533901/2000000000 : ℝ)|^539 ≤ (47161020113741/100000000000000 : ℝ)^411
        have hw : |(1127533901/2000000000 : ℝ)|=(1127533901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010156493/2000000000 : ℝ)|^539 ≤ (20414747782913/50000000000000 : ℝ)^411
        have hw : |(1010156493/2000000000 : ℝ)|=(1010156493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s1_1 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5404674583/10000000000 : ℝ)*x 0 + (-1149767607/5000000000 : ℝ)*x 1 + (1262695743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404674583/10000000000 : ℝ)^539 ≤ (44621533869557/100000000000000 : ℝ)^411 := by
    have hnat : (5404674583 : ℕ)^539*100000000000000^411 ≤ 44621533869557^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404674583 10000000000 44621533869557 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1149767607/5000000000 : ℝ)^539 ≤ (14548965167411/100000000000000 : ℝ)^411 := by
    have hnat : (1149767607 : ℕ)^539*100000000000000^411 ≤ 14548965167411^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149767607 5000000000 14548965167411 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1262695743/2500000000 : ℝ)^539 ≤ (1633180037629/4000000000000 : ℝ)^411 := by
    have hnat : (1262695743 : ℕ)^539*4000000000000^411 ≤ 1633180037629^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262695743 2500000000 1633180037629 4000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404674583/10000000000 : ℝ), (-1149767607/5000000000 : ℝ), (1262695743/2500000000 : ℝ)] ![(44621533869557/100000000000000 : ℝ), (14548965167411/100000000000000 : ℝ), (1633180037629/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404674583/10000000000 : ℝ)|^539 ≤ (44621533869557/100000000000000 : ℝ)^411
        have hw : |(5404674583/10000000000 : ℝ)|=(5404674583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1149767607/5000000000 : ℝ)|^539 ≤ (14548965167411/100000000000000 : ℝ)^411
        have hw : |(-1149767607/5000000000 : ℝ)|=(1149767607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1262695743/2500000000 : ℝ)|^539 ≤ (1633180037629/4000000000000 : ℝ)^411
        have hw : |(1262695743/2500000000 : ℝ)|=(1262695743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s1_2 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1351168641/2500000000 : ℝ)*x 0 + (5050782547/10000000000 : ℝ)*x 1 + (-2299535783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351168641/2500000000 : ℝ)^539 ≤ (44621533663837/100000000000000 : ℝ)^411 := by
    have hnat : (1351168641 : ℕ)^539*100000000000000^411 ≤ 44621533663837^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351168641 2500000000 44621533663837 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5050782547/10000000000 : ℝ)^539 ≤ (40829496435139/100000000000000 : ℝ)^411 := by
    have hnat : (5050782547 : ℕ)^539*100000000000000^411 ≤ 40829496435139^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5050782547 10000000000 40829496435139 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2299535783/10000000000 : ℝ)^539 ≤ (7274484944299/50000000000000 : ℝ)^411 := by
    have hnat : (2299535783 : ℕ)^539*50000000000000^411 ≤ 7274484944299^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299535783 10000000000 7274484944299 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351168641/2500000000 : ℝ), (5050782547/10000000000 : ℝ), (-2299535783/10000000000 : ℝ)] ![(44621533663837/100000000000000 : ℝ), (40829496435139/100000000000000 : ℝ), (7274484944299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351168641/2500000000 : ℝ)|^539 ≤ (44621533663837/100000000000000 : ℝ)^411
        have hw : |(1351168641/2500000000 : ℝ)|=(1351168641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5050782547/10000000000 : ℝ)|^539 ≤ (40829496435139/100000000000000 : ℝ)^411
        have hw : |(5050782547/10000000000 : ℝ)|=(5050782547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2299535783/10000000000 : ℝ)|^539 ≤ (7274484944299/50000000000000 : ℝ)^411
        have hw : |(-2299535783/10000000000 : ℝ)|=(2299535783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s1_3 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4290525043/10000000000 : ℝ)*x 0 + (371450331/1000000000 : ℝ)*x 1 + (4948404603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4290525043/10000000000 : ℝ)^539 ≤ (3296561165739/10000000000000 : ℝ)^411 := by
    have hnat : (4290525043 : ℕ)^539*10000000000000^411 ≤ 3296561165739^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290525043 10000000000 3296561165739 10000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (371450331/1000000000 : ℝ)^539 ≤ (27286797295499/100000000000000 : ℝ)^411 := by
    have hnat : (371450331 : ℕ)^539*100000000000000^411 ≤ 27286797295499^411*1000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371450331 1000000000 27286797295499 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4948404603/10000000000 : ℝ)^539 ≤ (19873795514493/50000000000000 : ℝ)^411 := by
    have hnat : (4948404603 : ℕ)^539*50000000000000^411 ≤ 19873795514493^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4948404603 10000000000 19873795514493 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4290525043/10000000000 : ℝ), (371450331/1000000000 : ℝ), (4948404603/10000000000 : ℝ)] ![(3296561165739/10000000000000 : ℝ), (27286797295499/100000000000000 : ℝ), (19873795514493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4290525043/10000000000 : ℝ)|^539 ≤ (3296561165739/10000000000000 : ℝ)^411
        have hw : |(4290525043/10000000000 : ℝ)|=(4290525043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(371450331/1000000000 : ℝ)|^539 ≤ (27286797295499/100000000000000 : ℝ)^411
        have hw : |(371450331/1000000000 : ℝ)|=(371450331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4948404603/10000000000 : ℝ)|^539 ≤ (19873795514493/50000000000000 : ℝ)^411
        have hw : |(4948404603/10000000000 : ℝ)|=(4948404603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s1_4 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-248392989/1250000000 : ℝ)*x 0 + (316130633/625000000 : ℝ)*x 1 + (5630229931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (248392989/1250000000 : ℝ)^539 ≤ (12013595410577/100000000000000 : ℝ)^411 := by
    have hnat : (248392989 : ℕ)^539*100000000000000^411 ≤ 12013595410577^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248392989 1250000000 12013595410577 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316130633/625000000 : ℝ)^539 ≤ (5113373038409/12500000000000 : ℝ)^411 := by
    have hnat : (316130633 : ℕ)^539*12500000000000^411 ≤ 5113373038409^411*625000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316130633 625000000 5113373038409 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5630229931/10000000000 : ℝ)^539 ≤ (11769855068283/25000000000000 : ℝ)^411 := by
    have hnat : (5630229931 : ℕ)^539*25000000000000^411 ≤ 11769855068283^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5630229931 10000000000 11769855068283 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-248392989/1250000000 : ℝ), (316130633/625000000 : ℝ), (5630229931/10000000000 : ℝ)] ![(12013595410577/100000000000000 : ℝ), (5113373038409/12500000000000 : ℝ), (11769855068283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-248392989/1250000000 : ℝ)|^539 ≤ (12013595410577/100000000000000 : ℝ)^411
        have hw : |(-248392989/1250000000 : ℝ)|=(248392989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(316130633/625000000 : ℝ)|^539 ≤ (5113373038409/12500000000000 : ℝ)^411
        have hw : |(316130633/625000000 : ℝ)|=(316130633/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5630229931/10000000000 : ℝ)|^539 ≤ (11769855068283/25000000000000 : ℝ)^411
        have hw : |(5630229931/10000000000 : ℝ)|=(5630229931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s1_5 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5252259107/10000000000 : ℝ)*x 0 + (-430022011/2500000000 : ℝ)*x 1 + (5630229983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252259107/10000000000 : ℝ)^539 ≤ (10744643392587/25000000000000 : ℝ)^411 := by
    have hnat : (5252259107 : ℕ)^539*25000000000000^411 ≤ 10744643392587^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252259107 10000000000 10744643392587 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430022011/2500000000 : ℝ)^539 ≤ (248550139421/2500000000000 : ℝ)^411 := by
    have hnat : (430022011 : ℕ)^539*2500000000000^411 ≤ 248550139421^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430022011 2500000000 248550139421 2500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5630229983/10000000000 : ℝ)^539 ≤ (47079420843369/100000000000000 : ℝ)^411 := by
    have hnat : (5630229983 : ℕ)^539*100000000000000^411 ≤ 47079420843369^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5630229983 10000000000 47079420843369 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252259107/10000000000 : ℝ), (-430022011/2500000000 : ℝ), (5630229983/10000000000 : ℝ)] ![(10744643392587/25000000000000 : ℝ), (248550139421/2500000000000 : ℝ), (47079420843369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252259107/10000000000 : ℝ)|^539 ≤ (10744643392587/25000000000000 : ℝ)^411
        have hw : |(5252259107/10000000000 : ℝ)|=(5252259107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430022011/2500000000 : ℝ)|^539 ≤ (248550139421/2500000000000 : ℝ)^411
        have hw : |(-430022011/2500000000 : ℝ)|=(430022011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5630229983/10000000000 : ℝ)|^539 ≤ (47079420843369/100000000000000 : ℝ)^411
        have hw : |(5630229983/10000000000 : ℝ)|=(5630229983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s1_6 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5252259003/10000000000 : ℝ)*x 0 + (2815115029/5000000000 : ℝ)*x 1 + (-1720088083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252259003/10000000000 : ℝ)^539 ≤ (10744643113573/25000000000000 : ℝ)^411 := by
    have hnat : (5252259003 : ℕ)^539*25000000000000^411 ≤ 10744643113573^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252259003 10000000000 10744643113573 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2815115029/5000000000 : ℝ)^539 ≤ (23539710832913/50000000000000 : ℝ)^411 := by
    have hnat : (2815115029 : ℕ)^539*50000000000000^411 ≤ 23539710832913^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2815115029 5000000000 23539710832913 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1720088083/10000000000 : ℝ)^539 ≤ (9942005872461/100000000000000 : ℝ)^411 := by
    have hnat : (1720088083 : ℕ)^539*100000000000000^411 ≤ 9942005872461^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720088083 10000000000 9942005872461 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252259003/10000000000 : ℝ), (2815115029/5000000000 : ℝ), (-1720088083/10000000000 : ℝ)] ![(10744643113573/25000000000000 : ℝ), (23539710832913/50000000000000 : ℝ), (9942005872461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252259003/10000000000 : ℝ)|^539 ≤ (10744643113573/25000000000000 : ℝ)^411
        have hw : |(5252259003/10000000000 : ℝ)|=(5252259003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2815115029/5000000000 : ℝ)|^539 ≤ (23539710832913/50000000000000 : ℝ)^411
        have hw : |(2815115029/5000000000 : ℝ)|=(2815115029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1720088083/10000000000 : ℝ)|^539 ≤ (9942005872461/100000000000000 : ℝ)^411
        have hw : |(-1720088083/10000000000 : ℝ)|=(1720088083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s1_7 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2145807851/5000000000 : ℝ)*x 0 + (1233260379/2500000000 : ℝ)*x 1 + (1457087/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145807851/5000000000 : ℝ)^539 ≤ (32976601812387/100000000000000 : ℝ)^411 := by
    have hnat : (2145807851 : ℕ)^539*100000000000000^411 ≤ 32976601812387^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145807851 5000000000 32976601812387 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1233260379/2500000000 : ℝ)^539 ≤ (39585834848521/100000000000000 : ℝ)^411 := by
    have hnat : (1233260379 : ℕ)^539*100000000000000^411 ≤ 39585834848521^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233260379 2500000000 39585834848521 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1457087/3906250 : ℝ)^539 ≤ (27437563322873/100000000000000 : ℝ)^411 := by
    have hnat : (1457087 : ℕ)^539*100000000000000^411 ≤ 27437563322873^411*3906250^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1457087 3906250 27437563322873 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145807851/5000000000 : ℝ), (1233260379/2500000000 : ℝ), (1457087/3906250 : ℝ)] ![(32976601812387/100000000000000 : ℝ), (39585834848521/100000000000000 : ℝ), (27437563322873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145807851/5000000000 : ℝ)|^539 ≤ (32976601812387/100000000000000 : ℝ)^411
        have hw : |(2145807851/5000000000 : ℝ)|=(2145807851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1233260379/2500000000 : ℝ)|^539 ≤ (39585834848521/100000000000000 : ℝ)^411
        have hw : |(1233260379/2500000000 : ℝ)|=(1233260379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1457087/3906250 : ℝ)|^539 ≤ (27437563322873/100000000000000 : ℝ)^411
        have hw : |(1457087/3906250 : ℝ)|=(1457087/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1352_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1489/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3491/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19387/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26799/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1489/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26799/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1489/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26799/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1489/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26799/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1489/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26799/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1489/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26799/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1489/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1489/100000 : ℝ) ^ (4311/1024 : ℝ) ≤ (1016080351307/50000000000000000000 : ℝ) := by
    have hpowers : (1489/100000 : ℝ)^4311 ≤ (1016080351307/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1489 : ℕ)^4311*50000000000000000000^1024 ≤ 1016080351307^1024*100000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1489 100000 1016080351307 50000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1489/100000 : ℝ)) (X := (1016080351307/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26799/100000 : ℝ) ^ (4311/1024 : ℝ) ≤ (78240495689653027/20000000000000000000 : ℝ) := by
    have hpowers : (26799/100000 : ℝ)^4311 ≤ (78240495689653027/20000000000000000000 : ℝ)^1024 := by
      have hnat : (26799 : ℕ)^4311*20000000000000000000^1024 ≤ 78240495689653027^1024*100000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26799 100000 78240495689653027 20000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26799/100000 : ℝ)) (X := (78240495689653027/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000001016080351307/25000000000000000000 : ℝ) ≤ (2500000024135149/2500000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (25000001016080351307/25000000000000000000 : ℝ)^1024 ≤ (2500000024135149/2500000000000000 : ℝ)^4311 := by
      have hnat : (25000001016080351307 : ℕ)^1024*2500000000000000^4311 ≤ 2500000024135149^4311*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000001016080351307 25000000000000000000 2500000024135149 2500000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000024135149/2500000000000000 : ℝ)) (X := (25000001016080351307/25000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100391204510608967749/100000000000000000000 : ℝ) ≤ (5004639263991147/5000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (100391204510608967749/100000000000000000000 : ℝ)^1024 ≤ (5004639263991147/5000000000000000 : ℝ)^4311 := by
      have hnat : (100391204510608967749 : ℕ)^1024*5000000000000000^4311 ≤ 5004639263991147^4311*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100391204510608967749 100000000000000000000 5004639263991147 5000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004639263991147/5000000000000000 : ℝ)) (X := (100391204510608967749/100000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10078240495689653027/10000000000000000000 : ℝ) ≤ (1252319619927999/1250000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (10078240495689653027/10000000000000000000 : ℝ)^1024 ≤ (1252319619927999/1250000000000000 : ℝ)^4311 := by
      have hnat : (10078240495689653027 : ℕ)^1024*1250000000000000^4311 ≤ 1252319619927999^4311*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10078240495689653027 10000000000000000000 1252319619927999 1250000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252319619927999/1250000000000000 : ℝ)) (X := (10078240495689653027/10000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1016080351307/50000000000000000000 : ℝ) ≤ ((63268092818652277029/63275000000000000000 : ℝ)+2*(4639215720849/1265500000000000 : ℝ)*(1489/100000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (63268092818652277029/63275000000000000000 : ℝ)+2*(4639215720849/1265500000000000 : ℝ)*(1489/100000 : ℝ)=(2500000024135149/2500000000000000 : ℝ) by norm_num, show 1+2*(1016080351307/50000000000000000000 : ℝ)=(25000001016080351307/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78240495689653027/20000000000000000000 : ℝ)+(1016080351307/50000000000000000000 : ℝ) ≤ ((63268092818652277029/63275000000000000000 : ℝ)+(4639215720849/1265500000000000 : ℝ)*((26799/100000 : ℝ)+(1489/100000 : ℝ)))^(4311/1024 : ℝ) := by
    rw [show (63268092818652277029/63275000000000000000 : ℝ)+(4639215720849/1265500000000000 : ℝ)*((26799/100000 : ℝ)+(1489/100000 : ℝ))=(5004639263991147/5000000000000000 : ℝ) by norm_num, show 1+(78240495689653027/20000000000000000000 : ℝ)+(1016080351307/50000000000000000000 : ℝ)=(100391204510608967749/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78240495689653027/20000000000000000000 : ℝ) ≤ ((63268092818652277029/63275000000000000000 : ℝ)+2*(4639215720849/1265500000000000 : ℝ)*(26799/100000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (63268092818652277029/63275000000000000000 : ℝ)+2*(4639215720849/1265500000000000 : ℝ)*(26799/100000 : ℝ)=(1252319619927999/1250000000000000 : ℝ) by norm_num, show 1+2*(78240495689653027/20000000000000000000 : ℝ)=(10078240495689653027/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63268092818652277029/63275000000000000000 : ℝ)*(X 1 0+X 2 0)+(4639215720849/1265500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (1489/100000 : ℝ)) (hi := (26799/100000 : ℝ)) (c := (63268092818652277029/63275000000000000000 : ℝ)) (alpha := (4639215720849/1265500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63268092818652277029/63275000000000000000 : ℝ)*(X 0 1+X 2 1)+(4639215720849/1265500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (1489/100000 : ℝ)) (hi := (26799/100000 : ℝ)) (c := (63268092818652277029/63275000000000000000 : ℝ)) (alpha := (4639215720849/1265500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63268092818652277029/63275000000000000000 : ℝ)*(X 0 2+X 1 2)+(4639215720849/1265500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (1489/100000 : ℝ)) (hi := (26799/100000 : ℝ)) (c := (63268092818652277029/63275000000000000000 : ℝ)) (alpha := (4639215720849/1265500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1986625367/10000000000 : ℝ)*X 0 0+(1127533901/2000000000 : ℝ)*X 0 1+(1010156493/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5404674583/10000000000 : ℝ)*X 1 0+(-1149767607/5000000000 : ℝ)*X 1 1+(1262695743/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1351168641/2500000000 : ℝ)*X 2 0+(5050782547/10000000000 : ℝ)*X 2 1+(-2299535783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4290525043/10000000000 : ℝ)*X 0 0+(371450331/1000000000 : ℝ)*X 0 1+(4948404603/10000000000 : ℝ)*X 0 2+(4290525043/10000000000 : ℝ)*X 1 0+(371450331/1000000000 : ℝ)*X 1 1+(4948404603/10000000000 : ℝ)*X 1 2+(4290525043/10000000000 : ℝ)*X 2 0+(371450331/1000000000 : ℝ)*X 2 1+(4948404603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-248392989/1250000000 : ℝ)*X 0 0+(316130633/625000000 : ℝ)*X 0 1+(5630229931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252259107/10000000000 : ℝ)*X 1 0+(-430022011/2500000000 : ℝ)*X 1 1+(5630229983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252259003/10000000000 : ℝ)*X 2 0+(2815115029/5000000000 : ℝ)*X 2 1+(-1720088083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2145807851/5000000000 : ℝ)*X 0 0+(1233260379/2500000000 : ℝ)*X 0 1+(1457087/3906250 : ℝ)*X 0 2+(2145807851/5000000000 : ℝ)*X 1 0+(1233260379/2500000000 : ℝ)*X 1 1+(1457087/3906250 : ℝ)*X 1 2+(2145807851/5000000000 : ℝ)*X 2 0+(1233260379/2500000000 : ℝ)*X 2 1+(1457087/3906250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3542813142651367668647446089/395468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40039443/100000000000000 : ℝ)*(base1) + (1466968749/100000000000000 : ℝ)*(base19) + (365244661/25000000000000 : ℝ)*(base23) + (54655387/20000000000000 : ℝ)*(upper3) + (7193697/20000000000000 : ℝ)*(upper5) + (314296466092547/25000000000000 : ℝ)*(major0) + (314296466092547/25000000000000 : ℝ)*(major1) + (314296466092547/25000000000000 : ℝ)*(major2) + (1703916895257791/100000000000000 : ℝ)*(sp0) + (1703924343741739/100000000000000 : ℝ)*(sp1) + (1703924349731843/100000000000000 : ℝ)*(sp2) + (810440967557967/100000000000000 : ℝ)*(sp3) + (447774607/5000000000000 : ℝ)*(sp4) + (461181527/10000000000000 : ℝ)*(sp7) + (810445619412681/100000000000000 : ℝ)*(f.failure) + (212990726338811/12500000000000 : ℝ)*(f.sum) + (59345375815753/15818750000000000000000000000 : ℝ)*base65 + (4097494165030522137/1581875000000000000000000000000000 : ℝ)*base68 + (3752734302168647137/1581875000000000000000000000000000 : ℝ)*base70 + (5992547975519897137/1581875000000000000000000000000000 : ℝ)*base72 + (29830407217003/15818750000000000000000000000 : ℝ)*base73 + (10406402932320522137/1581875000000000000000000000000000 : ℝ)*base76 + (6298516792748022137/1581875000000000000000000000000000 : ℝ)*base78 + (4437375176140727863/1581875000000000000000000000000000 : ℝ)*base79 + (17248244841203/15818750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (57512671/10000000000000000000000 : ℝ)*base89 + (57512671/10000000000000000000000 : ℝ)*base91 + (57512671/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27724737219602122458313585323/3163750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94923719/100000000000000 : ℝ)*(base1) + (892952897/50000000000000 : ℝ)*(base19) + (874426491/50000000000000 : ℝ)*(base23) + (50705711/25000000000000 : ℝ)*(upper3) + (96963491/50000000000000 : ℝ)*(upper5) + (1289574901377429/100000000000000 : ℝ)*(major0) + (1289574901377429/100000000000000 : ℝ)*(major1) + (1289574901377429/100000000000000 : ℝ)*(major2) + (920224551/10000000000000 : ℝ)*(sp1) + (9118013871/100000000000000 : ℝ)*(sp2) + (1747824374078299/100000000000000 : ℝ)*(sp4) + (436953322750819/25000000000000 : ℝ)*(sp5) + (1747813412287727/100000000000000 : ℝ)*(sp6) + (83132513656817/10000000000000 : ℝ)*(sp7) + (831325231491889/100000000000000 : ℝ)*(f.failure) + (87391213957729/5000000000000 : ℝ)*(f.sum) + (102366689336921/63275000000000000000000000000 : ℝ)*base65 + (30075639030876828441/6327500000000000000000000000000000 : ℝ)*base67 + (30701971238090671559/6327500000000000000000000000000000 : ℝ)*base70 + (25078863932898171559/6327500000000000000000000000000000 : ℝ)*base72 + (346159899629321/63275000000000000000000000000 : ℝ)*base73 + (269940087913171559/6327500000000000000000000000000000 : ℝ)*base76 + (1532534739719328441/6327500000000000000000000000000000 : ℝ)*base77 + (12822756626025671559/6327500000000000000000000000000000 : ℝ)*base80 + (124048940583929/63275000000000000000000000000 : ℝ)*base82 + (15542199/10000000000000000000000 : ℝ)*base89 + (15542199/10000000000000000000000 : ℝ)*base91 + (15542199/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1352_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1489/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3491/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19387/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1352_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1352_s2_0 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-506478409/2500000000 : ℝ)*x 0 + (5477045637/10000000000 : ℝ)*x 1 + (5186225753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (506478409/2500000000 : ℝ)^539 ≤ (1540238824863/12500000000000 : ℝ)^411 := by
    have hnat : (506478409 : ℕ)^539*12500000000000^411 ≤ 1540238824863^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506478409 2500000000 1540238824863 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477045637/10000000000 : ℝ)^539 ≤ (45406748969523/100000000000000 : ℝ)^411 := by
    have hnat : (5477045637 : ℕ)^539*100000000000000^411 ≤ 45406748969523^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477045637 10000000000 45406748969523 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5186225753/10000000000 : ℝ)^539 ≤ (21135670206507/50000000000000 : ℝ)^411 := by
    have hnat : (5186225753 : ℕ)^539*50000000000000^411 ≤ 21135670206507^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186225753 10000000000 21135670206507 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-506478409/2500000000 : ℝ), (5477045637/10000000000 : ℝ), (5186225753/10000000000 : ℝ)] ![(1540238824863/12500000000000 : ℝ), (45406748969523/100000000000000 : ℝ), (21135670206507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-506478409/2500000000 : ℝ)|^539 ≤ (1540238824863/12500000000000 : ℝ)^411
        have hw : |(-506478409/2500000000 : ℝ)|=(506478409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477045637/10000000000 : ℝ)|^539 ≤ (45406748969523/100000000000000 : ℝ)^411
        have hw : |(5477045637/10000000000 : ℝ)|=(5477045637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5186225753/10000000000 : ℝ)|^539 ≤ (21135670206507/50000000000000 : ℝ)^411
        have hw : |(5186225753/10000000000 : ℝ)|=(5186225753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s2_1 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (167664187/312500000 : ℝ)*x 0 + (-272012601/1250000000 : ℝ)*x 1 + (2593113069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167664187/312500000 : ℝ)^539 ≤ (44195199114879/100000000000000 : ℝ)^411 := by
    have hnat : (167664187 : ℕ)^539*100000000000000^411 ≤ 44195199114879^411*312500000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167664187 312500000 44195199114879 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272012601/1250000000 : ℝ)^539 ≤ (845841021391/6250000000000 : ℝ)^411 := by
    have hnat : (272012601 : ℕ)^539*6250000000000^411 ≤ 845841021391^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272012601 1250000000 845841021391 6250000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2593113069/5000000000 : ℝ)^539 ≤ (42271344528321/100000000000000 : ℝ)^411 := by
    have hnat : (2593113069 : ℕ)^539*100000000000000^411 ≤ 42271344528321^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593113069 5000000000 42271344528321 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167664187/312500000 : ℝ), (-272012601/1250000000 : ℝ), (2593113069/5000000000 : ℝ)] ![(44195199114879/100000000000000 : ℝ), (845841021391/6250000000000 : ℝ), (42271344528321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167664187/312500000 : ℝ)|^539 ≤ (44195199114879/100000000000000 : ℝ)^411
        have hw : |(167664187/312500000 : ℝ)|=(167664187/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-272012601/1250000000 : ℝ)|^539 ≤ (845841021391/6250000000000 : ℝ)^411
        have hw : |(-272012601/1250000000 : ℝ)|=(272012601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2593113069/5000000000 : ℝ)|^539 ≤ (42271344528321/100000000000000 : ℝ)^411
        have hw : |(2593113069/5000000000 : ℝ)|=(2593113069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s2_2 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (670656757/1250000000 : ℝ)*x 0 + (2593113027/5000000000 : ℝ)*x 1 + (-1088050411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670656757/1250000000 : ℝ)^539 ≤ (690549998323/1562500000000 : ℝ)^411 := by
    have hnat : (670656757 : ℕ)^539*1562500000000^411 ≤ 690549998323^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670656757 1250000000 690549998323 1562500000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593113027/5000000000 : ℝ)^539 ≤ (10567835907609/25000000000000 : ℝ)^411 := by
    have hnat : (2593113027 : ℕ)^539*25000000000000^411 ≤ 10567835907609^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593113027 5000000000 10567835907609 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088050411/5000000000 : ℝ)^539 ≤ (338336411411/2500000000000 : ℝ)^411 := by
    have hnat : (1088050411 : ℕ)^539*2500000000000^411 ≤ 338336411411^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088050411 5000000000 338336411411 2500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670656757/1250000000 : ℝ), (2593113027/5000000000 : ℝ), (-1088050411/5000000000 : ℝ)] ![(690549998323/1562500000000 : ℝ), (10567835907609/25000000000000 : ℝ), (338336411411/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670656757/1250000000 : ℝ)|^539 ≤ (690549998323/1562500000000 : ℝ)^411
        have hw : |(670656757/1250000000 : ℝ)|=(670656757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593113027/5000000000 : ℝ)|^539 ≤ (10567835907609/25000000000000 : ℝ)^411
        have hw : |(2593113027/5000000000 : ℝ)|=(2593113027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088050411/5000000000 : ℝ)|^539 ≤ (338336411411/2500000000000 : ℝ)^411
        have hw : |(-1088050411/5000000000 : ℝ)|=(1088050411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s2_3 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4318030451/10000000000 : ℝ)*x 0 + (2011178773/5000000000 : ℝ)*x 1 + (57922409/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318030451/10000000000 : ℝ)^539 ≤ (33243038462739/100000000000000 : ℝ)^411 := by
    have hnat : (4318030451 : ℕ)^539*100000000000000^411 ≤ 33243038462739^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318030451 10000000000 33243038462739 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011178773/5000000000 : ℝ)^539 ≤ (473284116321/1562500000000 : ℝ)^411 := by
    have hnat : (2011178773 : ℕ)^539*1562500000000^411 ≤ 473284116321^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011178773 5000000000 473284116321 1562500000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57922409/125000000 : ℝ)^539 ≤ (3646677807631/10000000000000 : ℝ)^411 := by
    have hnat : (57922409 : ℕ)^539*10000000000000^411 ≤ 3646677807631^411*125000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57922409 125000000 3646677807631 10000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318030451/10000000000 : ℝ), (2011178773/5000000000 : ℝ), (57922409/125000000 : ℝ)] ![(33243038462739/100000000000000 : ℝ), (473284116321/1562500000000 : ℝ), (3646677807631/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318030451/10000000000 : ℝ)|^539 ≤ (33243038462739/100000000000000 : ℝ)^411
        have hw : |(4318030451/10000000000 : ℝ)|=(4318030451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2011178773/5000000000 : ℝ)|^539 ≤ (473284116321/1562500000000 : ℝ)^411
        have hw : |(2011178773/5000000000 : ℝ)|=(2011178773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(57922409/125000000 : ℝ)|^539 ≤ (3646677807631/10000000000000 : ℝ)^411
        have hw : |(57922409/125000000 : ℝ)|=(57922409/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s2_4 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-253247093/1250000000 : ℝ)*x 0 + (1037606029/2000000000 : ℝ)*x 1 + (5475225157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253247093/1250000000 : ℝ)^539 ≤ (12322413972687/100000000000000 : ℝ)^411 := by
    have hnat : (253247093 : ℕ)^539*100000000000000^411 ≤ 12322413972687^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253247093 1250000000 12322413972687 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037606029/2000000000 : ℝ)^539 ≤ (42290628802393/100000000000000 : ℝ)^411 := by
    have hnat : (1037606029 : ℕ)^539*100000000000000^411 ≤ 42290628802393^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037606029 2000000000 42290628802393 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475225157/10000000000 : ℝ)^539 ≤ (45386957209173/100000000000000 : ℝ)^411 := by
    have hnat : (5475225157 : ℕ)^539*100000000000000^411 ≤ 45386957209173^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475225157 10000000000 45386957209173 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-253247093/1250000000 : ℝ), (1037606029/2000000000 : ℝ), (5475225157/10000000000 : ℝ)] ![(12322413972687/100000000000000 : ℝ), (42290628802393/100000000000000 : ℝ), (45386957209173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-253247093/1250000000 : ℝ)|^539 ≤ (12322413972687/100000000000000 : ℝ)^411
        have hw : |(-253247093/1250000000 : ℝ)|=(253247093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037606029/2000000000 : ℝ)|^539 ≤ (42290628802393/100000000000000 : ℝ)^411
        have hw : |(1037606029/2000000000 : ℝ)|=(1037606029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475225157/10000000000 : ℝ)|^539 ≤ (45386957209173/100000000000000 : ℝ)^411
        have hw : |(5475225157/10000000000 : ℝ)|=(5475225157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s2_5 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (165319201/312500000 : ℝ)*x 0 + (-471775373/2500000000 : ℝ)*x 1 + (5475225131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165319201/312500000 : ℝ)^539 ≤ (43386341567507/100000000000000 : ℝ)^411 := by
    have hnat : (165319201 : ℕ)^539*100000000000000^411 ≤ 43386341567507^411*312500000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165319201 312500000 43386341567507 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471775373/2500000000 : ℝ)^539 ≤ (2245340298579/20000000000000 : ℝ)^411 := by
    have hnat : (471775373 : ℕ)^539*20000000000000^411 ≤ 2245340298579^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471775373 2500000000 2245340298579 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475225131/10000000000 : ℝ)^539 ≤ (45386956926523/100000000000000 : ℝ)^411 := by
    have hnat : (5475225131 : ℕ)^539*100000000000000^411 ≤ 45386956926523^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475225131 10000000000 45386956926523 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165319201/312500000 : ℝ), (-471775373/2500000000 : ℝ), (5475225131/10000000000 : ℝ)] ![(43386341567507/100000000000000 : ℝ), (2245340298579/20000000000000 : ℝ), (45386956926523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165319201/312500000 : ℝ)|^539 ≤ (43386341567507/100000000000000 : ℝ)^411
        have hw : |(165319201/312500000 : ℝ)|=(165319201/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-471775373/2500000000 : ℝ)|^539 ≤ (2245340298579/20000000000000 : ℝ)^411
        have hw : |(-471775373/2500000000 : ℝ)|=(471775373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475225131/10000000000 : ℝ)|^539 ≤ (45386956926523/100000000000000 : ℝ)^411
        have hw : |(5475225131/10000000000 : ℝ)|=(5475225131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s2_6 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (264510721/500000000 : ℝ)*x 0 + (5475225163/10000000000 : ℝ)*x 1 + (-235887683/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264510721/500000000 : ℝ)^539 ≤ (43386341438443/100000000000000 : ℝ)^411 := by
    have hnat : (264510721 : ℕ)^539*100000000000000^411 ≤ 43386341438443^411*500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264510721 500000000 43386341438443 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475225163/10000000000 : ℝ)^539 ≤ (56733696593/125000000000 : ℝ)^411 := by
    have hnat : (5475225163 : ℕ)^539*125000000000^411 ≤ 56733696593^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475225163 10000000000 56733696593 125000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235887683/1250000000 : ℝ)^539 ≤ (280667531861/2500000000000 : ℝ)^411 := by
    have hnat : (235887683 : ℕ)^539*2500000000000^411 ≤ 280667531861^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235887683 1250000000 280667531861 2500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264510721/500000000 : ℝ), (5475225163/10000000000 : ℝ), (-235887683/1250000000 : ℝ)] ![(43386341438443/100000000000000 : ℝ), (56733696593/125000000000 : ℝ), (280667531861/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264510721/500000000 : ℝ)|^539 ≤ (43386341438443/100000000000000 : ℝ)^411
        have hw : |(264510721/500000000 : ℝ)|=(264510721/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475225163/10000000000 : ℝ)|^539 ≤ (56733696593/125000000000 : ℝ)^411
        have hw : |(5475225163/10000000000 : ℝ)|=(5475225163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-235887683/1250000000 : ℝ)|^539 ≤ (280667531861/2500000000000 : ℝ)^411
        have hw : |(-235887683/1250000000 : ℝ)|=(235887683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s2_7 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2159081731/5000000000 : ℝ)*x 0 + (14468749/31250000 : ℝ)*x 1 + (402618443/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159081731/5000000000 : ℝ)^539 ≤ (33244381387237/100000000000000 : ℝ)^411 := by
    have hnat : (2159081731 : ℕ)^539*100000000000000^411 ≤ 33244381387237^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159081731 5000000000 33244381387237 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14468749/31250000 : ℝ)^539 ≤ (36427636367107/100000000000000 : ℝ)^411 := by
    have hnat : (14468749 : ℕ)^539*100000000000000^411 ≤ 36427636367107^411*31250000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14468749 31250000 36427636367107 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402618443/1000000000 : ℝ)^539 ≤ (15163991112799/50000000000000 : ℝ)^411 := by
    have hnat : (402618443 : ℕ)^539*50000000000000^411 ≤ 15163991112799^411*1000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402618443 1000000000 15163991112799 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159081731/5000000000 : ℝ), (14468749/31250000 : ℝ), (402618443/1000000000 : ℝ)] ![(33244381387237/100000000000000 : ℝ), (36427636367107/100000000000000 : ℝ), (15163991112799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159081731/5000000000 : ℝ)|^539 ≤ (33244381387237/100000000000000 : ℝ)^411
        have hw : |(2159081731/5000000000 : ℝ)|=(2159081731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14468749/31250000 : ℝ)|^539 ≤ (36427636367107/100000000000000 : ℝ)^411
        have hw : |(14468749/31250000 : ℝ)|=(14468749/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(402618443/1000000000 : ℝ)|^539 ≤ (15163991112799/50000000000000 : ℝ)^411
        have hw : |(402618443/1000000000 : ℝ)|=(402618443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1352_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2479/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3213/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19387/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19387/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19387/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19387/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19387/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19387/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3491/50000 : ℝ) ^ (4311/1024 : ℝ) ≤ (1358940062989779/100000000000000000000 : ℝ) := by
    have hpowers : (3491/50000 : ℝ)^4311 ≤ (1358940062989779/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3491 : ℕ)^4311*100000000000000000000^1024 ≤ 1358940062989779^1024*50000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3491 50000 1358940062989779 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3491/50000 : ℝ)) (X := (1358940062989779/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19387/100000 : ℝ) ^ (4311/1024 : ℝ) ≤ (20020618803506519/20000000000000000000 : ℝ) := by
    have hpowers : (19387/100000 : ℝ)^4311 ≤ (20020618803506519/20000000000000000000 : ℝ)^1024 := by
      have hnat : (19387 : ℕ)^4311*20000000000000000000^1024 ≤ 20020618803506519^1024*100000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19387 100000 20020618803506519 20000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19387/100000 : ℝ)) (X := (20020618803506519/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001358940062989779/50000000000000000000 : ℝ) ≤ (10000064557652803/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50001358940062989779/50000000000000000000 : ℝ)^1024 ≤ (10000064557652803/10000000000000000 : ℝ)^4311 := by
      have hnat : (50001358940062989779 : ℕ)^1024*10000000000000000^4311 ≤ 10000064557652803^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001358940062989779 50000000000000000000 10000064557652803 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000064557652803/10000000000000000 : ℝ)) (X := (50001358940062989779/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50050731017040261187/50000000000000000000 : ℝ) ≤ (2500602278813599/2500000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50050731017040261187/50000000000000000000 : ℝ)^1024 ≤ (2500602278813599/2500000000000000 : ℝ)^4311 := by
      have hnat : (50050731017040261187 : ℕ)^1024*2500000000000000^4311 ≤ 2500602278813599^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50050731017040261187 50000000000000000000 2500602278813599 2500000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500602278813599/2500000000000000 : ℝ)) (X := (50050731017040261187/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10020020618803506519/10000000000000000000 : ℝ) ≤ (10004753672855989/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (10020020618803506519/10000000000000000000 : ℝ)^1024 ≤ (10004753672855989/10000000000000000 : ℝ)^4311 := by
      have hnat : (10020020618803506519 : ℕ)^1024*10000000000000000^4311 ≤ 10004753672855989^4311*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10020020618803506519 10000000000000000000 10004753672855989 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004753672855989/10000000000000000 : ℝ)) (X := (10020020618803506519/10000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1358940062989779/100000000000000000000 : ℝ) ≤ ((41339353811778125521/41350000000000000000 : ℝ)+2*(781519200531/413500000000000 : ℝ)*(3491/50000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (41339353811778125521/41350000000000000000 : ℝ)+2*(781519200531/413500000000000 : ℝ)*(3491/50000 : ℝ)=(10000064557652803/10000000000000000 : ℝ) by norm_num, show 1+2*(1358940062989779/100000000000000000000 : ℝ)=(50001358940062989779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20020618803506519/20000000000000000000 : ℝ)+(1358940062989779/100000000000000000000 : ℝ) ≤ ((41339353811778125521/41350000000000000000 : ℝ)+(781519200531/413500000000000 : ℝ)*((19387/100000 : ℝ)+(3491/50000 : ℝ)))^(4311/1024 : ℝ) := by
    rw [show (41339353811778125521/41350000000000000000 : ℝ)+(781519200531/413500000000000 : ℝ)*((19387/100000 : ℝ)+(3491/50000 : ℝ))=(2500602278813599/2500000000000000 : ℝ) by norm_num, show 1+(20020618803506519/20000000000000000000 : ℝ)+(1358940062989779/100000000000000000000 : ℝ)=(50050731017040261187/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20020618803506519/20000000000000000000 : ℝ) ≤ ((41339353811778125521/41350000000000000000 : ℝ)+2*(781519200531/413500000000000 : ℝ)*(19387/100000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (41339353811778125521/41350000000000000000 : ℝ)+2*(781519200531/413500000000000 : ℝ)*(19387/100000 : ℝ)=(10004753672855989/10000000000000000 : ℝ) by norm_num, show 1+2*(20020618803506519/20000000000000000000 : ℝ)=(10020020618803506519/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41339353811778125521/41350000000000000000 : ℝ)*(X 1 0+X 2 0)+(781519200531/413500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (3491/50000 : ℝ)) (hi := (19387/100000 : ℝ)) (c := (41339353811778125521/41350000000000000000 : ℝ)) (alpha := (781519200531/413500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41339353811778125521/41350000000000000000 : ℝ)*(X 0 1+X 2 1)+(781519200531/413500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (3491/50000 : ℝ)) (hi := (19387/100000 : ℝ)) (c := (41339353811778125521/41350000000000000000 : ℝ)) (alpha := (781519200531/413500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41339353811778125521/41350000000000000000 : ℝ)*(X 0 2+X 1 2)+(781519200531/413500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (3491/50000 : ℝ)) (hi := (19387/100000 : ℝ)) (c := (41339353811778125521/41350000000000000000 : ℝ)) (alpha := (781519200531/413500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-506478409/2500000000 : ℝ)*X 0 0+(5477045637/10000000000 : ℝ)*X 0 1+(5186225753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167664187/312500000 : ℝ)*X 1 0+(-272012601/1250000000 : ℝ)*X 1 1+(2593113069/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((670656757/1250000000 : ℝ)*X 2 0+(2593113027/5000000000 : ℝ)*X 2 1+(-1088050411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318030451/10000000000 : ℝ)*X 0 0+(2011178773/5000000000 : ℝ)*X 0 1+(57922409/125000000 : ℝ)*X 0 2+(4318030451/10000000000 : ℝ)*X 1 0+(2011178773/5000000000 : ℝ)*X 1 1+(57922409/125000000 : ℝ)*X 1 2+(4318030451/10000000000 : ℝ)*X 2 0+(2011178773/5000000000 : ℝ)*X 2 1+(57922409/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-253247093/1250000000 : ℝ)*X 0 0+(1037606029/2000000000 : ℝ)*X 0 1+(5475225157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165319201/312500000 : ℝ)*X 1 0+(-471775373/2500000000 : ℝ)*X 1 1+(5475225131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264510721/500000000 : ℝ)*X 2 0+(5475225163/10000000000 : ℝ)*X 2 1+(-235887683/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159081731/5000000000 : ℝ)*X 0 0+(14468749/31250000 : ℝ)*X 0 1+(402618443/1000000000 : ℝ)*X 0 2+(2159081731/5000000000 : ℝ)*X 1 0+(14468749/31250000 : ℝ)*X 1 1+(402618443/1000000000 : ℝ)*X 1 2+(2159081731/5000000000 : ℝ)*X 2 0+(14468749/31250000 : ℝ)*X 2 1+(402618443/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1361879517240400124451920739/129218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (936888039/50000000000000 : ℝ)*(base19) + (923204461/50000000000000 : ℝ)*(base23) + (4930143/12500000000000 : ℝ)*(lower2) + (50804463/20000000000000 : ℝ)*(upper3) + (191905947/100000000000000 : ℝ)*(upper5) + (317133088725853/12500000000000 : ℝ)*(major0) + (317133088725853/12500000000000 : ℝ)*(major1) + (317133088725853/12500000000000 : ℝ)*(major2) + (214911361475773/6250000000000 : ℝ)*(sp0) + (3438606911883499/100000000000000 : ℝ)*(sp1) + (687721387850131/20000000000000 : ℝ)*(sp2) + (817753911301921/50000000000000 : ℝ)*(sp3) + (27002047209/100000000000000 : ℝ)*(sp4) + (12460039103/100000000000000 : ℝ)*(sp7) + (327104056528589/20000000000000 : ℝ)*(f.failure) + (3438608785659577/100000000000000 : ℝ)*(f.sum) + (939090191291/1292187500000000000000000000 : ℝ)*base66 + (2427302390433280587/516875000000000000000000000000000 : ℝ)*base68 + (3166440852907030587/516875000000000000000000000000000 : ℝ)*base70 + (3802822985293905587/516875000000000000000000000000000 : ℝ)*base72 + (27767215951761/5168750000000000000000000000 : ℝ)*base73 + (2097751694896094413/516875000000000000000000000000000 : ℝ)*base75 + (5035981635998905587/516875000000000000000000000000000 : ℝ)*base78 + (845050661510155587/516875000000000000000000000000000 : ℝ)*base80 + (1597604325233/646093750000000000000000000 : ℝ)*base82 + (16971899/2000000000000000000000 : ℝ)*base89 + (16971899/2000000000000000000000 : ℝ)*base91 + (16971899/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8720200065161853238053/1292187500000000000000000000 : ℝ) := by norm_num
    linear_combination (1405106637/100000000000000 : ℝ)*(base19) + (783553619/50000000000000 : ℝ)*(base23) + (41566603/25000000000000 : ℝ)*(upper3) + (67969979/100000000000000 : ℝ)*(lower4) + (26449623/25000000000000 : ℝ)*(upper5) + (1284522181664443/50000000000000 : ℝ)*(major0) + (1284522181664443/50000000000000 : ℝ)*(major1) + (1284522181664443/50000000000000 : ℝ)*(major2) + (1991614341/12500000000000 : ℝ)*(sp1) + (9426353773/50000000000000 : ℝ)*(sp2) + (3481952516297477/100000000000000 : ℝ)*(sp4) + (217620948642257/6250000000000 : ℝ)*(sp5) + (1740966048241347/50000000000000 : ℝ)*(sp6) + (414033996353393/25000000000000 : ℝ)*(sp7) + (414033996353393/25000000000000 : ℝ)*(f.failure) + (3481952516297477/100000000000000 : ℝ)*(f.sum) + (43985277430167/10337500000000000000000000000 : ℝ)*base66 + (4259191659657650197/2067500000000000000000000000000000 : ℝ)*base68 + (21349252600972349803/2067500000000000000000000000000000 : ℝ)*base69 + (1654410176220150197/2067500000000000000000000000000000 : ℝ)*base72 + (49228108601567/10337500000000000000000000000 : ℝ)*base74 + (17230581205299849803/2067500000000000000000000000000000 : ℝ)*base75 + (8434929204679849803/2067500000000000000000000000000000 : ℝ)*base77 + (2247490261425150197/2067500000000000000000000000000000 : ℝ)*base80 + (63096897317183/10337500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5520137/2500000000000000000000 : ℝ)*base90 + (5520137/2500000000000000000000 : ℝ)*base92 + (5520137/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1352_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2479/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1352_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1352_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2479/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1352_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1352_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1352_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2479/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1352_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
