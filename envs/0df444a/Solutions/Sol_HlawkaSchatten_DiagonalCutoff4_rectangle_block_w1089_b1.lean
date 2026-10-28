-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1089_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:56:24.55898+00:00
-- url     : https://prove2.me/submissions/10005e04-b075-42c1-a3d2-09fa8c8025e8

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
theorem support_rectangle_w1089_s3_0 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188059819/10000000000 : ℝ)*x 0 + (2717447769/5000000000 : ℝ)*x 1 + (5226825467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188059819/10000000000 : ℝ)^4141 ≤ (6640866833807/50000000000000 : ℝ)^3117 := by
    have hnat : (2188059819 : ℕ)^4141*50000000000000^3117 ≤ 6640866833807^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188059819 10000000000 6640866833807 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717447769/5000000000 : ℝ)^4141 ≤ (44483192252847/100000000000000 : ℝ)^3117 := by
    have hnat : (2717447769 : ℕ)^4141*100000000000000^3117 ≤ 44483192252847^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717447769 5000000000 44483192252847 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226825467/10000000000 : ℝ)^4141 ≤ (8447014812419/20000000000000 : ℝ)^3117 := by
    have hnat : (5226825467 : ℕ)^4141*20000000000000^3117 ≤ 8447014812419^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226825467 10000000000 8447014812419 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188059819/10000000000 : ℝ), (2717447769/5000000000 : ℝ), (5226825467/10000000000 : ℝ)] ![(6640866833807/50000000000000 : ℝ), (44483192252847/100000000000000 : ℝ), (8447014812419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188059819/10000000000 : ℝ)|^4141 ≤ (6640866833807/50000000000000 : ℝ)^3117
        have hw : |(-2188059819/10000000000 : ℝ)|=(2188059819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717447769/5000000000 : ℝ)|^4141 ≤ (44483192252847/100000000000000 : ℝ)^3117
        have hw : |(2717447769/5000000000 : ℝ)|=(2717447769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226825467/10000000000 : ℝ)|^4141 ≤ (8447014812419/20000000000000 : ℝ)^3117
        have hw : |(5226825467/10000000000 : ℝ)|=(5226825467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s3_1 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677551203/5000000000 : ℝ)*x 0 + (-2294548083/10000000000 : ℝ)*x 1 + (522682539/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677551203/5000000000 : ℝ)^4141 ≤ (21808826668577/50000000000000 : ℝ)^3117 := by
    have hnat : (2677551203 : ℕ)^4141*50000000000000^3117 ≤ 21808826668577^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677551203 5000000000 21808826668577 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2294548083/10000000000 : ℝ)^4141 ≤ (282945468177/2000000000000 : ℝ)^3117 := by
    have hnat : (2294548083 : ℕ)^4141*2000000000000^3117 ≤ 282945468177^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294548083 10000000000 282945468177 2000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522682539/1000000000 : ℝ)^4141 ≤ (42235073235497/100000000000000 : ℝ)^3117 := by
    have hnat : (522682539 : ℕ)^4141*100000000000000^3117 ≤ 42235073235497^3117*1000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522682539 1000000000 42235073235497 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677551203/5000000000 : ℝ), (-2294548083/10000000000 : ℝ), (522682539/1000000000 : ℝ)] ![(21808826668577/50000000000000 : ℝ), (282945468177/2000000000000 : ℝ), (42235073235497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677551203/5000000000 : ℝ)|^4141 ≤ (21808826668577/50000000000000 : ℝ)^3117
        have hw : |(2677551203/5000000000 : ℝ)|=(2677551203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2294548083/10000000000 : ℝ)|^4141 ≤ (282945468177/2000000000000 : ℝ)^3117
        have hw : |(-2294548083/10000000000 : ℝ)|=(2294548083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522682539/1000000000 : ℝ)|^4141 ≤ (42235073235497/100000000000000 : ℝ)^3117
        have hw : |(522682539/1000000000 : ℝ)|=(522682539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s3_2 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677551151/5000000000 : ℝ)*x 0 + (2613412913/5000000000 : ℝ)*x 1 + (-2294547649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677551151/5000000000 : ℝ)^4141 ≤ (43617652211781/100000000000000 : ℝ)^3117 := by
    have hnat : (2677551151 : ℕ)^4141*100000000000000^3117 ≤ 43617652211781^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677551151 5000000000 43617652211781 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613412913/5000000000 : ℝ)^4141 ≤ (1689403116639/4000000000000 : ℝ)^3117 := by
    have hnat : (2613412913 : ℕ)^4141*4000000000000^3117 ≤ 1689403116639^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613412913 5000000000 1689403116639 4000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2294547649/10000000000 : ℝ)^4141 ≤ (7073634926949/50000000000000 : ℝ)^3117 := by
    have hnat : (2294547649 : ℕ)^4141*50000000000000^3117 ≤ 7073634926949^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294547649 10000000000 7073634926949 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677551151/5000000000 : ℝ), (2613412913/5000000000 : ℝ), (-2294547649/10000000000 : ℝ)] ![(43617652211781/100000000000000 : ℝ), (1689403116639/4000000000000 : ℝ), (7073634926949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677551151/5000000000 : ℝ)|^4141 ≤ (43617652211781/100000000000000 : ℝ)^3117
        have hw : |(2677551151/5000000000 : ℝ)|=(2677551151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613412913/5000000000 : ℝ)|^4141 ≤ (1689403116639/4000000000000 : ℝ)^3117
        have hw : |(2613412913/5000000000 : ℝ)|=(2613412913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2294547649/10000000000 : ℝ)|^4141 ≤ (7073634926949/50000000000000 : ℝ)^3117
        have hw : |(-2294547649/10000000000 : ℝ)|=(2294547649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s3_3 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546196149/1250000000 : ℝ)*x 0 + (521196689/1250000000 : ℝ)*x 1 + (2289611857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546196149/1250000000 : ℝ)^4141 ≤ (4161263000359/12500000000000 : ℝ)^3117 := by
    have hnat : (546196149 : ℕ)^4141*12500000000000^3117 ≤ 4161263000359^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546196149 1250000000 4161263000359 12500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521196689/1250000000 : ℝ)^4141 ≤ (6256245026623/20000000000000 : ℝ)^3117 := by
    have hnat : (521196689 : ℕ)^4141*20000000000000^3117 ≤ 6256245026623^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521196689 1250000000 6256245026623 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2289611857/5000000000 : ℝ)^4141 ≤ (8857167710589/25000000000000 : ℝ)^3117 := by
    have hnat : (2289611857 : ℕ)^4141*25000000000000^3117 ≤ 8857167710589^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289611857 5000000000 8857167710589 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546196149/1250000000 : ℝ), (521196689/1250000000 : ℝ), (2289611857/5000000000 : ℝ)] ![(4161263000359/12500000000000 : ℝ), (6256245026623/20000000000000 : ℝ), (8857167710589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546196149/1250000000 : ℝ)|^4141 ≤ (4161263000359/12500000000000 : ℝ)^3117
        have hw : |(546196149/1250000000 : ℝ)|=(546196149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521196689/1250000000 : ℝ)|^4141 ≤ (6256245026623/20000000000000 : ℝ)^3117
        have hw : |(521196689/1250000000 : ℝ)|=(521196689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2289611857/5000000000 : ℝ)|^4141 ≤ (8857167710589/25000000000000 : ℝ)^3117
        have hw : |(2289611857/5000000000 : ℝ)|=(2289611857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s3_4 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188081319/10000000000 : ℝ)*x 0 + (52276639/100000000 : ℝ)*x 1 + (27170259/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188081319/10000000000 : ℝ)^4141 ≤ (6640953524639/50000000000000 : ℝ)^3117 := by
    have hnat : (2188081319 : ℕ)^4141*50000000000000^3117 ≤ 6640953524639^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188081319 10000000000 6640953524639 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52276639/100000000 : ℝ)^4141 ≤ (42244074911509/100000000000000 : ℝ)^3117 := by
    have hnat : (52276639 : ℕ)^4141*100000000000000^3117 ≤ 42244074911509^3117*100000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52276639 100000000 42244074911509 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27170259/50000000 : ℝ)^4141 ≤ (44474018021089/100000000000000 : ℝ)^3117 := by
    have hnat : (27170259 : ℕ)^4141*100000000000000^3117 ≤ 44474018021089^3117*50000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27170259 50000000 44474018021089 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188081319/10000000000 : ℝ), (52276639/100000000 : ℝ), (27170259/50000000 : ℝ)] ![(6640953524639/50000000000000 : ℝ), (42244074911509/100000000000000 : ℝ), (44474018021089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188081319/10000000000 : ℝ)|^4141 ≤ (6640953524639/50000000000000 : ℝ)^3117
        have hw : |(-2188081319/10000000000 : ℝ)|=(2188081319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52276639/100000000 : ℝ)|^4141 ≤ (42244074911509/100000000000000 : ℝ)^3117
        have hw : |(52276639/100000000 : ℝ)|=(52276639/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27170259/50000000 : ℝ)|^4141 ≤ (44474018021089/100000000000000 : ℝ)^3117
        have hw : |(27170259/50000000 : ℝ)|=(27170259/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s3_5 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530259697/1000000000 : ℝ)*x 0 + (-2087322063/10000000000 : ℝ)*x 1 + (5434051777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530259697/1000000000 : ℝ)^4141 ≤ (4305041488883/10000000000000 : ℝ)^3117 := by
    have hnat : (530259697 : ℕ)^4141*10000000000000^3117 ≤ 4305041488883^3117*1000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530259697 1000000000 4305041488883 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087322063/10000000000 : ℝ)^4141 ≤ (12475567330341/100000000000000 : ℝ)^3117 := by
    have hnat : (2087322063 : ℕ)^4141*100000000000000^3117 ≤ 12475567330341^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087322063 10000000000 12475567330341 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434051777/10000000000 : ℝ)^4141 ≤ (44474017771009/100000000000000 : ℝ)^3117 := by
    have hnat : (5434051777 : ℕ)^4141*100000000000000^3117 ≤ 44474017771009^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434051777 10000000000 44474017771009 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530259697/1000000000 : ℝ), (-2087322063/10000000000 : ℝ), (5434051777/10000000000 : ℝ)] ![(4305041488883/10000000000000 : ℝ), (12475567330341/100000000000000 : ℝ), (44474017771009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530259697/1000000000 : ℝ)|^4141 ≤ (4305041488883/10000000000000 : ℝ)^3117
        have hw : |(530259697/1000000000 : ℝ)|=(530259697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2087322063/10000000000 : ℝ)|^4141 ≤ (12475567330341/100000000000000 : ℝ)^3117
        have hw : |(-2087322063/10000000000 : ℝ)|=(2087322063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434051777/10000000000 : ℝ)|^4141 ≤ (44474017771009/100000000000000 : ℝ)^3117
        have hw : |(5434051777/10000000000 : ℝ)|=(5434051777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s3_6 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325649347/2500000000 : ℝ)*x 0 + (1358513043/2500000000 : ℝ)*x 1 + (-2087320953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325649347/2500000000 : ℝ)^4141 ≤ (1345325606167/3125000000000 : ℝ)^3117 := by
    have hnat : (1325649347 : ℕ)^4141*3125000000000^3117 ≤ 1345325606167^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325649347 2500000000 1345325606167 3125000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358513043/2500000000 : ℝ)^4141 ≤ (2223701103293/5000000000000 : ℝ)^3117 := by
    have hnat : (1358513043 : ℕ)^4141*5000000000000^3117 ≤ 2223701103293^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358513043 2500000000 2223701103293 5000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087320953/10000000000 : ℝ)^4141 ≤ (12475558516561/100000000000000 : ℝ)^3117 := by
    have hnat : (2087320953 : ℕ)^4141*100000000000000^3117 ≤ 12475558516561^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087320953 10000000000 12475558516561 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325649347/2500000000 : ℝ), (1358513043/2500000000 : ℝ), (-2087320953/10000000000 : ℝ)] ![(1345325606167/3125000000000 : ℝ), (2223701103293/5000000000000 : ℝ), (12475558516561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325649347/2500000000 : ℝ)|^4141 ≤ (1345325606167/3125000000000 : ℝ)^3117
        have hw : |(1325649347/2500000000 : ℝ)|=(1325649347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358513043/2500000000 : ℝ)|^4141 ≤ (2223701103293/5000000000000 : ℝ)^3117
        have hw : |(1358513043/2500000000 : ℝ)|=(1358513043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087320953/10000000000 : ℝ)|^4141 ≤ (12475558516561/100000000000000 : ℝ)^3117
        have hw : |(-2087320953/10000000000 : ℝ)|=(2087320953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s3_7 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2184804903/5000000000 : ℝ)*x 0 + (4577573461/10000000000 : ℝ)*x 1 + (4171233911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184804903/5000000000 : ℝ)^4141 ≤ (33290515078177/100000000000000 : ℝ)^3117 := by
    have hnat : (2184804903 : ℕ)^4141*100000000000000^3117 ≤ 33290515078177^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184804903 5000000000 33290515078177 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4577573461/10000000000 : ℝ)^4141 ≤ (17705854827603/50000000000000 : ℝ)^3117 := by
    have hnat : (4577573461 : ℕ)^4141*50000000000000^3117 ≤ 17705854827603^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4577573461 10000000000 17705854827603 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171233911/10000000000 : ℝ)^4141 ≤ (31297775263309/100000000000000 : ℝ)^3117 := by
    have hnat : (4171233911 : ℕ)^4141*100000000000000^3117 ≤ 31297775263309^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171233911 10000000000 31297775263309 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184804903/5000000000 : ℝ), (4577573461/10000000000 : ℝ), (4171233911/10000000000 : ℝ)] ![(33290515078177/100000000000000 : ℝ), (17705854827603/50000000000000 : ℝ), (31297775263309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184804903/5000000000 : ℝ)|^4141 ≤ (33290515078177/100000000000000 : ℝ)^3117
        have hw : |(2184804903/5000000000 : ℝ)|=(2184804903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4577573461/10000000000 : ℝ)|^4141 ≤ (17705854827603/50000000000000 : ℝ)^3117
        have hw : |(4577573461/10000000000 : ℝ)|=(4577573461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171233911/10000000000 : ℝ)|^4141 ≤ (31297775263309/100000000000000 : ℝ)^3117
        have hw : |(4171233911/10000000000 : ℝ)|=(4171233911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1089_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8823/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10471/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14873/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8333/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8823/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8333/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8823/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8333/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8823/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8333/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8823/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8333/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8823/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8333/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8823/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8823/100000 : ℝ) ^ (8281/2048 : ℝ) ≤ (340819745606599/6250000000000000000 : ℝ) := by
    have hpowers : (8823/100000 : ℝ)^8281 ≤ (340819745606599/6250000000000000000 : ℝ)^2048 := by
      have hnat : (8823 : ℕ)^8281*6250000000000000000^2048 ≤ 340819745606599^2048*100000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8823 100000 340819745606599 6250000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8823/100000 : ℝ)) (X := (340819745606599/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8333/50000 : ℝ) ^ (8281/2048 : ℝ) ≤ (71368835701598993/100000000000000000000 : ℝ) := by
    have hpowers : (8333/50000 : ℝ)^8281 ≤ (71368835701598993/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8333 : ℕ)^8281*100000000000000000000^2048 ≤ 71368835701598993^2048*50000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8333 50000 71368835701598993 100000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8333/50000 : ℝ)) (X := (71368835701598993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125340819745606599/3125000000000000000 : ℝ) ≤ (2500067428589933/2500000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (3125340819745606599/3125000000000000000 : ℝ)^2048 ≤ (2500067428589933/2500000000000000 : ℝ)^8281 := by
      have hnat : (3125340819745606599 : ℕ)^2048*2500000000000000^8281 ≤ 2500067428589933^8281*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125340819745606599 3125000000000000000 2500067428589933 2500000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500067428589933/2500000000000000 : ℝ)) (X := (3125340819745606599/3125000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100076821951631304577/100000000000000000000 : ℝ) ≤ (5000949679329723/5000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (100076821951631304577/100000000000000000000 : ℝ)^2048 ≤ (5000949679329723/5000000000000000 : ℝ)^8281 := by
      have hnat : (100076821951631304577 : ℕ)^2048*5000000000000000^8281 ≤ 5000949679329723^8281*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100076821951631304577 100000000000000000000 5000949679329723 5000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000949679329723/5000000000000000 : ℝ)) (X := (100076821951631304577/100000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50071368835701598993/50000000000000000000 : ℝ) ≤ (250088225073979/250000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (50071368835701598993/50000000000000000000 : ℝ)^2048 ≤ (250088225073979/250000000000000 : ℝ)^8281 := by
      have hnat : (50071368835701598993 : ℕ)^2048*250000000000000^8281 ≤ 250088225073979^8281*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50071368835701598993 50000000000000000000 250088225073979 250000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250088225073979/250000000000000 : ℝ)) (X := (50071368835701598993/50000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(340819745606599/6250000000000000000 : ℝ) ≤ ((1225052479162666013/1225468750000000000 : ℝ)+2*(814822149857/392150000000000 : ℝ)*(8823/100000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (1225052479162666013/1225468750000000000 : ℝ)+2*(814822149857/392150000000000 : ℝ)*(8823/100000 : ℝ)=(2500067428589933/2500000000000000 : ℝ) by norm_num, show 1+2*(340819745606599/6250000000000000000 : ℝ)=(3125340819745606599/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71368835701598993/100000000000000000000 : ℝ)+(340819745606599/6250000000000000000 : ℝ) ≤ ((1225052479162666013/1225468750000000000 : ℝ)+(814822149857/392150000000000 : ℝ)*((8333/50000 : ℝ)+(8823/100000 : ℝ)))^(8281/2048 : ℝ) := by
    rw [show (1225052479162666013/1225468750000000000 : ℝ)+(814822149857/392150000000000 : ℝ)*((8333/50000 : ℝ)+(8823/100000 : ℝ))=(5000949679329723/5000000000000000 : ℝ) by norm_num, show 1+(71368835701598993/100000000000000000000 : ℝ)+(340819745606599/6250000000000000000 : ℝ)=(100076821951631304577/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71368835701598993/100000000000000000000 : ℝ) ≤ ((1225052479162666013/1225468750000000000 : ℝ)+2*(814822149857/392150000000000 : ℝ)*(8333/50000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (1225052479162666013/1225468750000000000 : ℝ)+2*(814822149857/392150000000000 : ℝ)*(8333/50000 : ℝ)=(250088225073979/250000000000000 : ℝ) by norm_num, show 1+2*(71368835701598993/100000000000000000000 : ℝ)=(50071368835701598993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1225052479162666013/1225468750000000000 : ℝ)*(X 1 0+X 2 0)+(814822149857/392150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (8823/100000 : ℝ)) (hi := (8333/50000 : ℝ)) (c := (1225052479162666013/1225468750000000000 : ℝ)) (alpha := (814822149857/392150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1225052479162666013/1225468750000000000 : ℝ)*(X 0 1+X 2 1)+(814822149857/392150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (8823/100000 : ℝ)) (hi := (8333/50000 : ℝ)) (c := (1225052479162666013/1225468750000000000 : ℝ)) (alpha := (814822149857/392150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1225052479162666013/1225468750000000000 : ℝ)*(X 0 2+X 1 2)+(814822149857/392150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (8823/100000 : ℝ)) (hi := (8333/50000 : ℝ)) (c := (1225052479162666013/1225468750000000000 : ℝ)) (alpha := (814822149857/392150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2188059819/10000000000 : ℝ)*X 0 0+(2717447769/5000000000 : ℝ)*X 0 1+(5226825467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677551203/5000000000 : ℝ)*X 1 0+(-2294548083/10000000000 : ℝ)*X 1 1+(522682539/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677551151/5000000000 : ℝ)*X 2 0+(2613412913/5000000000 : ℝ)*X 2 1+(-2294547649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546196149/1250000000 : ℝ)*X 0 0+(521196689/1250000000 : ℝ)*X 0 1+(2289611857/5000000000 : ℝ)*X 0 2+(546196149/1250000000 : ℝ)*X 1 0+(521196689/1250000000 : ℝ)*X 1 1+(2289611857/5000000000 : ℝ)*X 1 2+(546196149/1250000000 : ℝ)*X 2 0+(521196689/1250000000 : ℝ)*X 2 1+(2289611857/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2188081319/10000000000 : ℝ)*X 0 0+(52276639/100000000 : ℝ)*X 0 1+(27170259/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530259697/1000000000 : ℝ)*X 1 0+(-2087322063/10000000000 : ℝ)*X 1 1+(5434051777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325649347/2500000000 : ℝ)*X 2 0+(1358513043/2500000000 : ℝ)*X 2 1+(-2087320953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184804903/5000000000 : ℝ)*X 0 0+(4577573461/10000000000 : ℝ)*X 0 1+(4171233911/10000000000 : ℝ)*X 0 2+(2184804903/5000000000 : ℝ)*X 1 0+(4577573461/10000000000 : ℝ)*X 1 1+(4171233911/10000000000 : ℝ)*X 1 2+(2184804903/5000000000 : ℝ)*X 2 0+(4577573461/10000000000 : ℝ)*X 2 1+(4171233911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (400208003228309053021271991/61273437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (442861623/25000000000000 : ℝ)*(base19) + (128091319/10000000000000 : ℝ)*(base23) + (21270179/10000000000000 : ℝ)*(lower2) + (74837907/100000000000000 : ℝ)*(upper3) + (183083261/100000000000000 : ℝ)*(upper5) + (452954481730009/12500000000000 : ℝ)*(major0) + (452954481730009/12500000000000 : ℝ)*(major1) + (452954481730009/12500000000000 : ℝ)*(major2) + (961220394746001/20000000000000 : ℝ)*(sp0) + (600766950984907/12500000000000 : ℝ)*(sp1) + (4806136098412559/100000000000000 : ℝ)*(sp2) + (1220560339922497/50000000000000 : ℝ)*(sp3) + (35405595743/100000000000000 : ℝ)*(sp4) + (13430792429/100000000000000 : ℝ)*(sp7) + (1220567055318711/50000000000000 : ℝ)*(f.failure) + (1201534344831437/25000000000000 : ℝ)*(f.sum) + (87666794147621/19607500000000000000000000000 : ℝ)*base66 + (752459364738755189/122546875000000000000000000000000 : ℝ)*base68 + (526695871652729157/61273437500000000000000000000000 : ℝ)*base70 + (201287633020833343/61273437500000000000000000000000 : ℝ)*base71 + (1891940046873/39215000000000000000000000000 : ℝ)*base73 + (670749555469755189/122546875000000000000000000000000 : ℝ)*base76 + (208305932130584633/15318359375000000000000000000000 : ℝ)*base78 + (1967873553441755189/122546875000000000000000000000000 : ℝ)*base80 + (9789090892597/2450937500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (20304919/5000000000000000000000 : ℝ)*base90 + (20304919/5000000000000000000000 : ℝ)*base92 + (20304919/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48150111887423251545155121/122546875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46466039/20000000000000 : ℝ)*(base19) + (264481793/20000000000000 : ℝ)*(base23) + (55593019/25000000000000 : ℝ)*(upper2) + (94936701/100000000000000 : ℝ)*(upper3) + (244117/800000000000 : ℝ)*(upper4) + (15616743/25000000000000 : ℝ)*(upper5) + (456640202251877/12500000000000 : ℝ)*(major0) + (456640202251877/12500000000000 : ℝ)*(major1) + (456640202251877/12500000000000 : ℝ)*(major2) + (34975047139/100000000000000 : ℝ)*(sp2) + (2422622721436871/50000000000000 : ℝ)*(sp4) + (4845245210543547/100000000000000 : ℝ)*(sp5) + (2422604572708819/50000000000000 : ℝ)*(sp6) + (307624722507403/12500000000000 : ℝ)*(sp7) + (307624722507403/12500000000000 : ℝ)*(f.failure) + (2422622721436871/50000000000000 : ℝ)*(f.sum) + (52709371334767/19607500000000000000000000000 : ℝ)*base65 + (124256441050088987/7659179687500000000000000000000 : ℝ)*base68 + (29629038002131099/15318359375000000000000000000000 : ℝ)*base70 + (165183378822665021/61273437500000000000000000000000 : ℝ)*base72 + (12616523324221/39215000000000000000000000000 : ℝ)*base74 + (1500266040401435583/122546875000000000000000000000000 : ℝ)*base75 + (880249966163883771/61273437500000000000000000000000 : ℝ)*base78 + (258911682176102521/61273437500000000000000000000000 : ℝ)*base80 + (233478267430961/39215000000000000000000000000 : ℝ)*base82 + (3787413/1250000000000000000000 : ℝ)*base89 + (3787413/1250000000000000000000 : ℝ)*base91 + (3787413/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1089_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8823/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14873/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1089_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1089_s4_0 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095759827/5000000000 : ℝ)*x 0 + (540456337/1000000000 : ℝ)*x 1 + (5254896461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095759827/5000000000 : ℝ)^4141 ≤ (2661928377537/20000000000000 : ℝ)^3117 := by
    have hnat : (1095759827 : ℕ)^4141*20000000000000^3117 ≤ 2661928377537^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095759827 5000000000 2661928377537 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540456337/1000000000 : ℝ)^4141 ≤ (44153675264337/100000000000000 : ℝ)^3117 := by
    have hnat : (540456337 : ℕ)^4141*100000000000000^3117 ≤ 44153675264337^3117*1000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540456337 1000000000 44153675264337 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254896461/10000000000 : ℝ)^4141 ≤ (42536682838917/100000000000000 : ℝ)^3117 := by
    have hnat : (5254896461 : ℕ)^4141*100000000000000^3117 ≤ 42536682838917^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254896461 10000000000 42536682838917 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095759827/5000000000 : ℝ), (540456337/1000000000 : ℝ), (5254896461/10000000000 : ℝ)] ![(2661928377537/20000000000000 : ℝ), (44153675264337/100000000000000 : ℝ), (42536682838917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095759827/5000000000 : ℝ)|^4141 ≤ (2661928377537/20000000000000 : ℝ)^3117
        have hw : |(-1095759827/5000000000 : ℝ)|=(1095759827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540456337/1000000000 : ℝ)|^4141 ≤ (44153675264337/100000000000000 : ℝ)^3117
        have hw : |(540456337/1000000000 : ℝ)|=(540456337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254896461/10000000000 : ℝ)|^4141 ≤ (42536682838917/100000000000000 : ℝ)^3117
        have hw : |(5254896461/10000000000 : ℝ)|=(5254896461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s4_1 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347569407/10000000000 : ℝ)*x 0 + (-2267623997/10000000000 : ℝ)*x 1 + (2627448133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347569407/10000000000 : ℝ)^4141 ≤ (2721009901973/6250000000000 : ℝ)^3117 := by
    have hnat : (5347569407 : ℕ)^4141*6250000000000^3117 ≤ 2721009901973^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347569407 10000000000 2721009901973 6250000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267623997/10000000000 : ℝ)^4141 ≤ (13927160815411/100000000000000 : ℝ)^3117 := by
    have hnat : (2267623997 : ℕ)^4141*100000000000000^3117 ≤ 13927160815411^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267623997 10000000000 13927160815411 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627448133/5000000000 : ℝ)^4141 ≤ (42536680741897/100000000000000 : ℝ)^3117 := by
    have hnat : (2627448133 : ℕ)^4141*100000000000000^3117 ≤ 42536680741897^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627448133 5000000000 42536680741897 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347569407/10000000000 : ℝ), (-2267623997/10000000000 : ℝ), (2627448133/5000000000 : ℝ)] ![(2721009901973/6250000000000 : ℝ), (13927160815411/100000000000000 : ℝ), (42536680741897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347569407/10000000000 : ℝ)|^4141 ≤ (2721009901973/6250000000000 : ℝ)^3117
        have hw : |(5347569407/10000000000 : ℝ)|=(5347569407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2267623997/10000000000 : ℝ)|^4141 ≤ (13927160815411/100000000000000 : ℝ)^3117
        have hw : |(-2267623997/10000000000 : ℝ)|=(2267623997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627448133/5000000000 : ℝ)|^4141 ≤ (42536680741897/100000000000000 : ℝ)^3117
        have hw : |(2627448133/5000000000 : ℝ)|=(2627448133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s4_2 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334223101/625000000 : ℝ)*x 0 + (1313724059/2500000000 : ℝ)*x 1 + (-28345297/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334223101/625000000 : ℝ)^4141 ≤ (43536160692089/100000000000000 : ℝ)^3117 := by
    have hnat : (334223101 : ℕ)^4141*100000000000000^3117 ≤ 43536160692089^3117*625000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334223101 625000000 43536160692089 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313724059/2500000000 : ℝ)^4141 ≤ (42536680419279/100000000000000 : ℝ)^3117 := by
    have hnat : (1313724059 : ℕ)^4141*100000000000000^3117 ≤ 42536680419279^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313724059 2500000000 42536680419279 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28345297/125000000 : ℝ)^4141 ≤ (6963579440813/50000000000000 : ℝ)^3117 := by
    have hnat : (28345297 : ℕ)^4141*50000000000000^3117 ≤ 6963579440813^3117*125000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28345297 125000000 6963579440813 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334223101/625000000 : ℝ), (1313724059/2500000000 : ℝ), (-28345297/125000000 : ℝ)] ![(43536160692089/100000000000000 : ℝ), (42536680419279/100000000000000 : ℝ), (6963579440813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334223101/625000000 : ℝ)|^4141 ≤ (43536160692089/100000000000000 : ℝ)^3117
        have hw : |(334223101/625000000 : ℝ)|=(334223101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313724059/2500000000 : ℝ)|^4141 ≤ (42536680419279/100000000000000 : ℝ)^3117
        have hw : |(1313724059/2500000000 : ℝ)|=(1313724059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28345297/125000000 : ℝ)|^4141 ≤ (6963579440813/50000000000000 : ℝ)^3117
        have hw : |(-28345297/125000000 : ℝ)|=(28345297/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s4_3 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371628937/10000000000 : ℝ)*x 0 + (264174769/625000000 : ℝ)*x 1 + (4521462677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371628937/10000000000 : ℝ)^4141 ≤ (33310953329791/100000000000000 : ℝ)^3117 := by
    have hnat : (4371628937 : ℕ)^4141*100000000000000^3117 ≤ 33310953329791^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371628937 10000000000 33310953329791 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264174769/625000000 : ℝ)^4141 ≤ (19908025837/62500000000 : ℝ)^3117 := by
    have hnat : (264174769 : ℕ)^4141*62500000000^3117 ≤ 19908025837^3117*625000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264174769 625000000 19908025837 62500000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4521462677/10000000000 : ℝ)^4141 ≤ (6967241063211/20000000000000 : ℝ)^3117 := by
    have hnat : (4521462677 : ℕ)^4141*20000000000000^3117 ≤ 6967241063211^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521462677 10000000000 6967241063211 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371628937/10000000000 : ℝ), (264174769/625000000 : ℝ), (4521462677/10000000000 : ℝ)] ![(33310953329791/100000000000000 : ℝ), (19908025837/62500000000 : ℝ), (6967241063211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371628937/10000000000 : ℝ)|^4141 ≤ (33310953329791/100000000000000 : ℝ)^3117
        have hw : |(4371628937/10000000000 : ℝ)|=(4371628937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264174769/625000000 : ℝ)|^4141 ≤ (19908025837/62500000000 : ℝ)^3117
        have hw : |(264174769/625000000 : ℝ)|=(264174769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4521462677/10000000000 : ℝ)|^4141 ≤ (6967241063211/20000000000000 : ℝ)^3117
        have hw : |(4521462677/10000000000 : ℝ)|=(4521462677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s4_4 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2191527967/10000000000 : ℝ)*x 0 + (5255330869/10000000000 : ℝ)*x 1 + (5404126759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2191527967/10000000000 : ℝ)^4141 ≤ (13309708960647/100000000000000 : ℝ)^3117 := by
    have hnat : (2191527967 : ℕ)^4141*100000000000000^3117 ≤ 13309708960647^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191527967 10000000000 13309708960647 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255330869/10000000000 : ℝ)^4141 ≤ (340330836023/800000000000 : ℝ)^3117 := by
    have hnat : (5255330869 : ℕ)^4141*800000000000^3117 ≤ 340330836023^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255330869 10000000000 340330836023 800000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404126759/10000000000 : ℝ)^4141 ≤ (22074468258333/50000000000000 : ℝ)^3117 := by
    have hnat : (5404126759 : ℕ)^4141*50000000000000^3117 ≤ 22074468258333^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404126759 10000000000 22074468258333 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2191527967/10000000000 : ℝ), (5255330869/10000000000 : ℝ), (5404126759/10000000000 : ℝ)] ![(13309708960647/100000000000000 : ℝ), (340330836023/800000000000 : ℝ), (22074468258333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2191527967/10000000000 : ℝ)|^4141 ≤ (13309708960647/100000000000000 : ℝ)^3117
        have hw : |(-2191527967/10000000000 : ℝ)|=(2191527967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255330869/10000000000 : ℝ)|^4141 ≤ (340330836023/800000000000 : ℝ)^3117
        have hw : |(5255330869/10000000000 : ℝ)|=(5255330869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404126759/10000000000 : ℝ)|^4141 ≤ (22074468258333/50000000000000 : ℝ)^3117
        have hw : |(5404126759/10000000000 : ℝ)|=(5404126759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s4_5 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2654902471/5000000000 : ℝ)*x 0 + (-1059196717/5000000000 : ℝ)*x 1 + (2702063411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654902471/5000000000 : ℝ)^4141 ≤ (21564088422021/50000000000000 : ℝ)^3117 := by
    have hnat : (2654902471 : ℕ)^4141*50000000000000^3117 ≤ 21564088422021^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654902471 5000000000 21564088422021 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059196717/5000000000 : ℝ)^4141 ≤ (6361442969177/50000000000000 : ℝ)^3117 := by
    have hnat : (1059196717 : ℕ)^4141*50000000000000^3117 ≤ 6361442969177^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059196717 5000000000 6361442969177 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702063411/5000000000 : ℝ)^4141 ≤ (22074468600213/50000000000000 : ℝ)^3117 := by
    have hnat : (2702063411 : ℕ)^4141*50000000000000^3117 ≤ 22074468600213^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702063411 5000000000 22074468600213 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654902471/5000000000 : ℝ), (-1059196717/5000000000 : ℝ), (2702063411/5000000000 : ℝ)] ![(21564088422021/50000000000000 : ℝ), (6361442969177/50000000000000 : ℝ), (22074468600213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654902471/5000000000 : ℝ)|^4141 ≤ (21564088422021/50000000000000 : ℝ)^3117
        have hw : |(2654902471/5000000000 : ℝ)|=(2654902471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1059196717/5000000000 : ℝ)|^4141 ≤ (6361442969177/50000000000000 : ℝ)^3117
        have hw : |(-1059196717/5000000000 : ℝ)|=(1059196717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702063411/5000000000 : ℝ)|^4141 ≤ (22074468600213/50000000000000 : ℝ)^3117
        have hw : |(2702063411/5000000000 : ℝ)|=(2702063411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s4_6 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309805169/10000000000 : ℝ)*x 0 + (5404126849/10000000000 : ℝ)*x 1 + (-2118393091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309805169/10000000000 : ℝ)^4141 ≤ (21564089646769/50000000000000 : ℝ)^3117 := by
    have hnat : (5309805169 : ℕ)^4141*50000000000000^3117 ≤ 21564089646769^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309805169 10000000000 21564089646769 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404126849/10000000000 : ℝ)^4141 ≤ (22074468746733/50000000000000 : ℝ)^3117 := by
    have hnat : (5404126849 : ℕ)^4141*50000000000000^3117 ≤ 22074468746733^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404126849 10000000000 22074468746733 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118393091/10000000000 : ℝ)^4141 ≤ (12722883201563/100000000000000 : ℝ)^3117 := by
    have hnat : (2118393091 : ℕ)^4141*100000000000000^3117 ≤ 12722883201563^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118393091 10000000000 12722883201563 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309805169/10000000000 : ℝ), (5404126849/10000000000 : ℝ), (-2118393091/10000000000 : ℝ)] ![(21564089646769/50000000000000 : ℝ), (22074468746733/50000000000000 : ℝ), (12722883201563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309805169/10000000000 : ℝ)|^4141 ≤ (21564089646769/50000000000000 : ℝ)^3117
        have hw : |(5309805169/10000000000 : ℝ)|=(5309805169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404126849/10000000000 : ℝ)|^4141 ≤ (22074468746733/50000000000000 : ℝ)^3117
        have hw : |(5404126849/10000000000 : ℝ)|=(5404126849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2118393091/10000000000 : ℝ)|^4141 ≤ (12722883201563/100000000000000 : ℝ)^3117
        have hw : |(-2118393091/10000000000 : ℝ)|=(2118393091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s4_7 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34973153/80000000 : ℝ)*x 0 + (2260303597/5000000000 : ℝ)*x 1 + (2113827763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34973153/80000000 : ℝ)^4141 ≤ (8327776769763/25000000000000 : ℝ)^3117 := by
    have hnat : (34973153 : ℕ)^4141*25000000000000^3117 ≤ 8327776769763^3117*80000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34973153 80000000 8327776769763 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260303597/5000000000 : ℝ)^4141 ≤ (17413724532499/50000000000000 : ℝ)^3117 := by
    have hnat : (2260303597 : ℕ)^4141*50000000000000^3117 ≤ 17413724532499^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260303597 5000000000 17413724532499 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113827763/5000000000 : ℝ)^4141 ≤ (3186144384901/10000000000000 : ℝ)^3117 := by
    have hnat : (2113827763 : ℕ)^4141*10000000000000^3117 ≤ 3186144384901^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113827763 5000000000 3186144384901 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34973153/80000000 : ℝ), (2260303597/5000000000 : ℝ), (2113827763/5000000000 : ℝ)] ![(8327776769763/25000000000000 : ℝ), (17413724532499/50000000000000 : ℝ), (3186144384901/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34973153/80000000 : ℝ)|^4141 ≤ (8327776769763/25000000000000 : ℝ)^3117
        have hw : |(34973153/80000000 : ℝ)|=(34973153/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2260303597/5000000000 : ℝ)|^4141 ≤ (17413724532499/50000000000000 : ℝ)^3117
        have hw : |(2260303597/5000000000 : ℝ)|=(2260303597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113827763/5000000000 : ℝ)|^4141 ≤ (3186144384901/10000000000000 : ℝ)^3117
        have hw : |(2113827763/5000000000 : ℝ)|=(2113827763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1089_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1107/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (89/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14873/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14873/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14873/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14873/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14873/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14873/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10471/100000 : ℝ) ^ (8281/2048 : ℝ) ≤ (10898437380283333/100000000000000000000 : ℝ) := by
    have hpowers : (10471/100000 : ℝ)^8281 ≤ (10898437380283333/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10471 : ℕ)^8281*100000000000000000000^2048 ≤ 10898437380283333^2048*100000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10471 100000 10898437380283333 100000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10471/100000 : ℝ)) (X := (10898437380283333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14873/100000 : ℝ) ^ (8281/2048 : ℝ) ≤ (22521598673118307/50000000000000000000 : ℝ) := by
    have hpowers : (14873/100000 : ℝ)^8281 ≤ (22521598673118307/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14873 : ℕ)^8281*50000000000000000000^2048 ≤ 22521598673118307^2048*100000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14873 100000 22521598673118307 50000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14873/100000 : ℝ)) (X := (22521598673118307/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010898437380283333/50000000000000000000 : ℝ) ≤ (5000269510554929/5000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (50010898437380283333/50000000000000000000 : ℝ)^2048 ≤ (5000269510554929/5000000000000000 : ℝ)^8281 := by
      have hnat : (50010898437380283333 : ℕ)^2048*5000000000000000^8281 ≤ 5000269510554929^8281*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010898437380283333 50000000000000000000 5000269510554929 5000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269510554929/5000000000000000 : ℝ)) (X := (50010898437380283333/50000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100055941634726519947/100000000000000000000 : ℝ) ≤ (10001383218879297/10000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (100055941634726519947/100000000000000000000 : ℝ)^2048 ≤ (10001383218879297/10000000000000000 : ℝ)^8281 := by
      have hnat : (100055941634726519947 : ℕ)^2048*10000000000000000^8281 ≤ 10001383218879297^8281*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100055941634726519947 100000000000000000000 10001383218879297 10000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001383218879297/10000000000000000 : ℝ)) (X := (100055941634726519947/100000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25022521598673118307/25000000000000000000 : ℝ) ≤ (312569606770273/312500000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (25022521598673118307/25000000000000000000 : ℝ)^2048 ≤ (312569606770273/312500000000000 : ℝ)^8281 := by
      have hnat : (25022521598673118307 : ℕ)^2048*312500000000000^8281 ≤ 312569606770273^8281*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022521598673118307 25000000000000000000 312569606770273 312500000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312569606770273/312500000000000 : ℝ)) (X := (25022521598673118307/25000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10898437380283333/100000000000000000000 : ℝ) ≤ ((22002346790619001689/22010000000000000000 : ℝ)+2*(844197769439/440200000000000 : ℝ)*(10471/100000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (22002346790619001689/22010000000000000000 : ℝ)+2*(844197769439/440200000000000 : ℝ)*(10471/100000 : ℝ)=(5000269510554929/5000000000000000 : ℝ) by norm_num, show 1+2*(10898437380283333/100000000000000000000 : ℝ)=(50010898437380283333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22521598673118307/50000000000000000000 : ℝ)+(10898437380283333/100000000000000000000 : ℝ) ≤ ((22002346790619001689/22010000000000000000 : ℝ)+(844197769439/440200000000000 : ℝ)*((14873/100000 : ℝ)+(10471/100000 : ℝ)))^(8281/2048 : ℝ) := by
    rw [show (22002346790619001689/22010000000000000000 : ℝ)+(844197769439/440200000000000 : ℝ)*((14873/100000 : ℝ)+(10471/100000 : ℝ))=(10001383218879297/10000000000000000 : ℝ) by norm_num, show 1+(22521598673118307/50000000000000000000 : ℝ)+(10898437380283333/100000000000000000000 : ℝ)=(100055941634726519947/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22521598673118307/50000000000000000000 : ℝ) ≤ ((22002346790619001689/22010000000000000000 : ℝ)+2*(844197769439/440200000000000 : ℝ)*(14873/100000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (22002346790619001689/22010000000000000000 : ℝ)+2*(844197769439/440200000000000 : ℝ)*(14873/100000 : ℝ)=(312569606770273/312500000000000 : ℝ) by norm_num, show 1+2*(22521598673118307/50000000000000000000 : ℝ)=(25022521598673118307/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22002346790619001689/22010000000000000000 : ℝ)*(X 1 0+X 2 0)+(844197769439/440200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (10471/100000 : ℝ)) (hi := (14873/100000 : ℝ)) (c := (22002346790619001689/22010000000000000000 : ℝ)) (alpha := (844197769439/440200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22002346790619001689/22010000000000000000 : ℝ)*(X 0 1+X 2 1)+(844197769439/440200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (10471/100000 : ℝ)) (hi := (14873/100000 : ℝ)) (c := (22002346790619001689/22010000000000000000 : ℝ)) (alpha := (844197769439/440200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22002346790619001689/22010000000000000000 : ℝ)*(X 0 2+X 1 2)+(844197769439/440200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (10471/100000 : ℝ)) (hi := (14873/100000 : ℝ)) (c := (22002346790619001689/22010000000000000000 : ℝ)) (alpha := (844197769439/440200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1095759827/5000000000 : ℝ)*X 0 0+(540456337/1000000000 : ℝ)*X 0 1+(5254896461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347569407/10000000000 : ℝ)*X 1 0+(-2267623997/10000000000 : ℝ)*X 1 1+(2627448133/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334223101/625000000 : ℝ)*X 2 0+(1313724059/2500000000 : ℝ)*X 2 1+(-28345297/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371628937/10000000000 : ℝ)*X 0 0+(264174769/625000000 : ℝ)*X 0 1+(4521462677/10000000000 : ℝ)*X 0 2+(4371628937/10000000000 : ℝ)*X 1 0+(264174769/625000000 : ℝ)*X 1 1+(4521462677/10000000000 : ℝ)*X 1 2+(4371628937/10000000000 : ℝ)*X 2 0+(264174769/625000000 : ℝ)*X 2 1+(4521462677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2191527967/10000000000 : ℝ)*X 0 0+(5255330869/10000000000 : ℝ)*X 0 1+(5404126759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654902471/5000000000 : ℝ)*X 1 0+(-1059196717/5000000000 : ℝ)*X 1 1+(2702063411/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309805169/10000000000 : ℝ)*X 2 0+(5404126849/10000000000 : ℝ)*X 2 1+(-2118393091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34973153/80000000 : ℝ)*X 0 0+(2260303597/5000000000 : ℝ)*X 0 1+(2113827763/5000000000 : ℝ)*X 0 2+(34973153/80000000 : ℝ)*X 1 0+(2260303597/5000000000 : ℝ)*X 1 1+(2113827763/5000000000 : ℝ)*X 1 2+(34973153/80000000 : ℝ)*X 2 0+(2260303597/5000000000 : ℝ)*X 2 1+(2113827763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2837766345125109259418751669/220100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1528417219/100000000000000 : ℝ)*(base19) + (1024436341/100000000000000 : ℝ)*(base23) + (409151661/100000000000000 : ℝ)*(lower2) + (2682003/1250000000000 : ℝ)*(upper3) + (6091471/50000000000000 : ℝ)*(upper5) + (1007524554928607/20000000000000 : ℝ)*(major0) + (1007524554928607/20000000000000 : ℝ)*(major1) + (1007524554928607/20000000000000 : ℝ)*(major2) + (1670381301195003/25000000000000 : ℝ)*(sp0) + (3340774583560627/50000000000000 : ℝ)*(sp1) + (1670387417775533/25000000000000 : ℝ)*(sp2) + (1696838625250481/50000000000000 : ℝ)*(sp3) + (12745379231/50000000000000 : ℝ)*(sp4) + (858673869/5000000000000 : ℝ)*(sp7) + (1696847211989171/50000000000000 : ℝ)*(f.failure) + (6681550695538473/100000000000000 : ℝ)*(f.sum) + (17790371977911/4402000000000000000000000000 : ℝ)*base66 + (84747822776132777/440200000000000000000000000000000 : ℝ)*base68 + (2616372527852267223/440200000000000000000000000000000 : ℝ)*base69 + (2947133437853332777/440200000000000000000000000000000 : ℝ)*base72 + (14733731781613/4402000000000000000000000000 : ℝ)*base73 + (11168747440217467223/440200000000000000000000000000000 : ℝ)*base75 + (1259470437800132777/440200000000000000000000000000000 : ℝ)*base78 + (121483055982932777/440200000000000000000000000000000 : ℝ)*base80 + (2462041141959/880400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (37973741/5000000000000000000000 : ℝ)*base89 + (37973741/5000000000000000000000 : ℝ)*base91 + (37973741/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6219629767274232923122952217/550250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1580597041/100000000000000 : ℝ)*(base19) + (506005831/25000000000000 : ℝ)*(base23) + (374277/12500000000000 : ℝ)*(upper2) + (34379787/12500000000000 : ℝ)*(upper3) + (21823171/12500000000000 : ℝ)*(upper5) + (5067075878926451/100000000000000 : ℝ)*(major0) + (5067075878926451/100000000000000 : ℝ)*(major1) + (5067075878926451/100000000000000 : ℝ)*(major2) + (16542320433/50000000000000 : ℝ)*(sp1) + (54241744079/100000000000000 : ℝ)*(sp2) + (3360307644829989/50000000000000 : ℝ)*(sp4) + (6720580624422071/100000000000000 : ℝ)*(sp5) + (3360279511946287/50000000000000 : ℝ)*(sp6) + (3413536091416921/100000000000000 : ℝ)*(sp7) + (3413536091416921/100000000000000 : ℝ)*(f.failure) + (3360307644829989/50000000000000 : ℝ)*(f.sum) + (31186896591001/22010000000000000000000000000 : ℝ)*base66 + (36263529064530774261/2201000000000000000000000000000000 : ℝ)*base68 + (23067909403122774261/2201000000000000000000000000000000 : ℝ)*base70 + (2951886216956225739/2201000000000000000000000000000000 : ℝ)*base71 + (68576429409591/22010000000000000000000000000 : ℝ)*base74 + (18034538061738774261/2201000000000000000000000000000000 : ℝ)*base76 + (7042760857569774261/2201000000000000000000000000000000 : ℝ)*base78 + (8883628503218774261/2201000000000000000000000000000000 : ℝ)*base80 + (14908251574731/22010000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6006009/10000000000000000000000 : ℝ)*base90 + (6006009/10000000000000000000000 : ℝ)*base92 + (6006009/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1089_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1107/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (89/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1089_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1089_s5_0 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192283383/10000000000 : ℝ)*x 0 + (5396351239/10000000000 : ℝ)*x 1 + (2631303869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192283383/10000000000 : ℝ)^4141 ≤ (6657902169977/50000000000000 : ℝ)^3117 := by
    have hnat : (2192283383 : ℕ)^4141*50000000000000^3117 ≤ 6657902169977^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192283383 10000000000 6657902169977 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396351239/10000000000 : ℝ)^4141 ≤ (4406456615633/10000000000000 : ℝ)^3117 := by
    have hnat : (5396351239 : ℕ)^4141*10000000000000^3117 ≤ 4406456615633^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396351239 10000000000 4406456615633 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631303869/5000000000 : ℝ)^4141 ≤ (42619629483941/100000000000000 : ℝ)^3117 := by
    have hnat : (2631303869 : ℕ)^4141*100000000000000^3117 ≤ 42619629483941^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631303869 5000000000 42619629483941 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192283383/10000000000 : ℝ), (5396351239/10000000000 : ℝ), (2631303869/5000000000 : ℝ)] ![(6657902169977/50000000000000 : ℝ), (4406456615633/10000000000000 : ℝ), (42619629483941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192283383/10000000000 : ℝ)|^4141 ≤ (6657902169977/50000000000000 : ℝ)^3117
        have hw : |(-2192283383/10000000000 : ℝ)|=(2192283383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396351239/10000000000 : ℝ)|^4141 ≤ (4406456615633/10000000000000 : ℝ)^3117
        have hw : |(5396351239/10000000000 : ℝ)|=(5396351239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631303869/5000000000 : ℝ)|^4141 ≤ (42619629483941/100000000000000 : ℝ)^3117
        have hw : |(2631303869/5000000000 : ℝ)|=(2631303869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s5_1 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069104181/2000000000 : ℝ)*x 0 + (-452033971/2000000000 : ℝ)*x 1 + (5262607267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069104181/2000000000 : ℝ)^4141 ≤ (8702800692329/20000000000000 : ℝ)^3117 := by
    have hnat : (1069104181 : ℕ)^4141*20000000000000^3117 ≤ 8702800692329^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069104181 2000000000 8702800692329 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452033971/2000000000 : ℝ)^4141 ≤ (6933186054671/50000000000000 : ℝ)^3117 := by
    have hnat : (452033971 : ℕ)^4141*50000000000000^3117 ≤ 6933186054671^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452033971 2000000000 6933186054671 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262607267/10000000000 : ℝ)^4141 ≤ (5327453052049/12500000000000 : ℝ)^3117 := by
    have hnat : (5262607267 : ℕ)^4141*12500000000000^3117 ≤ 5327453052049^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262607267 10000000000 5327453052049 12500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069104181/2000000000 : ℝ), (-452033971/2000000000 : ℝ), (5262607267/10000000000 : ℝ)] ![(8702800692329/20000000000000 : ℝ), (6933186054671/50000000000000 : ℝ), (5327453052049/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069104181/2000000000 : ℝ)|^4141 ≤ (8702800692329/20000000000000 : ℝ)^3117
        have hw : |(1069104181/2000000000 : ℝ)|=(1069104181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-452033971/2000000000 : ℝ)|^4141 ≤ (6933186054671/50000000000000 : ℝ)^3117
        have hw : |(-452033971/2000000000 : ℝ)|=(452033971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262607267/10000000000 : ℝ)|^4141 ≤ (5327453052049/12500000000000 : ℝ)^3117
        have hw : |(5262607267/10000000000 : ℝ)|=(5262607267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s5_2 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345520799/10000000000 : ℝ)*x 0 + (526260761/1000000000 : ℝ)*x 1 + (-1130084771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345520799/10000000000 : ℝ)^4141 ≤ (8702800463061/20000000000000 : ℝ)^3117 := by
    have hnat : (5345520799 : ℕ)^4141*20000000000000^3117 ≤ 8702800463061^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345520799 10000000000 8702800463061 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526260761/1000000000 : ℝ)^4141 ≤ (42619628106773/100000000000000 : ℝ)^3117 := by
    have hnat : (526260761 : ℕ)^4141*100000000000000^3117 ≤ 42619628106773^3117*1000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526260761 1000000000 42619628106773 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130084771/5000000000 : ℝ)^4141 ≤ (13866369558201/100000000000000 : ℝ)^3117 := by
    have hnat : (1130084771 : ℕ)^4141*100000000000000^3117 ≤ 13866369558201^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130084771 5000000000 13866369558201 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345520799/10000000000 : ℝ), (526260761/1000000000 : ℝ), (-1130084771/5000000000 : ℝ)] ![(8702800463061/20000000000000 : ℝ), (42619628106773/100000000000000 : ℝ), (13866369558201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345520799/10000000000 : ℝ)|^4141 ≤ (8702800463061/20000000000000 : ℝ)^3117
        have hw : |(5345520799/10000000000 : ℝ)|=(5345520799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526260761/1000000000 : ℝ)|^4141 ≤ (42619628106773/100000000000000 : ℝ)^3117
        have hw : |(526260761/1000000000 : ℝ)|=(526260761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1130084771/5000000000 : ℝ)|^4141 ≤ (13866369558201/100000000000000 : ℝ)^3117
        have hw : |(-1130084771/5000000000 : ℝ)|=(1130084771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s5_3 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2186037011/5000000000 : ℝ)*x 0 + (2121206547/5000000000 : ℝ)*x 1 + (225286469/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186037011/5000000000 : ℝ)^4141 ≤ (16657729515659/50000000000000 : ℝ)^3117 := by
    have hnat : (2186037011 : ℕ)^4141*50000000000000^3117 ≤ 16657729515659^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186037011 5000000000 16657729515659 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121206547/5000000000 : ℝ)^4141 ≤ (32009285850759/100000000000000 : ℝ)^3117 := by
    have hnat : (2121206547 : ℕ)^4141*100000000000000^3117 ≤ 32009285850759^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121206547 5000000000 32009285850759 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225286469/500000000 : ℝ)^4141 ≤ (3467525510019/10000000000000 : ℝ)^3117 := by
    have hnat : (225286469 : ℕ)^4141*10000000000000^3117 ≤ 3467525510019^3117*500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225286469 500000000 3467525510019 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186037011/5000000000 : ℝ), (2121206547/5000000000 : ℝ), (225286469/500000000 : ℝ)] ![(16657729515659/50000000000000 : ℝ), (32009285850759/100000000000000 : ℝ), (3467525510019/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186037011/5000000000 : ℝ)|^4141 ≤ (16657729515659/50000000000000 : ℝ)^3117
        have hw : |(2186037011/5000000000 : ℝ)|=(2186037011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2121206547/5000000000 : ℝ)|^4141 ≤ (32009285850759/100000000000000 : ℝ)^3117
        have hw : |(2121206547/5000000000 : ℝ)|=(2121206547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225286469/500000000 : ℝ)|^4141 ≤ (3467525510019/10000000000000 : ℝ)^3117
        have hw : |(225286469/500000000 : ℝ)|=(225286469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s5_4 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-274036127/1250000000 : ℝ)*x 0 + (1052590983/2000000000 : ℝ)*x 1 + (1079200543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274036127/1250000000 : ℝ)^4141 ≤ (3328962448671/25000000000000 : ℝ)^3117 := by
    have hnat : (274036127 : ℕ)^4141*25000000000000^3117 ≤ 3328962448671^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274036127 1250000000 3328962448671 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052590983/2000000000 : ℝ)^4141 ≤ (10655841211601/25000000000000 : ℝ)^3117 := by
    have hnat : (1052590983 : ℕ)^4141*25000000000000^3117 ≤ 10655841211601^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052590983 2000000000 10655841211601 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079200543/2000000000 : ℝ)^4141 ≤ (44060785338087/100000000000000 : ℝ)^3117 := by
    have hnat : (1079200543 : ℕ)^4141*100000000000000^3117 ≤ 44060785338087^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079200543 2000000000 44060785338087 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-274036127/1250000000 : ℝ), (1052590983/2000000000 : ℝ), (1079200543/2000000000 : ℝ)] ![(3328962448671/25000000000000 : ℝ), (10655841211601/25000000000000 : ℝ), (44060785338087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-274036127/1250000000 : ℝ)|^4141 ≤ (3328962448671/25000000000000 : ℝ)^3117
        have hw : |(-274036127/1250000000 : ℝ)|=(274036127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052590983/2000000000 : ℝ)|^4141 ≤ (10655841211601/25000000000000 : ℝ)^3117
        have hw : |(1052590983/2000000000 : ℝ)|=(1052590983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079200543/2000000000 : ℝ)|^4141 ≤ (44060785338087/100000000000000 : ℝ)^3117
        have hw : |(1079200543/2000000000 : ℝ)|=(1079200543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s5_5 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311772741/10000000000 : ℝ)*x 0 + (-1063387301/5000000000 : ℝ)*x 1 + (674500339/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311772741/10000000000 : ℝ)^4141 ≤ (21574706065411/50000000000000 : ℝ)^3117 := by
    have hnat : (5311772741 : ℕ)^4141*50000000000000^3117 ≤ 21574706065411^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311772741 10000000000 21574706065411 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063387301/5000000000 : ℝ)^4141 ≤ (639490127047/5000000000000 : ℝ)^3117 := by
    have hnat : (1063387301 : ℕ)^4141*5000000000000^3117 ≤ 639490127047^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063387301 5000000000 639490127047 5000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674500339/1250000000 : ℝ)^4141 ≤ (44060785305543/100000000000000 : ℝ)^3117 := by
    have hnat : (674500339 : ℕ)^4141*100000000000000^3117 ≤ 44060785305543^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674500339 1250000000 44060785305543 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311772741/10000000000 : ℝ), (-1063387301/5000000000 : ℝ), (674500339/1250000000 : ℝ)] ![(21574706065411/50000000000000 : ℝ), (639490127047/5000000000000 : ℝ), (44060785305543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311772741/10000000000 : ℝ)|^4141 ≤ (21574706065411/50000000000000 : ℝ)^3117
        have hw : |(5311772741/10000000000 : ℝ)|=(5311772741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1063387301/5000000000 : ℝ)|^4141 ≤ (639490127047/5000000000000 : ℝ)^3117
        have hw : |(-1063387301/5000000000 : ℝ)|=(1063387301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674500339/1250000000 : ℝ)|^4141 ≤ (44060785305543/100000000000000 : ℝ)^3117
        have hw : |(674500339/1250000000 : ℝ)|=(674500339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s5_6 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311772721/10000000000 : ℝ)*x 0 + (5396002733/10000000000 : ℝ)*x 1 + (-1063387301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311772721/10000000000 : ℝ)^4141 ≤ (43149411914981/100000000000000 : ℝ)^3117 := by
    have hnat : (5311772721 : ℕ)^4141*100000000000000^3117 ≤ 43149411914981^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311772721 10000000000 43149411914981 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396002733/10000000000 : ℝ)^4141 ≤ (44060785533351/100000000000000 : ℝ)^3117 := by
    have hnat : (5396002733 : ℕ)^4141*100000000000000^3117 ≤ 44060785533351^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396002733 10000000000 44060785533351 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063387301/5000000000 : ℝ)^4141 ≤ (639490127047/5000000000000 : ℝ)^3117 := by
    have hnat : (1063387301 : ℕ)^4141*5000000000000^3117 ≤ 639490127047^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063387301 5000000000 639490127047 5000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311772721/10000000000 : ℝ), (5396002733/10000000000 : ℝ), (-1063387301/5000000000 : ℝ)] ![(43149411914981/100000000000000 : ℝ), (44060785533351/100000000000000 : ℝ), (639490127047/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311772721/10000000000 : ℝ)|^4141 ≤ (43149411914981/100000000000000 : ℝ)^3117
        have hw : |(5311772721/10000000000 : ℝ)|=(5311772721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396002733/10000000000 : ℝ)|^4141 ≤ (44060785533351/100000000000000 : ℝ)^3117
        have hw : |(5396002733/10000000000 : ℝ)|=(5396002733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1063387301/5000000000 : ℝ)|^4141 ≤ (639490127047/5000000000000 : ℝ)^3117
        have hw : |(-1063387301/5000000000 : ℝ)|=(1063387301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s5_7 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546510623/1250000000 : ℝ)*x 0 + (2252522841/5000000000 : ℝ)*x 1 + (848619869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546510623/1250000000 : ℝ)^4141 ≤ (16657785002079/50000000000000 : ℝ)^3117 := by
    have hnat : (546510623 : ℕ)^4141*50000000000000^3117 ≤ 16657785002079^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546510623 1250000000 16657785002079 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252522841/5000000000 : ℝ)^4141 ≤ (17334132555747/50000000000000 : ℝ)^3117 := by
    have hnat : (2252522841 : ℕ)^4141*50000000000000^3117 ≤ 17334132555747^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252522841 5000000000 17334132555747 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848619869/2000000000 : ℝ)^4141 ≤ (32016164861503/100000000000000 : ℝ)^3117 := by
    have hnat : (848619869 : ℕ)^4141*100000000000000^3117 ≤ 32016164861503^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848619869 2000000000 32016164861503 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546510623/1250000000 : ℝ), (2252522841/5000000000 : ℝ), (848619869/2000000000 : ℝ)] ![(16657785002079/50000000000000 : ℝ), (17334132555747/50000000000000 : ℝ), (32016164861503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546510623/1250000000 : ℝ)|^4141 ≤ (16657785002079/50000000000000 : ℝ)^3117
        have hw : |(546510623/1250000000 : ℝ)|=(546510623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252522841/5000000000 : ℝ)|^4141 ≤ (17334132555747/50000000000000 : ℝ)^3117
        have hw : |(2252522841/5000000000 : ℝ)|=(2252522841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848619869/2000000000 : ℝ)|^4141 ≤ (32016164861503/100000000000000 : ℝ)^3117
        have hw : |(848619869/2000000000 : ℝ)|=(848619869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1089_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1107/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2247/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3517/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1107/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1107/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1107/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1107/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1107/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1107/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1107/10000 : ℝ) ^ (8281/2048 : ℝ) ≤ (1705933076323701/12500000000000000000 : ℝ) := by
    have hpowers : (1107/10000 : ℝ)^8281 ≤ (1705933076323701/12500000000000000000 : ℝ)^2048 := by
      have hnat : (1107 : ℕ)^8281*12500000000000000000^2048 ≤ 1705933076323701^2048*10000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1107 10000 1705933076323701 12500000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1107/10000 : ℝ)) (X := (1705933076323701/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (89/625 : ℝ) ^ (8281/2048 : ℝ) ≤ (2361206834966101/6250000000000000000 : ℝ) := by
    have hpowers : (89/625 : ℝ)^8281 ≤ (2361206834966101/6250000000000000000 : ℝ)^2048 := by
      have hnat : (89 : ℕ)^8281*6250000000000000000^2048 ≤ 2361206834966101^2048*625^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 625 2361206834966101 6250000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/625 : ℝ)) (X := (2361206834966101/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251705933076323701/6250000000000000000 : ℝ) ≤ (10000674970097349/10000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (6251705933076323701/6250000000000000000 : ℝ)^2048 ≤ (10000674970097349/10000000000000000 : ℝ)^8281 := by
      have hnat : (6251705933076323701 : ℕ)^2048*10000000000000000^8281 ≤ 10000674970097349^8281*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251705933076323701 6250000000000000000 10000674970097349 10000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000674970097349/10000000000000000 : ℝ)) (X := (6251705933076323701/6250000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506428346746255903/12500000000000000000 : ℝ) ≤ (19533733604577/19531250000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (12506428346746255903/12500000000000000000 : ℝ)^2048 ≤ (19533733604577/19531250000000 : ℝ)^8281 := by
      have hnat : (12506428346746255903 : ℕ)^2048*19531250000000^8281 ≤ 19533733604577^8281*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506428346746255903 12500000000000000000 19533733604577 19531250000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19533733604577/19531250000000 : ℝ)) (X := (12506428346746255903/12500000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127361206834966101/3125000000000000000 : ℝ) ≤ (10001868240989499/10000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (3127361206834966101/3125000000000000000 : ℝ)^2048 ≤ (10001868240989499/10000000000000000 : ℝ)^8281 := by
      have hnat : (3127361206834966101 : ℕ)^2048*10000000000000000^8281 ≤ 10001868240989499^8281*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127361206834966101 3125000000000000000 10001868240989499 10000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001868240989499/10000000000000000 : ℝ)) (X := (3127361206834966101/3125000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1705933076323701/12500000000000000000 : ℝ) ≤ ((3168893014643249583/3170000000000000000 : ℝ)+2*(23865417843/12680000000000 : ℝ)*(1107/10000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (3168893014643249583/3170000000000000000 : ℝ)+2*(23865417843/12680000000000 : ℝ)*(1107/10000 : ℝ)=(10000674970097349/10000000000000000 : ℝ) by norm_num, show 1+2*(1705933076323701/12500000000000000000 : ℝ)=(6251705933076323701/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2361206834966101/6250000000000000000 : ℝ)+(1705933076323701/12500000000000000000 : ℝ) ≤ ((3168893014643249583/3170000000000000000 : ℝ)+(23865417843/12680000000000 : ℝ)*((89/625 : ℝ)+(1107/10000 : ℝ)))^(8281/2048 : ℝ) := by
    rw [show (3168893014643249583/3170000000000000000 : ℝ)+(23865417843/12680000000000 : ℝ)*((89/625 : ℝ)+(1107/10000 : ℝ))=(19533733604577/19531250000000 : ℝ) by norm_num, show 1+(2361206834966101/6250000000000000000 : ℝ)+(1705933076323701/12500000000000000000 : ℝ)=(12506428346746255903/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2361206834966101/6250000000000000000 : ℝ) ≤ ((3168893014643249583/3170000000000000000 : ℝ)+2*(23865417843/12680000000000 : ℝ)*(89/625 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (3168893014643249583/3170000000000000000 : ℝ)+2*(23865417843/12680000000000 : ℝ)*(89/625 : ℝ)=(10001868240989499/10000000000000000 : ℝ) by norm_num, show 1+2*(2361206834966101/6250000000000000000 : ℝ)=(3127361206834966101/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3168893014643249583/3170000000000000000 : ℝ)*(X 1 0+X 2 0)+(23865417843/12680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (1107/10000 : ℝ)) (hi := (89/625 : ℝ)) (c := (3168893014643249583/3170000000000000000 : ℝ)) (alpha := (23865417843/12680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3168893014643249583/3170000000000000000 : ℝ)*(X 0 1+X 2 1)+(23865417843/12680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (1107/10000 : ℝ)) (hi := (89/625 : ℝ)) (c := (3168893014643249583/3170000000000000000 : ℝ)) (alpha := (23865417843/12680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3168893014643249583/3170000000000000000 : ℝ)*(X 0 2+X 1 2)+(23865417843/12680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (1107/10000 : ℝ)) (hi := (89/625 : ℝ)) (c := (3168893014643249583/3170000000000000000 : ℝ)) (alpha := (23865417843/12680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2192283383/10000000000 : ℝ)*X 0 0+(5396351239/10000000000 : ℝ)*X 0 1+(2631303869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069104181/2000000000 : ℝ)*X 1 0+(-452033971/2000000000 : ℝ)*X 1 1+(5262607267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345520799/10000000000 : ℝ)*X 2 0+(526260761/1000000000 : ℝ)*X 2 1+(-1130084771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186037011/5000000000 : ℝ)*X 0 0+(2121206547/5000000000 : ℝ)*X 0 1+(225286469/500000000 : ℝ)*X 0 2+(2186037011/5000000000 : ℝ)*X 1 0+(2121206547/5000000000 : ℝ)*X 1 1+(225286469/500000000 : ℝ)*X 1 2+(2186037011/5000000000 : ℝ)*X 2 0+(2121206547/5000000000 : ℝ)*X 2 1+(225286469/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-274036127/1250000000 : ℝ)*X 0 0+(1052590983/2000000000 : ℝ)*X 0 1+(1079200543/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311772741/10000000000 : ℝ)*X 1 0+(-1063387301/5000000000 : ℝ)*X 1 1+(674500339/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311772721/10000000000 : ℝ)*X 2 0+(5396002733/10000000000 : ℝ)*X 2 1+(-1063387301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546510623/1250000000 : ℝ)*X 0 0+(2252522841/5000000000 : ℝ)*X 0 1+(848619869/2000000000 : ℝ)*X 0 2+(546510623/1250000000 : ℝ)*X 1 0+(2252522841/5000000000 : ℝ)*X 1 1+(848619869/2000000000 : ℝ)*X 1 2+(546510623/1250000000 : ℝ)*X 2 0+(2252522841/5000000000 : ℝ)*X 2 1+(848619869/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1116477017552787303543/317000000000000000000000000 : ℝ) := by norm_num
    linear_combination (635413793/50000000000000 : ℝ)*(base19) + (1046081769/100000000000000 : ℝ)*(base23) + (36979631/50000000000000 : ℝ)*(lower2) + (46597753/50000000000000 : ℝ)*(upper5) + (281869870742681/5000000000000 : ℝ)*(major0) + (281869870742681/5000000000000 : ℝ)*(major1) + (281869870742681/5000000000000 : ℝ)*(major2) + (3738510840897937/50000000000000 : ℝ)*(sp0) + (7477039142732653/100000000000000 : ℝ)*(sp1) + (7477049168793157/100000000000000 : ℝ)*(sp2) + (379773008713673/10000000000000 : ℝ)*(sp3) + (7133269763/25000000000000 : ℝ)*(sp4) + (9801314687/100000000000000 : ℝ)*(sp5) + (7205147629/50000000000000 : ℝ)*(sp7) + (949436124357997/25000000000000 : ℝ)*(f.failure) + (3738525107437463/50000000000000 : ℝ)*(f.sum) + (12808564293/39625000000000000000000000 : ℝ)*base65 + (183237523891397977/15850000000000000000000000000000 : ℝ)*base68 + (45687424982602023/15850000000000000000000000000000 : ℝ)*base69 + (118766079094902023/15850000000000000000000000000000 : ℝ)*base71 + (1795278717949/317000000000000000000000000 : ℝ)*base74 + (429541877669947977/15850000000000000000000000000000 : ℝ)*base76 + (13122430680552023/15850000000000000000000000000000 : ℝ)*base77 + (299452835309797977/15850000000000000000000000000000 : ℝ)*base80 + (739574541171/158500000000000000000000000 : ℝ)*base82 + (18895987/2500000000000000000000 : ℝ)*base89 + (18895987/2500000000000000000000 : ℝ)*base91 + (18895987/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43455671388191067040103271/3962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65028703/3125000000000 : ℝ)*(base19) + (2230353283/100000000000000 : ℝ)*(base23) + (56949797/25000000000000 : ℝ)*(upper3) + (39812631/50000000000000 : ℝ)*(lower4) + (216935471/100000000000000 : ℝ)*(upper5) + (141670856389521/2500000000000 : ℝ)*(major0) + (141670856389521/2500000000000 : ℝ)*(major1) + (141670856389521/2500000000000 : ℝ)*(major2) + (13643649821/25000000000000 : ℝ)*(sp1) + (29477610021/50000000000000 : ℝ)*(sp2) + (7516092937000369/100000000000000 : ℝ)*(sp4) + (7516036281482589/100000000000000 : ℝ)*(sp5) + (7516031751427043/100000000000000 : ℝ)*(sp6) + (954393802150901/25000000000000 : ℝ)*(sp7) + (954393802150901/25000000000000 : ℝ)*(f.failure) + (7516092937000369/100000000000000 : ℝ)*(f.sum) + (350137808029/79250000000000000000000000 : ℝ)*base65 + (93291360317205257/7925000000000000000000000000000 : ℝ)*base68 + (58996710440694743/7925000000000000000000000000000 : ℝ)*base69 + (69410322189944743/7925000000000000000000000000000 : ℝ)*base71 + (10967384739/6340000000000000000000000 : ℝ)*base74 + (89617512779769743/7925000000000000000000000000000 : ℝ)*base75 + (10041044864155257/7925000000000000000000000000000 : ℝ)*base78 + (21252908488594743/7925000000000000000000000000000 : ℝ)*base79 + (17598961213/6340000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12305429/2500000000000000000000 : ℝ)*base90 + (12305429/2500000000000000000000 : ℝ)*base92 + (12305429/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1089_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1107/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1089_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1089_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8823/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1089_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1089_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1089_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8823/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1089_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
