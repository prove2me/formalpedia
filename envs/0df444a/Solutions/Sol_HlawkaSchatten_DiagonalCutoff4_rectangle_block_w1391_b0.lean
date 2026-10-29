-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1391_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:42.627979+00:00
-- url     : https://prove2.me/submissions/62cb5ae1-cc34-428f-88e5-09e5c9db875c

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
theorem support_rectangle_w1391_s0_0 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1780530843/10000000000 : ℝ)*x 0 + (2988010369/5000000000 : ℝ)*x 1 + (2411232279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1780530843/10000000000 : ℝ)^4351 ≤ (5234196710379/50000000000000 : ℝ)^3327 := by
    have hnat : (1780530843 : ℕ)^4351*50000000000000^3327 ≤ 5234196710379^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780530843 10000000000 5234196710379 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2988010369/5000000000 : ℝ)^4351 ≤ (159384161211/312500000000 : ℝ)^3327 := by
    have hnat : (2988010369 : ℕ)^4351*312500000000^3327 ≤ 159384161211^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2988010369 5000000000 159384161211 312500000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2411232279/5000000000 : ℝ)^4351 ≤ (19264337486131/50000000000000 : ℝ)^3327 := by
    have hnat : (2411232279 : ℕ)^4351*50000000000000^3327 ≤ 19264337486131^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411232279 5000000000 19264337486131 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1780530843/10000000000 : ℝ), (2988010369/5000000000 : ℝ), (2411232279/5000000000 : ℝ)] ![(5234196710379/50000000000000 : ℝ), (159384161211/312500000000 : ℝ), (19264337486131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1780530843/10000000000 : ℝ)|^4351 ≤ (5234196710379/50000000000000 : ℝ)^3327
        have hw : |(-1780530843/10000000000 : ℝ)|=(1780530843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2988010369/5000000000 : ℝ)|^4351 ≤ (159384161211/312500000000 : ℝ)^3327
        have hw : |(2988010369/5000000000 : ℝ)|=(2988010369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2411232279/5000000000 : ℝ)|^4351 ≤ (19264337486131/50000000000000 : ℝ)^3327
        have hw : |(2411232279/5000000000 : ℝ)|=(2411232279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s0_1 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (343520847/625000000 : ℝ)*x 0 + (-1216953647/5000000000 : ℝ)*x 1 + (150702021/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343520847/625000000 : ℝ)^4351 ≤ (4571634778851/10000000000000 : ℝ)^3327 := by
    have hnat : (343520847 : ℕ)^4351*10000000000000^3327 ≤ 4571634778851^3327*625000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343520847 625000000 4571634778851 10000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1216953647/5000000000 : ℝ)^4351 ≤ (15754976036967/100000000000000 : ℝ)^3327 := by
    have hnat : (1216953647 : ℕ)^4351*100000000000000^3327 ≤ 15754976036967^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216953647 5000000000 15754976036967 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150702021/312500000 : ℝ)^4351 ≤ (4816084520423/12500000000000 : ℝ)^3327 := by
    have hnat : (150702021 : ℕ)^4351*12500000000000^3327 ≤ 4816084520423^3327*312500000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150702021 312500000 4816084520423 12500000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343520847/625000000 : ℝ), (-1216953647/5000000000 : ℝ), (150702021/312500000 : ℝ)] ![(4571634778851/10000000000000 : ℝ), (15754976036967/100000000000000 : ℝ), (4816084520423/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343520847/625000000 : ℝ)|^4351 ≤ (4571634778851/10000000000000 : ℝ)^3327
        have hw : |(343520847/625000000 : ℝ)|=(343520847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1216953647/5000000000 : ℝ)|^4351 ≤ (15754976036967/100000000000000 : ℝ)^3327
        have hw : |(-1216953647/5000000000 : ℝ)|=(1216953647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(150702021/312500000 : ℝ)|^4351 ≤ (4816084520423/12500000000000 : ℝ)^3327
        have hw : |(150702021/312500000 : ℝ)|=(150702021/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s0_2 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1374083391/2500000000 : ℝ)*x 0 + (4822464643/10000000000 : ℝ)*x 1 + (-1216953657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374083391/2500000000 : ℝ)^4351 ≤ (45716347919041/100000000000000 : ℝ)^3327 := by
    have hnat : (1374083391 : ℕ)^4351*100000000000000^3327 ≤ 45716347919041^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374083391 2500000000 45716347919041 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4822464643/10000000000 : ℝ)^4351 ≤ (38528675860379/100000000000000 : ℝ)^3327 := by
    have hnat : (4822464643 : ℕ)^4351*100000000000000^3327 ≤ 38528675860379^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4822464643 10000000000 38528675860379 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216953657/5000000000 : ℝ)^4351 ≤ (3938744051569/25000000000000 : ℝ)^3327 := by
    have hnat : (1216953657 : ℕ)^4351*25000000000000^3327 ≤ 3938744051569^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216953657 5000000000 3938744051569 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374083391/2500000000 : ℝ), (4822464643/10000000000 : ℝ), (-1216953657/5000000000 : ℝ)] ![(45716347919041/100000000000000 : ℝ), (38528675860379/100000000000000 : ℝ), (3938744051569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374083391/2500000000 : ℝ)|^4351 ≤ (45716347919041/100000000000000 : ℝ)^3327
        have hw : |(1374083391/2500000000 : ℝ)|=(1374083391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4822464643/10000000000 : ℝ)|^4351 ≤ (38528675860379/100000000000000 : ℝ)^3327
        have hw : |(4822464643/10000000000 : ℝ)|=(4822464643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1216953657/5000000000 : ℝ)|^4351 ≤ (3938744051569/25000000000000 : ℝ)^3327
        have hw : |(-1216953657/5000000000 : ℝ)|=(1216953657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s0_3 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2085750591/5000000000 : ℝ)*x 0 + (3104492251/10000000000 : ℝ)*x 1 + (2782659011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085750591/5000000000 : ℝ)^4351 ≤ (31873087698707/100000000000000 : ℝ)^3327 := by
    have hnat : (2085750591 : ℕ)^4351*100000000000000^3327 ≤ 31873087698707^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085750591 5000000000 31873087698707 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104492251/10000000000 : ℝ)^4351 ≤ (10829365489339/50000000000000 : ℝ)^3327 := by
    have hnat : (3104492251 : ℕ)^4351*50000000000000^3327 ≤ 10829365489339^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104492251 10000000000 10829365489339 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2782659011/5000000000 : ℝ)^4351 ≤ (9293636260851/20000000000000 : ℝ)^3327 := by
    have hnat : (2782659011 : ℕ)^4351*20000000000000^3327 ≤ 9293636260851^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782659011 5000000000 9293636260851 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2085750591/5000000000 : ℝ), (3104492251/10000000000 : ℝ), (2782659011/5000000000 : ℝ)] ![(31873087698707/100000000000000 : ℝ), (10829365489339/50000000000000 : ℝ), (9293636260851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2085750591/5000000000 : ℝ)|^4351 ≤ (31873087698707/100000000000000 : ℝ)^3327
        have hw : |(2085750591/5000000000 : ℝ)|=(2085750591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104492251/10000000000 : ℝ)|^4351 ≤ (10829365489339/50000000000000 : ℝ)^3327
        have hw : |(3104492251/10000000000 : ℝ)|=(3104492251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2782659011/5000000000 : ℝ)|^4351 ≤ (9293636260851/20000000000000 : ℝ)^3327
        have hw : |(2782659011/5000000000 : ℝ)|=(2782659011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s0_4 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1784736211/10000000000 : ℝ)*x 0 + (4852060769/10000000000 : ℝ)*x 1 + (2972683337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1784736211/10000000000 : ℝ)^4351 ≤ (2625185003781/25000000000000 : ℝ)^3327 := by
    have hnat : (1784736211 : ℕ)^4351*25000000000000^3327 ≤ 2625185003781^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784736211 10000000000 2625185003781 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4852060769/10000000000 : ℝ)^4351 ≤ (38838200753457/100000000000000 : ℝ)^3327 := by
    have hnat : (4852060769 : ℕ)^4351*100000000000000^3327 ≤ 38838200753457^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4852060769 10000000000 38838200753457 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2972683337/5000000000 : ℝ)^4351 ≤ (12665264802037/25000000000000 : ℝ)^3327 := by
    have hnat : (2972683337 : ℕ)^4351*25000000000000^3327 ≤ 12665264802037^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2972683337 5000000000 12665264802037 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1784736211/10000000000 : ℝ), (4852060769/10000000000 : ℝ), (2972683337/5000000000 : ℝ)] ![(2625185003781/25000000000000 : ℝ), (38838200753457/100000000000000 : ℝ), (12665264802037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1784736211/10000000000 : ℝ)|^4351 ≤ (2625185003781/25000000000000 : ℝ)^3327
        have hw : |(-1784736211/10000000000 : ℝ)|=(1784736211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4852060769/10000000000 : ℝ)|^4351 ≤ (38838200753457/100000000000000 : ℝ)^3327
        have hw : |(4852060769/10000000000 : ℝ)|=(4852060769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2972683337/5000000000 : ℝ)|^4351 ≤ (12665264802037/25000000000000 : ℝ)^3327
        have hw : |(2972683337/5000000000 : ℝ)|=(2972683337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s0_5 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518167267/1000000000 : ℝ)*x 0 + (-1311005509/10000000000 : ℝ)*x 1 + (1486341137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518167267/1000000000 : ℝ)^4351 ≤ (42324143253847/100000000000000 : ℝ)^3327 := by
    have hnat : (518167267 : ℕ)^4351*100000000000000^3327 ≤ 42324143253847^3327*1000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518167267 1000000000 42324143253847 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311005509/10000000000 : ℝ)^4351 ≤ (3507410610629/50000000000000 : ℝ)^3327 := by
    have hnat : (1311005509 : ℕ)^4351*50000000000000^3327 ≤ 3507410610629^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311005509 10000000000 3507410610629 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1486341137/2500000000 : ℝ)^4351 ≤ (50661035516507/100000000000000 : ℝ)^3327 := by
    have hnat : (1486341137 : ℕ)^4351*100000000000000^3327 ≤ 50661035516507^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486341137 2500000000 50661035516507 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518167267/1000000000 : ℝ), (-1311005509/10000000000 : ℝ), (1486341137/2500000000 : ℝ)] ![(42324143253847/100000000000000 : ℝ), (3507410610629/50000000000000 : ℝ), (50661035516507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518167267/1000000000 : ℝ)|^4351 ≤ (42324143253847/100000000000000 : ℝ)^3327
        have hw : |(518167267/1000000000 : ℝ)|=(518167267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1311005509/10000000000 : ℝ)|^4351 ≤ (3507410610629/50000000000000 : ℝ)^3327
        have hw : |(-1311005509/10000000000 : ℝ)|=(1311005509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1486341137/2500000000 : ℝ)|^4351 ≤ (50661035516507/100000000000000 : ℝ)^3327
        have hw : |(1486341137/2500000000 : ℝ)|=(1486341137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s0_6 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2590834173/5000000000 : ℝ)*x 0 + (297268487/500000000 : ℝ)*x 1 + (-1311003841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2590834173/5000000000 : ℝ)^4351 ≤ (42324097064681/100000000000000 : ℝ)^3327 := by
    have hnat : (2590834173 : ℕ)^4351*100000000000000^3327 ≤ 42324097064681^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590834173 5000000000 42324097064681 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297268487/500000000 : ℝ)^4351 ≤ (50661093374931/100000000000000 : ℝ)^3327 := by
    have hnat : (297268487 : ℕ)^4351*100000000000000^3327 ≤ 50661093374931^3327*500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297268487 500000000 50661093374931 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311003841/10000000000 : ℝ)^4351 ≤ (1753702387321/25000000000000 : ℝ)^3327 := by
    have hnat : (1311003841 : ℕ)^4351*25000000000000^3327 ≤ 1753702387321^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311003841 10000000000 1753702387321 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2590834173/5000000000 : ℝ), (297268487/500000000 : ℝ), (-1311003841/10000000000 : ℝ)] ![(42324097064681/100000000000000 : ℝ), (50661093374931/100000000000000 : ℝ), (1753702387321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2590834173/5000000000 : ℝ)|^4351 ≤ (42324097064681/100000000000000 : ℝ)^3327
        have hw : |(2590834173/5000000000 : ℝ)|=(2590834173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(297268487/500000000 : ℝ)|^4351 ≤ (50661093374931/100000000000000 : ℝ)^3327
        have hw : |(297268487/500000000 : ℝ)|=(297268487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1311003841/10000000000 : ℝ)|^4351 ≤ (1753702387321/25000000000000 : ℝ)^3327
        have hw : |(-1311003841/10000000000 : ℝ)|=(1311003841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s0_7 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045116123/2500000000 : ℝ)*x 0 + (5502183737/10000000000 : ℝ)*x 1 + (792472163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045116123/2500000000 : ℝ)^4351 ≤ (31962681915817/100000000000000 : ℝ)^3327 := by
    have hnat : (1045116123 : ℕ)^4351*100000000000000^3327 ≤ 31962681915817^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045116123 2500000000 31962681915817 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502183737/10000000000 : ℝ)^4351 ≤ (2861249651437/6250000000000 : ℝ)^3327 := by
    have hnat : (5502183737 : ℕ)^4351*6250000000000^3327 ≤ 2861249651437^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502183737 10000000000 2861249651437 6250000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (792472163/2500000000 : ℝ)^4351 ≤ (22257323651661/100000000000000 : ℝ)^3327 := by
    have hnat : (792472163 : ℕ)^4351*100000000000000^3327 ≤ 22257323651661^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792472163 2500000000 22257323651661 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045116123/2500000000 : ℝ), (5502183737/10000000000 : ℝ), (792472163/2500000000 : ℝ)] ![(31962681915817/100000000000000 : ℝ), (2861249651437/6250000000000 : ℝ), (22257323651661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045116123/2500000000 : ℝ)|^4351 ≤ (31962681915817/100000000000000 : ℝ)^3327
        have hw : |(1045116123/2500000000 : ℝ)|=(1045116123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502183737/10000000000 : ℝ)|^4351 ≤ (2861249651437/6250000000000 : ℝ)^3327
        have hw : |(5502183737/10000000000 : ℝ)|=(5502183737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(792472163/2500000000 : ℝ)|^4351 ≤ (22257323651661/100000000000000 : ℝ)^3327
        have hw : |(792472163/2500000000 : ℝ)|=(792472163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1391_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (111/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26523/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2175/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2175 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2175*1^512 ≤ 0^512*1^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2175/512 : ℝ) ≤ (1019769911917690379/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2175 ≤ (1019769911917690379/50000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2175*50000000000000000000^512 ≤ 1019769911917690379^512*5^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1019769911917690379 50000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1019769911917690379/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2175 := by
      have hnat : (1 : ℕ)^512*1^2175 ≤ 1^2175*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (51019769911917690379/50000000000000000000 : ℝ) ≤ (5023820657338223/5000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (51019769911917690379/50000000000000000000 : ℝ)^512 ≤ (5023820657338223/5000000000000000 : ℝ)^2175 := by
      have hnat : (51019769911917690379 : ℕ)^512*5000000000000000^2175 ≤ 5023820657338223^2175*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51019769911917690379 50000000000000000000 5023820657338223 5000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5023820657338223/5000000000000000 : ℝ)) (X := (51019769911917690379/50000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (26019769911917690379/25000000000000000000 : ℝ) ≤ (2523820657338223/2500000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (26019769911917690379/25000000000000000000 : ℝ)^512 ≤ (2523820657338223/2500000000000000 : ℝ)^2175 := by
      have hnat : (26019769911917690379 : ℕ)^512*2500000000000000^2175 ≤ 2523820657338223^2175*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26019769911917690379 25000000000000000000 2523820657338223 2500000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2523820657338223/2500000000000000 : ℝ)) (X := (26019769911917690379/25000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(23820657338223/2000000000000000 : ℝ)*(0 : ℝ))^(2175/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(23820657338223/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1019769911917690379/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(23820657338223/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2175/512 : ℝ) := by
    rw [show (1 : ℝ)+(23820657338223/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5023820657338223/5000000000000000 : ℝ) by norm_num, show 1+(1019769911917690379/50000000000000000000 : ℝ)+(0 : ℝ)=(51019769911917690379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1019769911917690379/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(23820657338223/2000000000000000 : ℝ)*(2/5 : ℝ))^(2175/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(23820657338223/2000000000000000 : ℝ)*(2/5 : ℝ)=(2523820657338223/2500000000000000 : ℝ) by norm_num, show 1+2*(1019769911917690379/50000000000000000000 : ℝ)=(26019769911917690379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(23820657338223/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23820657338223/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(23820657338223/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23820657338223/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(23820657338223/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23820657338223/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1780530843/10000000000 : ℝ)*X 0 0+(2988010369/5000000000 : ℝ)*X 0 1+(2411232279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((343520847/625000000 : ℝ)*X 1 0+(-1216953647/5000000000 : ℝ)*X 1 1+(150702021/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1374083391/2500000000 : ℝ)*X 2 0+(4822464643/10000000000 : ℝ)*X 2 1+(-1216953657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2085750591/5000000000 : ℝ)*X 0 0+(3104492251/10000000000 : ℝ)*X 0 1+(2782659011/5000000000 : ℝ)*X 0 2+(2085750591/5000000000 : ℝ)*X 1 0+(3104492251/10000000000 : ℝ)*X 1 1+(2782659011/5000000000 : ℝ)*X 1 2+(2085750591/5000000000 : ℝ)*X 2 0+(3104492251/10000000000 : ℝ)*X 2 1+(2782659011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1784736211/10000000000 : ℝ)*X 0 0+(4852060769/10000000000 : ℝ)*X 0 1+(2972683337/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518167267/1000000000 : ℝ)*X 1 0+(-1311005509/10000000000 : ℝ)*X 1 1+(1486341137/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2590834173/5000000000 : ℝ)*X 2 0+(297268487/500000000 : ℝ)*X 2 1+(-1311003841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1045116123/2500000000 : ℝ)*X 0 0+(5502183737/10000000000 : ℝ)*X 0 1+(792472163/2500000000 : ℝ)*X 0 2+(1045116123/2500000000 : ℝ)*X 1 0+(5502183737/10000000000 : ℝ)*X 1 1+(792472163/2500000000 : ℝ)*X 1 2+(1045116123/2500000000 : ℝ)*X 2 0+(5502183737/10000000000 : ℝ)*X 2 1+(792472163/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38574825267681191774397/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15692993/100000000000000 : ℝ)*(base1) + (727229857/100000000000000 : ℝ)*(base19) + (729122513/100000000000000 : ℝ)*(base23) + (93863099/100000000000000 : ℝ)*(upper3) + (89184481/100000000000000 : ℝ)*(upper5) + (159157448110771/25000000000000 : ℝ)*(major0) + (159157448110771/25000000000000 : ℝ)*(major1) + (159157448110771/25000000000000 : ℝ)*(major2) + (27090217392693/3125000000000 : ℝ)*(sp0) + (433444375754077/50000000000000 : ℝ)*(sp1) + (433444374807749/50000000000000 : ℝ)*(sp2) + (203184391673753/50000000000000 : ℝ)*(sp3) + (634466207/25000000000000 : ℝ)*(sp4) + (24084829/2000000000000 : ℝ)*(sp7) + (101592500820487/25000000000000 : ℝ)*(f.failure) + (866889478738011/100000000000000 : ℝ)*(f.sum) + (61978394100067/25000000000000000000000000000 : ℝ)*base66 + (708309347500067/50000000000000000000000000000 : ℝ)*base68 + (411586624300067/50000000000000000000000000000 : ℝ)*base70 + (423787508700067/50000000000000000000000000000 : ℝ)*base72 + (124116068200067/25000000000000000000000000000 : ℝ)*base74 + (348356784700067/50000000000000000000000000000 : ℝ)*base76 + (239797101900067/50000000000000000000000000000 : ℝ)*base78 + (555346677200067/50000000000000000000000000000 : ℝ)*base80 + (66021737700067/25000000000000000000000000000 : ℝ)*base82 + (4516753/500000000000000000000 : ℝ)*base89 + (4516753/500000000000000000000 : ℝ)*base91 + (4516753/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (878459529370389094505109/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399432657/25000000000000 : ℝ)*(base19) + (8364769/500000000000 : ℝ)*(base23) + (374076833/100000000000000 : ℝ)*(base39) + (55101517/25000000000000 : ℝ)*(upper2) + (1321869/400000000000 : ℝ)*(upper5) + (671707928046981/100000000000000 : ℝ)*(major0) + (671707928046981/100000000000000 : ℝ)*(major1) + (167926888492537/25000000000000 : ℝ)*(major2) + (807491441/20000000000000 : ℝ)*(sp1) + (241100797/5000000000000 : ℝ)*(sp2) + (182930860933797/20000000000000 : ℝ)*(sp4) + (914648669481153/100000000000000 : ℝ)*(sp5) + (457324091888039/50000000000000 : ℝ)*(sp6) + (85752176905659/20000000000000 : ℝ)*(sp7) + (85752176905659/20000000000000 : ℝ)*(f.failure) + (457327339372909/50000000000000 : ℝ)*(f.sum) + (608870971421767/200000000000000000000000000000 : ℝ)*base65 + (41199026341751/50000000000000000000000000000 : ℝ)*base67 + (742071505054763/200000000000000000000000000000 : ℝ)*base69 + (26811829841751/50000000000000000000000000000 : ℝ)*base71 + (222945378821767/200000000000000000000000000000 : ℝ)*base73 + (538792437745237/200000000000000000000000000000 : ℝ)*base76 + (743546693454763/200000000000000000000000000000 : ℝ)*base77 + (1009868840054763/200000000000000000000000000000 : ℝ)*base79 + (88743592854763/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2174979/400000000000000000000 : ℝ)*base90 + (2174979/400000000000000000000 : ℝ)*base92 + (2174979/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1391_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (111/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26523/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1391_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1391_s1_0 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-979149167/5000000000 : ℝ)*x 0 + (2810419487/5000000000 : ℝ)*x 1 + (632967957/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979149167/5000000000 : ℝ)^4351 ≤ (11855774643767/100000000000000 : ℝ)^3327 := by
    have hnat : (979149167 : ℕ)^4351*100000000000000^3327 ≤ 11855774643767^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979149167 5000000000 11855774643767 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2810419487/5000000000 : ℝ)^4351 ≤ (4707536988629/10000000000000 : ℝ)^3327 := by
    have hnat : (2810419487 : ℕ)^4351*10000000000000^3327 ≤ 4707536988629^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2810419487 5000000000 4707536988629 10000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632967957/1250000000 : ℝ)^4351 ≤ (10267213864639/25000000000000 : ℝ)^3327 := by
    have hnat : (632967957 : ℕ)^4351*25000000000000^3327 ≤ 10267213864639^3327*1250000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632967957 1250000000 10267213864639 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-979149167/5000000000 : ℝ), (2810419487/5000000000 : ℝ), (632967957/1250000000 : ℝ)] ![(11855774643767/100000000000000 : ℝ), (4707536988629/10000000000000 : ℝ), (10267213864639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-979149167/5000000000 : ℝ)|^4351 ≤ (11855774643767/100000000000000 : ℝ)^3327
        have hw : |(-979149167/5000000000 : ℝ)|=(979149167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2810419487/5000000000 : ℝ)|^4351 ≤ (4707536988629/10000000000000 : ℝ)^3327
        have hw : |(2810419487/5000000000 : ℝ)|=(2810419487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(632967957/1250000000 : ℝ)|^4351 ≤ (10267213864639/25000000000000 : ℝ)^3327
        have hw : |(632967957/1250000000 : ℝ)|=(632967957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s1_1 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080131821/2000000000 : ℝ)*x 0 + (-2254373161/10000000000 : ℝ)*x 1 + (5063745071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080131821/2000000000 : ℝ)^4351 ≤ (2233921731013/5000000000000 : ℝ)^3327 := by
    have hnat : (1080131821 : ℕ)^4351*5000000000000^3327 ≤ 2233921731013^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080131821 2000000000 2233921731013 5000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254373161/10000000000 : ℝ)^4351 ≤ (7126347442237/50000000000000 : ℝ)^3327 := by
    have hnat : (2254373161 : ℕ)^4351*50000000000000^3327 ≤ 7126347442237^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254373161 10000000000 7126347442237 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5063745071/10000000000 : ℝ)^4351 ≤ (4106887046693/10000000000000 : ℝ)^3327 := by
    have hnat : (5063745071 : ℕ)^4351*10000000000000^3327 ≤ 4106887046693^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5063745071 10000000000 4106887046693 10000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080131821/2000000000 : ℝ), (-2254373161/10000000000 : ℝ), (5063745071/10000000000 : ℝ)] ![(2233921731013/5000000000000 : ℝ), (7126347442237/50000000000000 : ℝ), (4106887046693/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080131821/2000000000 : ℝ)|^4351 ≤ (2233921731013/5000000000000 : ℝ)^3327
        have hw : |(1080131821/2000000000 : ℝ)|=(1080131821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2254373161/10000000000 : ℝ)|^4351 ≤ (7126347442237/50000000000000 : ℝ)^3327
        have hw : |(-2254373161/10000000000 : ℝ)|=(2254373161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5063745071/10000000000 : ℝ)|^4351 ≤ (4106887046693/10000000000000 : ℝ)^3327
        have hw : |(5063745071/10000000000 : ℝ)|=(5063745071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s1_2 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400659973/10000000000 : ℝ)*x 0 + (2531871919/5000000000 : ℝ)*x 1 + (-281796701/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400659973/10000000000 : ℝ)^4351 ≤ (1116961100279/2500000000000 : ℝ)^3327 := by
    have hnat : (5400659973 : ℕ)^4351*2500000000000^3327 ≤ 1116961100279^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400659973 10000000000 1116961100279 2500000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2531871919/5000000000 : ℝ)^4351 ≤ (20534428694481/50000000000000 : ℝ)^3327 := by
    have hnat : (2531871919 : ℕ)^4351*50000000000000^3327 ≤ 20534428694481^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2531871919 5000000000 20534428694481 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281796701/1250000000 : ℝ)^4351 ≤ (1425269858033/10000000000000 : ℝ)^3327 := by
    have hnat : (281796701 : ℕ)^4351*10000000000000^3327 ≤ 1425269858033^3327*1250000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281796701 1250000000 1425269858033 10000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400659973/10000000000 : ℝ), (2531871919/5000000000 : ℝ), (-281796701/1250000000 : ℝ)] ![(1116961100279/2500000000000 : ℝ), (20534428694481/50000000000000 : ℝ), (1425269858033/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400659973/10000000000 : ℝ)|^4351 ≤ (1116961100279/2500000000000 : ℝ)^3327
        have hw : |(5400659973/10000000000 : ℝ)|=(5400659973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2531871919/5000000000 : ℝ)|^4351 ≤ (20534428694481/50000000000000 : ℝ)^3327
        have hw : |(2531871919/5000000000 : ℝ)|=(2531871919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281796701/1250000000 : ℝ)|^4351 ≤ (1425269858033/10000000000000 : ℝ)^3327
        have hw : |(-281796701/1250000000 : ℝ)|=(281796701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s1_3 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (856703957/2000000000 : ℝ)*x 0 + (3726703021/10000000000 : ℝ)*x 1 + (2457561831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856703957/2000000000 : ℝ)^4351 ≤ (16498507580569/50000000000000 : ℝ)^3327 := by
    have hnat : (856703957 : ℕ)^4351*50000000000000^3327 ≤ 16498507580569^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856703957 2000000000 16498507580569 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3726703021/10000000000 : ℝ)^4351 ≤ (27503316973787/100000000000000 : ℝ)^3327 := by
    have hnat : (3726703021 : ℕ)^4351*100000000000000^3327 ≤ 27503316973787^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726703021 10000000000 27503316973787 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2457561831/5000000000 : ℝ)^4351 ≤ (1579986714167/4000000000000 : ℝ)^3327 := by
    have hnat : (2457561831 : ℕ)^4351*4000000000000^3327 ≤ 1579986714167^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2457561831 5000000000 1579986714167 4000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(856703957/2000000000 : ℝ), (3726703021/10000000000 : ℝ), (2457561831/5000000000 : ℝ)] ![(16498507580569/50000000000000 : ℝ), (27503316973787/100000000000000 : ℝ), (1579986714167/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(856703957/2000000000 : ℝ)|^4351 ≤ (16498507580569/50000000000000 : ℝ)^3327
        have hw : |(856703957/2000000000 : ℝ)|=(856703957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3726703021/10000000000 : ℝ)|^4351 ≤ (27503316973787/100000000000000 : ℝ)^3327
        have hw : |(3726703021/10000000000 : ℝ)|=(3726703021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2457561831/5000000000 : ℝ)|^4351 ≤ (1579986714167/4000000000000 : ℝ)^3327
        have hw : |(2457561831/5000000000 : ℝ)|=(2457561831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s1_4 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61210999/312500000 : ℝ)*x 0 + (1014094801/2000000000 : ℝ)*x 1 + (1122798171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61210999/312500000 : ℝ)^4351 ≤ (5929683206567/50000000000000 : ℝ)^3327 := by
    have hnat : (61210999 : ℕ)^4351*50000000000000^3327 ≤ 5929683206567^3327*312500000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61210999 312500000 5929683206567 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014094801/2000000000 : ℝ)^4351 ≤ (8228051267249/20000000000000 : ℝ)^3327 := by
    have hnat : (1014094801 : ℕ)^4351*20000000000000^3327 ≤ 8228051267249^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014094801 2000000000 8228051267249 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122798171/2000000000 : ℝ)^4351 ≤ (470003772329/1000000000000 : ℝ)^3327 := by
    have hnat : (1122798171 : ℕ)^4351*1000000000000^3327 ≤ 470003772329^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122798171 2000000000 470003772329 1000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61210999/312500000 : ℝ), (1014094801/2000000000 : ℝ), (1122798171/2000000000 : ℝ)] ![(5929683206567/50000000000000 : ℝ), (8228051267249/20000000000000 : ℝ), (470003772329/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61210999/312500000 : ℝ)|^4351 ≤ (5929683206567/50000000000000 : ℝ)^3327
        have hw : |(-61210999/312500000 : ℝ)|=(61210999/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014094801/2000000000 : ℝ)|^4351 ≤ (8228051267249/20000000000000 : ℝ)^3327
        have hw : |(1014094801/2000000000 : ℝ)|=(1014094801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122798171/2000000000 : ℝ)|^4351 ≤ (470003772329/1000000000000 : ℝ)^3327
        have hw : |(1122798171/2000000000 : ℝ)|=(1122798171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s1_5 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313881527/2500000000 : ℝ)*x 0 + (-852063613/5000000000 : ℝ)*x 1 + (5613990877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313881527/2500000000 : ℝ)^4351 ≤ (5389346734659/12500000000000 : ℝ)^3327 := by
    have hnat : (1313881527 : ℕ)^4351*12500000000000^3327 ≤ 5389346734659^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313881527 2500000000 5389346734659 12500000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (852063613/5000000000 : ℝ)^4351 ≤ (4942424315411/50000000000000 : ℝ)^3327 := by
    have hnat : (852063613 : ℕ)^4351*50000000000000^3327 ≤ 4942424315411^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852063613 5000000000 4942424315411 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5613990877/10000000000 : ℝ)^4351 ≤ (23500188736887/50000000000000 : ℝ)^3327 := by
    have hnat : (5613990877 : ℕ)^4351*50000000000000^3327 ≤ 23500188736887^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5613990877 10000000000 23500188736887 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313881527/2500000000 : ℝ), (-852063613/5000000000 : ℝ), (5613990877/10000000000 : ℝ)] ![(5389346734659/12500000000000 : ℝ), (4942424315411/50000000000000 : ℝ), (23500188736887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313881527/2500000000 : ℝ)|^4351 ≤ (5389346734659/12500000000000 : ℝ)^3327
        have hw : |(1313881527/2500000000 : ℝ)|=(1313881527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-852063613/5000000000 : ℝ)|^4351 ≤ (4942424315411/50000000000000 : ℝ)^3327
        have hw : |(-852063613/5000000000 : ℝ)|=(852063613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5613990877/10000000000 : ℝ)|^4351 ≤ (23500188736887/50000000000000 : ℝ)^3327
        have hw : |(5613990877/10000000000 : ℝ)|=(5613990877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s1_6 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051105307/2000000000 : ℝ)*x 0 + (350874453/625000000 : ℝ)*x 1 + (-1704126087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051105307/2000000000 : ℝ)^4351 ≤ (21557389229209/50000000000000 : ℝ)^3327 := by
    have hnat : (1051105307 : ℕ)^4351*50000000000000^3327 ≤ 21557389229209^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051105307 2000000000 21557389229209 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350874453/625000000 : ℝ)^4351 ≤ (47000381535773/100000000000000 : ℝ)^3327 := by
    have hnat : (350874453 : ℕ)^4351*100000000000000^3327 ≤ 47000381535773^3327*625000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350874453 625000000 47000381535773 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704126087/10000000000 : ℝ)^4351 ≤ (9884839990539/100000000000000 : ℝ)^3327 := by
    have hnat : (1704126087 : ℕ)^4351*100000000000000^3327 ≤ 9884839990539^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704126087 10000000000 9884839990539 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051105307/2000000000 : ℝ), (350874453/625000000 : ℝ), (-1704126087/10000000000 : ℝ)] ![(21557389229209/50000000000000 : ℝ), (47000381535773/100000000000000 : ℝ), (9884839990539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051105307/2000000000 : ℝ)|^4351 ≤ (21557389229209/50000000000000 : ℝ)^3327
        have hw : |(1051105307/2000000000 : ℝ)|=(1051105307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(350874453/625000000 : ℝ)|^4351 ≤ (47000381535773/100000000000000 : ℝ)^3327
        have hw : |(350874453/625000000 : ℝ)|=(350874453/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1704126087/10000000000 : ℝ)|^4351 ≤ (9884839990539/100000000000000 : ℝ)^3327
        have hw : |(-1704126087/10000000000 : ℝ)|=(1704126087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s1_7 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071122259/2500000000 : ℝ)*x 0 + (1225191657/2500000000 : ℝ)*x 1 + (116915913/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071122259/2500000000 : ℝ)^4351 ≤ (3300677992041/10000000000000 : ℝ)^3327 := by
    have hnat : (1071122259 : ℕ)^4351*10000000000000^3327 ≤ 3300677992041^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071122259 2500000000 3300677992041 10000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1225191657/2500000000 : ℝ)^4351 ≤ (39348845884897/100000000000000 : ℝ)^3327 := by
    have hnat : (1225191657 : ℕ)^4351*100000000000000^3327 ≤ 39348845884897^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225191657 2500000000 39348845884897 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116915913/312500000 : ℝ)^4351 ≤ (431943346661/1562500000000 : ℝ)^3327 := by
    have hnat : (116915913 : ℕ)^4351*1562500000000^3327 ≤ 431943346661^3327*312500000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116915913 312500000 431943346661 1562500000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071122259/2500000000 : ℝ), (1225191657/2500000000 : ℝ), (116915913/312500000 : ℝ)] ![(3300677992041/10000000000000 : ℝ), (39348845884897/100000000000000 : ℝ), (431943346661/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071122259/2500000000 : ℝ)|^4351 ≤ (3300677992041/10000000000000 : ℝ)^3327
        have hw : |(1071122259/2500000000 : ℝ)|=(1071122259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1225191657/2500000000 : ℝ)|^4351 ≤ (39348845884897/100000000000000 : ℝ)^3327
        have hw : |(1225191657/2500000000 : ℝ)|=(1225191657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(116915913/312500000 : ℝ)|^4351 ≤ (431943346661/1562500000000 : ℝ)^3327
        have hw : |(116915913/312500000 : ℝ)|=(116915913/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1391_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26523/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (111/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (733/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9553/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26523/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (111/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26523/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (111/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26523/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (111/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26523/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (111/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26523/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (111/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26523/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (111/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (111/6250 : ℝ) ^ (2175/512 : ℝ) ≤ (915148667129/25000000000000000000 : ℝ) := by
    have hpowers : (111/6250 : ℝ)^2175 ≤ (915148667129/25000000000000000000 : ℝ)^512 := by
      have hnat : (111 : ℕ)^2175*25000000000000000000^512 ≤ 915148667129^512*6250^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111 6250 915148667129 25000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (111/6250 : ℝ)) (X := (915148667129/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26523/100000 : ℝ) ^ (2175/512 : ℝ) ≤ (356059009608800307/100000000000000000000 : ℝ) := by
    have hpowers : (26523/100000 : ℝ)^2175 ≤ (356059009608800307/100000000000000000000 : ℝ)^512 := by
      have hnat : (26523 : ℕ)^2175*100000000000000000000^512 ≤ 356059009608800307^512*100000^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26523 100000 356059009608800307 100000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26523/100000 : ℝ)) (X := (356059009608800307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000915148667129/12500000000000000000 : ℝ) ≤ (2500000043085619/2500000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (12500000915148667129/12500000000000000000 : ℝ)^512 ≤ (2500000043085619/2500000000000000 : ℝ)^2175 := by
      have hnat : (12500000915148667129 : ℕ)^512*2500000000000000^2175 ≤ 2500000043085619^2175*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000915148667129 12500000000000000000 2500000043085619 2500000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000043085619/2500000000000000 : ℝ)) (X := (12500000915148667129/12500000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100356062670203468823/100000000000000000000 : ℝ) ≤ (10008370411447843/10000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (100356062670203468823/100000000000000000000 : ℝ)^512 ≤ (10008370411447843/10000000000000000 : ℝ)^2175 := by
      have hnat : (100356062670203468823 : ℕ)^512*10000000000000000^2175 ≤ 10008370411447843^2175*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100356062670203468823 100000000000000000000 10008370411447843 10000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008370411447843/10000000000000000 : ℝ)) (X := (100356062670203468823/100000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50356059009608800307/50000000000000000000 : ℝ) ≤ (1001674065055321/1000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (50356059009608800307/50000000000000000000 : ℝ)^512 ≤ (1001674065055321/1000000000000000 : ℝ)^2175 := by
      have hnat : (50356059009608800307 : ℕ)^512*1000000000000000^2175 ≤ 1001674065055321^2175*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50356059009608800307 50000000000000000000 1001674065055321 1000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001674065055321/1000000000000000 : ℝ)) (X := (50356059009608800307/50000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(915148667129/25000000000000000000 : ℝ) ≤ ((20620022764638082499/20622500000000000000 : ℝ)+2*(2790079701789/824900000000000 : ℝ)*(111/6250 : ℝ))^(2175/512 : ℝ) := by
    rw [show (20620022764638082499/20622500000000000000 : ℝ)+2*(2790079701789/824900000000000 : ℝ)*(111/6250 : ℝ)=(2500000043085619/2500000000000000 : ℝ) by norm_num, show 1+2*(915148667129/25000000000000000000 : ℝ)=(12500000915148667129/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(356059009608800307/100000000000000000000 : ℝ)+(915148667129/25000000000000000000 : ℝ) ≤ ((20620022764638082499/20622500000000000000 : ℝ)+(2790079701789/824900000000000 : ℝ)*((26523/100000 : ℝ)+(111/6250 : ℝ)))^(2175/512 : ℝ) := by
    rw [show (20620022764638082499/20622500000000000000 : ℝ)+(2790079701789/824900000000000 : ℝ)*((26523/100000 : ℝ)+(111/6250 : ℝ))=(10008370411447843/10000000000000000 : ℝ) by norm_num, show 1+(356059009608800307/100000000000000000000 : ℝ)+(915148667129/25000000000000000000 : ℝ)=(100356062670203468823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(356059009608800307/100000000000000000000 : ℝ) ≤ ((20620022764638082499/20622500000000000000 : ℝ)+2*(2790079701789/824900000000000 : ℝ)*(26523/100000 : ℝ))^(2175/512 : ℝ) := by
    rw [show (20620022764638082499/20622500000000000000 : ℝ)+2*(2790079701789/824900000000000 : ℝ)*(26523/100000 : ℝ)=(1001674065055321/1000000000000000 : ℝ) by norm_num, show 1+2*(356059009608800307/100000000000000000000 : ℝ)=(50356059009608800307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20620022764638082499/20622500000000000000 : ℝ)*(X 1 0+X 2 0)+(2790079701789/824900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (111/6250 : ℝ)) (hi := (26523/100000 : ℝ)) (c := (20620022764638082499/20622500000000000000 : ℝ)) (alpha := (2790079701789/824900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20620022764638082499/20622500000000000000 : ℝ)*(X 0 1+X 2 1)+(2790079701789/824900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (111/6250 : ℝ)) (hi := (26523/100000 : ℝ)) (c := (20620022764638082499/20622500000000000000 : ℝ)) (alpha := (2790079701789/824900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20620022764638082499/20622500000000000000 : ℝ)*(X 0 2+X 1 2)+(2790079701789/824900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (111/6250 : ℝ)) (hi := (26523/100000 : ℝ)) (c := (20620022764638082499/20622500000000000000 : ℝ)) (alpha := (2790079701789/824900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-979149167/5000000000 : ℝ)*X 0 0+(2810419487/5000000000 : ℝ)*X 0 1+(632967957/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1080131821/2000000000 : ℝ)*X 1 0+(-2254373161/10000000000 : ℝ)*X 1 1+(5063745071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5400659973/10000000000 : ℝ)*X 2 0+(2531871919/5000000000 : ℝ)*X 2 1+(-281796701/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((856703957/2000000000 : ℝ)*X 0 0+(3726703021/10000000000 : ℝ)*X 0 1+(2457561831/5000000000 : ℝ)*X 0 2+(856703957/2000000000 : ℝ)*X 1 0+(3726703021/10000000000 : ℝ)*X 1 1+(2457561831/5000000000 : ℝ)*X 1 2+(856703957/2000000000 : ℝ)*X 2 0+(3726703021/10000000000 : ℝ)*X 2 1+(2457561831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-61210999/312500000 : ℝ)*X 0 0+(1014094801/2000000000 : ℝ)*X 0 1+(1122798171/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1313881527/2500000000 : ℝ)*X 1 0+(-852063613/5000000000 : ℝ)*X 1 1+(5613990877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051105307/2000000000 : ℝ)*X 2 0+(350874453/625000000 : ℝ)*X 2 1+(-1704126087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1071122259/2500000000 : ℝ)*X 0 0+(1225191657/2500000000 : ℝ)*X 0 1+(116915913/312500000 : ℝ)*X 0 2+(1071122259/2500000000 : ℝ)*X 1 0+(1225191657/2500000000 : ℝ)*X 1 1+(116915913/312500000 : ℝ)*X 1 2+(1071122259/2500000000 : ℝ)*X 2 0+(1225191657/2500000000 : ℝ)*X 2 1+(116915913/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3817366653028033047193068819/515562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1290456249/100000000000000 : ℝ)*(base19) + (1573003311/100000000000000 : ℝ)*(base23) + (98060131/50000000000000 : ℝ)*(upper3) + (3216239/100000000000000 : ℝ)*(upper4) + (31681437/50000000000000 : ℝ)*(upper5) + (659128344121227/50000000000000 : ℝ)*(major0) + (659128344121227/50000000000000 : ℝ)*(major1) + (659128344121227/50000000000000 : ℝ)*(major2) + (897519096385013/50000000000000 : ℝ)*(sp0) + (224381191355937/12500000000000 : ℝ)*(sp1) + (897524624150217/50000000000000 : ℝ)*(sp2) + (841457053394563/100000000000000 : ℝ)*(sp3) + (12628533719/100000000000000 : ℝ)*(sp4) + (2627488711/50000000000000 : ℝ)*(sp7) + (168292461674397/20000000000000 : ℝ)*(f.failure) + (359010164260749/20000000000000 : ℝ)*(f.sum) + (42464690236189/41245000000000000000000000000 : ℝ)*base66 + (5955317996607068727/1031125000000000000000000000000000 : ℝ)*base68 + (4786065899224306273/1031125000000000000000000000000000 : ℝ)*base69 + (8086147572829693727/1031125000000000000000000000000000 : ℝ)*base72 + (77155522466371/41245000000000000000000000000 : ℝ)*base73 + (960494172817568727/1031125000000000000000000000000000 : ℝ)*base76 + (2459790502741943727/1031125000000000000000000000000000 : ℝ)*base78 + (205697419708306273/1031125000000000000000000000000000 : ℝ)*base79 + (68187591500659/10311250000000000000000000000 : ℝ)*base81 + (183957/400000000000000000000 : ℝ)*base90 + (183957/400000000000000000000 : ℝ)*base92 + (183957/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (372555639616205170959822333/64445312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7521653/4000000000000 : ℝ)*(base1) + (1503976229/100000000000000 : ℝ)*(base19) + (1745051957/100000000000000 : ℝ)*(base23) + (71719181/50000000000000 : ℝ)*(upper3) + (224612009/100000000000000 : ℝ)*(upper5) + (168896467353847/12500000000000 : ℝ)*(major0) + (168896467353847/12500000000000 : ℝ)*(major1) + (168896467353847/12500000000000 : ℝ)*(major2) + (3768211117/50000000000000 : ℝ)*(sp1) + (10853041521/100000000000000 : ℝ)*(sp2) + (919935505916663/50000000000000 : ℝ)*(sp4) + (919930891696769/50000000000000 : ℝ)*(sp5) + (919929112849261/50000000000000 : ℝ)*(sp6) + (107809034141203/12500000000000 : ℝ)*(sp7) + (862472461170949/100000000000000 : ℝ)*(f.failure) + (1839870823792001/100000000000000 : ℝ)*(f.sum) + (11596279364657/5155625000000000000000000000 : ℝ)*base66 + (762153777925588847/257781250000000000000000000000000 : ℝ)*base68 + (27701488206463847/257781250000000000000000000000000 : ℝ)*base70 + (101837553563036153/257781250000000000000000000000000 : ℝ)*base71 + (97973202700593/20622500000000000000000000000 : ℝ)*base74 + (1550737518675098653/257781250000000000000000000000000 : ℝ)*base75 + (2143725534040504903/257781250000000000000000000000000 : ℝ)*base77 + (1856712339087661153/257781250000000000000000000000000 : ℝ)*base79 + (87246058578113/20622500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1790531/2000000000000000000000 : ℝ)*base89 + (1790531/2000000000000000000000 : ℝ)*base91 + (1790531/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1391_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26523/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (111/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (733/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9553/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1391_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1391_s2_0 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-997182911/5000000000 : ℝ)*x 0 + (5467071207/10000000000 : ℝ)*x 1 + (1038868837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (997182911/5000000000 : ℝ)^4351 ≤ (12142144490347/100000000000000 : ℝ)^3327 := by
    have hnat : (997182911 : ℕ)^4351*100000000000000^3327 ≤ 12142144490347^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997182911 5000000000 12142144490347 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467071207/10000000000 : ℝ)^4351 ≤ (9079660722689/20000000000000 : ℝ)^3327 := by
    have hnat : (5467071207 : ℕ)^4351*20000000000000^3327 ≤ 9079660722689^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467071207 10000000000 9079660722689 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038868837/2000000000 : ℝ)^4351 ≤ (42459551883521/100000000000000 : ℝ)^3327 := by
    have hnat : (1038868837 : ℕ)^4351*100000000000000^3327 ≤ 42459551883521^3327*2000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038868837 2000000000 42459551883521 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-997182911/5000000000 : ℝ), (5467071207/10000000000 : ℝ), (1038868837/2000000000 : ℝ)] ![(12142144490347/100000000000000 : ℝ), (9079660722689/20000000000000 : ℝ), (42459551883521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-997182911/5000000000 : ℝ)|^4351 ≤ (12142144490347/100000000000000 : ℝ)^3327
        have hw : |(-997182911/5000000000 : ℝ)|=(997182911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467071207/10000000000 : ℝ)|^4351 ≤ (9079660722689/20000000000000 : ℝ)^3327
        have hw : |(5467071207/10000000000 : ℝ)|=(5467071207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038868837/2000000000 : ℝ)|^4351 ≤ (42459551883521/100000000000000 : ℝ)^3327
        have hw : |(1038868837/2000000000 : ℝ)|=(1038868837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s2_1 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362605139/10000000000 : ℝ)*x 0 + (-2134929647/10000000000 : ℝ)*x 1 + (519434413/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362605139/10000000000 : ℝ)^4351 ≤ (11066793899353/25000000000000 : ℝ)^3327 := by
    have hnat : (5362605139 : ℕ)^4351*25000000000000^3327 ≤ 11066793899353^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362605139 10000000000 11066793899353 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134929647/10000000000 : ℝ)^4351 ≤ (3318318271921/25000000000000 : ℝ)^3327 := by
    have hnat : (2134929647 : ℕ)^4351*25000000000000^3327 ≤ 3318318271921^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134929647 10000000000 3318318271921 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519434413/1000000000 : ℝ)^4351 ≤ (42459551295567/100000000000000 : ℝ)^3327 := by
    have hnat : (519434413 : ℕ)^4351*100000000000000^3327 ≤ 42459551295567^3327*1000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519434413 1000000000 42459551295567 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362605139/10000000000 : ℝ), (-2134929647/10000000000 : ℝ), (519434413/1000000000 : ℝ)] ![(11066793899353/25000000000000 : ℝ), (3318318271921/25000000000000 : ℝ), (42459551295567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362605139/10000000000 : ℝ)|^4351 ≤ (11066793899353/25000000000000 : ℝ)^3327
        have hw : |(5362605139/10000000000 : ℝ)|=(5362605139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2134929647/10000000000 : ℝ)|^4351 ≤ (3318318271921/25000000000000 : ℝ)^3327
        have hw : |(-2134929647/10000000000 : ℝ)|=(2134929647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519434413/1000000000 : ℝ)|^4351 ≤ (42459551295567/100000000000000 : ℝ)^3327
        have hw : |(519434413/1000000000 : ℝ)|=(519434413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s2_2 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362604973/10000000000 : ℝ)*x 0 + (5194344309/10000000000 : ℝ)*x 1 + (-2134929633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362604973/10000000000 : ℝ)^4351 ≤ (44267173805361/100000000000000 : ℝ)^3327 := by
    have hnat : (5362604973 : ℕ)^4351*100000000000000^3327 ≤ 44267173805361^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362604973 10000000000 44267173805361 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5194344309/10000000000 : ℝ)^4351 ≤ (42459553209091/100000000000000 : ℝ)^3327 := by
    have hnat : (5194344309 : ℕ)^4351*100000000000000^3327 ≤ 42459553209091^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194344309 10000000000 42459553209091 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2134929633/10000000000 : ℝ)^4351 ≤ (6636636486927/50000000000000 : ℝ)^3327 := by
    have hnat : (2134929633 : ℕ)^4351*50000000000000^3327 ≤ 6636636486927^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134929633 10000000000 6636636486927 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362604973/10000000000 : ℝ), (5194344309/10000000000 : ℝ), (-2134929633/10000000000 : ℝ)] ![(44267173805361/100000000000000 : ℝ), (42459553209091/100000000000000 : ℝ), (6636636486927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362604973/10000000000 : ℝ)|^4351 ≤ (44267173805361/100000000000000 : ℝ)^3327
        have hw : |(5362604973/10000000000 : ℝ)|=(5362604973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5194344309/10000000000 : ℝ)|^4351 ≤ (42459553209091/100000000000000 : ℝ)^3327
        have hw : |(5194344309/10000000000 : ℝ)|=(5194344309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2134929633/10000000000 : ℝ)|^4351 ≤ (6636636486927/50000000000000 : ℝ)^3327
        have hw : |(-2134929633/10000000000 : ℝ)|=(2134929633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s2_3 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172355133/400000000 : ℝ)*x 0 + (2013470151/5000000000 : ℝ)*x 1 + (1152184019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172355133/400000000 : ℝ)^4351 ≤ (33252714350429/100000000000000 : ℝ)^3327 := by
    have hnat : (172355133 : ℕ)^4351*100000000000000^3327 ≤ 33252714350429^3327*400000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172355133 400000000 33252714350429 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013470151/5000000000 : ℝ)^4351 ≤ (7609087387939/25000000000000 : ℝ)^3327 := by
    have hnat : (2013470151 : ℕ)^4351*25000000000000^3327 ≤ 7609087387939^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013470151 5000000000 7609087387939 25000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152184019/2500000000 : ℝ)^4351 ≤ (36310936078657/100000000000000 : ℝ)^3327 := by
    have hnat : (1152184019 : ℕ)^4351*100000000000000^3327 ≤ 36310936078657^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152184019 2500000000 36310936078657 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172355133/400000000 : ℝ), (2013470151/5000000000 : ℝ), (1152184019/2500000000 : ℝ)] ![(33252714350429/100000000000000 : ℝ), (7609087387939/25000000000000 : ℝ), (36310936078657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172355133/400000000 : ℝ)|^4351 ≤ (33252714350429/100000000000000 : ℝ)^3327
        have hw : |(172355133/400000000 : ℝ)|=(172355133/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2013470151/5000000000 : ℝ)|^4351 ≤ (7609087387939/25000000000000 : ℝ)^3327
        have hw : |(2013470151/5000000000 : ℝ)|=(2013470151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152184019/2500000000 : ℝ)|^4351 ≤ (36310936078657/100000000000000 : ℝ)^3327
        have hw : |(1152184019/2500000000 : ℝ)|=(1152184019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s2_4 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994418801/10000000000 : ℝ)*x 0 + (519596677/1000000000 : ℝ)*x 1 + (2732717491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994418801/10000000000 : ℝ)^4351 ≤ (6071283157709/50000000000000 : ℝ)^3327 := by
    have hnat : (1994418801 : ℕ)^4351*50000000000000^3327 ≤ 6071283157709^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994418801 10000000000 6071283157709 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519596677/1000000000 : ℝ)^4351 ≤ (8495379656233/20000000000000 : ℝ)^3327 := by
    have hnat : (519596677 : ℕ)^4351*20000000000000^3327 ≤ 8495379656233^3327*1000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519596677 1000000000 8495379656233 20000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732717491/5000000000 : ℝ)^4351 ≤ (45380535382257/100000000000000 : ℝ)^3327 := by
    have hnat : (2732717491 : ℕ)^4351*100000000000000^3327 ≤ 45380535382257^3327*5000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732717491 5000000000 45380535382257 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994418801/10000000000 : ℝ), (519596677/1000000000 : ℝ), (2732717491/5000000000 : ℝ)] ![(6071283157709/50000000000000 : ℝ), (8495379656233/20000000000000 : ℝ), (45380535382257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994418801/10000000000 : ℝ)|^4351 ≤ (6071283157709/50000000000000 : ℝ)^3327
        have hw : |(-1994418801/10000000000 : ℝ)|=(1994418801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519596677/1000000000 : ℝ)|^4351 ≤ (8495379656233/20000000000000 : ℝ)^3327
        have hw : |(519596677/1000000000 : ℝ)|=(519596677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732717491/5000000000 : ℝ)|^4351 ≤ (45380535382257/100000000000000 : ℝ)^3327
        have hw : |(2732717491/5000000000 : ℝ)|=(2732717491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s2_5 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5291948671/10000000000 : ℝ)*x 0 + (-1863839429/10000000000 : ℝ)*x 1 + (5465434669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291948671/10000000000 : ℝ)^4351 ≤ (2175297795641/5000000000000 : ℝ)^3327 := by
    have hnat : (5291948671 : ℕ)^4351*5000000000000^3327 ≤ 2175297795641^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291948671 10000000000 2175297795641 5000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1863839429/10000000000 : ℝ)^4351 ≤ (11113512079361/100000000000000 : ℝ)^3327 := by
    have hnat : (1863839429 : ℕ)^4351*100000000000000^3327 ≤ 11113512079361^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863839429 10000000000 11113512079361 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465434669/10000000000 : ℝ)^4351 ≤ (22690265991729/50000000000000 : ℝ)^3327 := by
    have hnat : (5465434669 : ℕ)^4351*50000000000000^3327 ≤ 22690265991729^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465434669 10000000000 22690265991729 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291948671/10000000000 : ℝ), (-1863839429/10000000000 : ℝ), (5465434669/10000000000 : ℝ)] ![(2175297795641/5000000000000 : ℝ), (11113512079361/100000000000000 : ℝ), (22690265991729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291948671/10000000000 : ℝ)|^4351 ≤ (2175297795641/5000000000000 : ℝ)^3327
        have hw : |(5291948671/10000000000 : ℝ)|=(5291948671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1863839429/10000000000 : ℝ)|^4351 ≤ (11113512079361/100000000000000 : ℝ)^3327
        have hw : |(-1863839429/10000000000 : ℝ)|=(1863839429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465434669/10000000000 : ℝ)|^4351 ≤ (22690265991729/50000000000000 : ℝ)^3327
        have hw : |(5465434669/10000000000 : ℝ)|=(5465434669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s2_6 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322987527/2500000000 : ℝ)*x 0 + (5465434683/10000000000 : ℝ)*x 1 + (-1863837431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322987527/2500000000 : ℝ)^4351 ≤ (43505971362737/100000000000000 : ℝ)^3327 := by
    have hnat : (1322987527 : ℕ)^4351*100000000000000^3327 ≤ 43505971362737^3327*2500000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322987527 2500000000 43505971362737 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465434683/10000000000 : ℝ)^4351 ≤ (45380532135481/100000000000000 : ℝ)^3327 := by
    have hnat : (5465434683 : ℕ)^4351*100000000000000^3327 ≤ 45380532135481^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465434683 10000000000 45380532135481 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1863837431/10000000000 : ℝ)^4351 ≤ (11113496499107/100000000000000 : ℝ)^3327 := by
    have hnat : (1863837431 : ℕ)^4351*100000000000000^3327 ≤ 11113496499107^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863837431 10000000000 11113496499107 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322987527/2500000000 : ℝ), (5465434683/10000000000 : ℝ), (-1863837431/10000000000 : ℝ)] ![(43505971362737/100000000000000 : ℝ), (45380532135481/100000000000000 : ℝ), (11113496499107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322987527/2500000000 : ℝ)|^4351 ≤ (43505971362737/100000000000000 : ℝ)^3327
        have hw : |(1322987527/2500000000 : ℝ)|=(1322987527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465434683/10000000000 : ℝ)|^4351 ≤ (45380532135481/100000000000000 : ℝ)^3327
        have hw : |(5465434683/10000000000 : ℝ)|=(5465434683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1863837431/10000000000 : ℝ)|^4351 ≤ (11113496499107/100000000000000 : ℝ)^3327
        have hw : |(-1863837431/10000000000 : ℝ)|=(1863837431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1391_s2_7 (p : ℝ) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308992761/10000000000 : ℝ)*x 0 + (4605275211/10000000000 : ℝ)*x 1 + (4030430213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308992761/10000000000 : ℝ)^4351 ≤ (33253869301531/100000000000000 : ℝ)^3327 := by
    have hnat : (4308992761 : ℕ)^4351*100000000000000^3327 ≤ 33253869301531^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308992761 10000000000 33253869301531 100000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4605275211/10000000000 : ℝ)^4351 ≤ (2267205037107/6250000000000 : ℝ)^3327 := by
    have hnat : (4605275211 : ℕ)^4351*6250000000000^3327 ≤ 2267205037107^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4605275211 10000000000 2267205037107 6250000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4030430213/10000000000 : ℝ)^4351 ≤ (15235425046649/50000000000000 : ℝ)^3327 := by
    have hnat : (4030430213 : ℕ)^4351*50000000000000^3327 ≤ 15235425046649^3327*10000000000^4351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030430213 10000000000 15235425046649 50000000000000 4351 3327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4351/1024 : ℝ)) 4351 3327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308992761/10000000000 : ℝ), (4605275211/10000000000 : ℝ), (4030430213/10000000000 : ℝ)] ![(33253869301531/100000000000000 : ℝ), (2267205037107/6250000000000 : ℝ), (15235425046649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308992761/10000000000 : ℝ)|^4351 ≤ (33253869301531/100000000000000 : ℝ)^3327
        have hw : |(4308992761/10000000000 : ℝ)|=(4308992761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4605275211/10000000000 : ℝ)|^4351 ≤ (2267205037107/6250000000000 : ℝ)^3327
        have hw : |(4605275211/10000000000 : ℝ)|=(4605275211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4030430213/10000000000 : ℝ)|^4351 ≤ (15235425046649/50000000000000 : ℝ)^3327
        have hw : |(4030430213/10000000000 : ℝ)|=(4030430213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1391_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9553/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (733/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2031/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15923/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9553/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (733/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9553/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (733/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9553/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (733/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9553/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (733/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9553/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (733/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9553/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (733/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (733/10000 : ℝ) ^ (2175/512 : ℝ) ≤ (377440496383983/25000000000000000000 : ℝ) := by
    have hpowers : (733/10000 : ℝ)^2175 ≤ (377440496383983/25000000000000000000 : ℝ)^512 := by
      have hnat : (733 : ℕ)^2175*25000000000000000000^512 ≤ 377440496383983^512*10000^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        733 10000 377440496383983 25000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (733/10000 : ℝ)) (X := (377440496383983/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9553/50000 : ℝ) ^ (2175/512 : ℝ) ≤ (88384376439444443/100000000000000000000 : ℝ) := by
    have hpowers : (9553/50000 : ℝ)^2175 ≤ (88384376439444443/100000000000000000000 : ℝ)^512 := by
      have hnat : (9553 : ℕ)^2175*100000000000000000000^512 ≤ 88384376439444443^512*50000^2175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9553 50000 88384376439444443 100000000000000000000 2175 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9553/50000 : ℝ)) (X := (88384376439444443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500377440496383983/12500000000000000000 : ℝ) ≤ (2000014215893583/2000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (12500377440496383983/12500000000000000000 : ℝ)^512 ≤ (2000014215893583/2000000000000000 : ℝ)^2175 := by
      have hnat : (12500377440496383983 : ℕ)^512*2000000000000000^2175 ≤ 2000014215893583^2175*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500377440496383983 12500000000000000000 2000014215893583 2000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000014215893583/2000000000000000 : ℝ)) (X := (12500377440496383983/12500000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (800719153107399843/800000000000000000 : ℝ) ≤ (10002115401830343/10000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (800719153107399843/800000000000000000 : ℝ)^512 ≤ (10002115401830343/10000000000000000 : ℝ)^2175 := by
      have hnat : (800719153107399843 : ℕ)^512*10000000000000000^2175 ≤ 10002115401830343^2175*800000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800719153107399843 800000000000000000 10002115401830343 10000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002115401830343/10000000000000000 : ℝ)) (X := (800719153107399843/800000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50088384376439444443/50000000000000000000 : ℝ) ≤ (10004159724192771/10000000000000000 : ℝ) ^ (2175/512 : ℝ) := by
    have hpowers : (50088384376439444443/50000000000000000000 : ℝ)^512 ≤ (10004159724192771/10000000000000000 : ℝ)^2175 := by
      have hnat : (50088384376439444443 : ℕ)^512*10000000000000000^2175 ≤ 10004159724192771^2175*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50088384376439444443 50000000000000000000 10004159724192771 10000000000000000 512 2175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004159724192771/10000000000000000 : ℝ)) (X := (50088384376439444443/50000000000000000000 : ℝ)) (by norm_num) 2175 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(377440496383983/25000000000000000000 : ℝ) ≤ ((1471635840824762157/1472000000000000000 : ℝ)+2*(511080590607/294400000000000 : ℝ)*(733/10000 : ℝ))^(2175/512 : ℝ) := by
    rw [show (1471635840824762157/1472000000000000000 : ℝ)+2*(511080590607/294400000000000 : ℝ)*(733/10000 : ℝ)=(2000014215893583/2000000000000000 : ℝ) by norm_num, show 1+2*(377440496383983/25000000000000000000 : ℝ)=(12500377440496383983/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(88384376439444443/100000000000000000000 : ℝ)+(377440496383983/25000000000000000000 : ℝ) ≤ ((1471635840824762157/1472000000000000000 : ℝ)+(511080590607/294400000000000 : ℝ)*((9553/50000 : ℝ)+(733/10000 : ℝ)))^(2175/512 : ℝ) := by
    rw [show (1471635840824762157/1472000000000000000 : ℝ)+(511080590607/294400000000000 : ℝ)*((9553/50000 : ℝ)+(733/10000 : ℝ))=(10002115401830343/10000000000000000 : ℝ) by norm_num, show 1+(88384376439444443/100000000000000000000 : ℝ)+(377440496383983/25000000000000000000 : ℝ)=(800719153107399843/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(88384376439444443/100000000000000000000 : ℝ) ≤ ((1471635840824762157/1472000000000000000 : ℝ)+2*(511080590607/294400000000000 : ℝ)*(9553/50000 : ℝ))^(2175/512 : ℝ) := by
    rw [show (1471635840824762157/1472000000000000000 : ℝ)+2*(511080590607/294400000000000 : ℝ)*(9553/50000 : ℝ)=(10004159724192771/10000000000000000 : ℝ) by norm_num, show 1+2*(88384376439444443/100000000000000000000 : ℝ)=(50088384376439444443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1471635840824762157/1472000000000000000 : ℝ)*(X 1 0+X 2 0)+(511080590607/294400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (733/10000 : ℝ)) (hi := (9553/50000 : ℝ)) (c := (1471635840824762157/1472000000000000000 : ℝ)) (alpha := (511080590607/294400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1471635840824762157/1472000000000000000 : ℝ)*(X 0 1+X 2 1)+(511080590607/294400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (733/10000 : ℝ)) (hi := (9553/50000 : ℝ)) (c := (1471635840824762157/1472000000000000000 : ℝ)) (alpha := (511080590607/294400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1471635840824762157/1472000000000000000 : ℝ)*(X 0 2+X 1 2)+(511080590607/294400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2175/512 : ℝ)) (lo := (733/10000 : ℝ)) (hi := (9553/50000 : ℝ)) (c := (1471635840824762157/1472000000000000000 : ℝ)) (alpha := (511080590607/294400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-997182911/5000000000 : ℝ)*X 0 0+(5467071207/10000000000 : ℝ)*X 0 1+(1038868837/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5362605139/10000000000 : ℝ)*X 1 0+(-2134929647/10000000000 : ℝ)*X 1 1+(519434413/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362604973/10000000000 : ℝ)*X 2 0+(5194344309/10000000000 : ℝ)*X 2 1+(-2134929633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172355133/400000000 : ℝ)*X 0 0+(2013470151/5000000000 : ℝ)*X 0 1+(1152184019/2500000000 : ℝ)*X 0 2+(172355133/400000000 : ℝ)*X 1 0+(2013470151/5000000000 : ℝ)*X 1 1+(1152184019/2500000000 : ℝ)*X 1 2+(172355133/400000000 : ℝ)*X 2 0+(2013470151/5000000000 : ℝ)*X 2 1+(1152184019/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1994418801/10000000000 : ℝ)*X 0 0+(519596677/1000000000 : ℝ)*X 0 1+(2732717491/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291948671/10000000000 : ℝ)*X 1 0+(-1863839429/10000000000 : ℝ)*X 1 1+(5465434669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322987527/2500000000 : ℝ)*X 2 0+(5465434683/10000000000 : ℝ)*X 2 1+(-1863837431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308992761/10000000000 : ℝ)*X 0 0+(4605275211/10000000000 : ℝ)*X 0 1+(4030430213/10000000000 : ℝ)*X 0 2+(4308992761/10000000000 : ℝ)*X 1 0+(4605275211/10000000000 : ℝ)*X 1 1+(4030430213/10000000000 : ℝ)*X 1 2+(4308992761/10000000000 : ℝ)*X 2 0+(4605275211/10000000000 : ℝ)*X 2 1+(4030430213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1391_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124231787910429019250053059/18400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (608940079/50000000000000 : ℝ)*(base19) + (969420833/100000000000000 : ℝ)*(base23) + (9046469/12500000000000 : ℝ)*(lower2) + (107144399/50000000000000 : ℝ)*(upper3) + (5947101/6250000000000 : ℝ)*(upper5) + (1346382216575071/50000000000000 : ℝ)*(major0) + (1346382216575071/50000000000000 : ℝ)*(major1) + (1346382216575071/50000000000000 : ℝ)*(major2) + (1833342610325303/50000000000000 : ℝ)*(sp0) + (183334847183089/5000000000000 : ℝ)*(sp1) + (1833348596060553/50000000000000 : ℝ)*(sp2) + (429705669977781/25000000000000 : ℝ)*(sp3) + (3235222833/25000000000000 : ℝ)*(sp4) + (62398317/800000000000 : ℝ)*(sp7) + (1718830479700749/100000000000000 : ℝ)*(f.failure) + (3666698161541939/100000000000000 : ℝ)*(f.sum) + (920735421137/7360000000000000000000000000 : ℝ)*base65 + (627994473292873147/73600000000000000000000000000000 : ℝ)*base67 + (921518097632073147/73600000000000000000000000000000 : ℝ)*base69 + (807384541708873147/73600000000000000000000000000000 : ℝ)*base71 + (28881691601583/7360000000000000000000000000 : ℝ)*base74 + (459151911654473147/73600000000000000000000000000000 : ℝ)*base75 + (472653749664073147/73600000000000000000000000000000 : ℝ)*base77 + (215987521766326853/73600000000000000000000000000000 : ℝ)*base80 + (9435191238737/7360000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (7643269/2000000000000000000000 : ℝ)*base90 + (7643269/2000000000000000000000 : ℝ)*base92 + (7643269/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42446112076204210319405217/9200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (700832667/100000000000000 : ℝ)*(base19) + (1328987893/50000000000000 : ℝ)*(base23) + (40983821/100000000000000 : ℝ)*(lower2) + (20164247/10000000000000 : ℝ)*(upper3) + (66060077/25000000000000 : ℝ)*(lower4) + (4101189/100000000000000 : ℝ)*(upper5) + (340663483084473/12500000000000 : ℝ)*(major0) + (340663483084473/12500000000000 : ℝ)*(major1) + (340663483084473/12500000000000 : ℝ)*(major2) + (1975671051/5000000000000 : ℝ)*(sp2) + (463876519110443/12500000000000 : ℝ)*(sp4) + (1855505726025439/50000000000000 : ℝ)*(sp5) + (1855484990743369/50000000000000 : ℝ)*(sp6) + (1739603422677751/100000000000000 : ℝ)*(sp7) + (1739603422677751/100000000000000 : ℝ)*(f.failure) + (463876519110443/12500000000000 : ℝ)*(f.sum) + (15615964226169/1840000000000000000000000000 : ℝ)*base66 + (271917674215843261/18400000000000000000000000000000 : ℝ)*base67 + (257800019743843261/18400000000000000000000000000000 : ℝ)*base69 + (41643876548643261/18400000000000000000000000000000 : ℝ)*base71 + (8647357634951/1840000000000000000000000000 : ℝ)*base73 + (40709678657756739/18400000000000000000000000000000 : ℝ)*base76 + (127597796729756739/18400000000000000000000000000000 : ℝ)*base78 + (164758349302243261/18400000000000000000000000000000 : ℝ)*base79 + (11803595331111/1840000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15915231/2000000000000000000000 : ℝ)*base90 + (15915231/2000000000000000000000 : ℝ)*base92 + (15915231/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1391_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9553/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (733/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2031/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15923/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1391_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1391_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2031/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15923/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1391_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1391_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1391_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2175/512 : ℝ) ≤ p) (hpb : p ≤ (4351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31332519/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2031/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15923/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1391_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
