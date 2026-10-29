-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1642_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:17.446361+00:00
-- url     : https://prove2.me/submissions/6a307b4b-1829-48b5-b42e-ebf1e72b31b0

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
theorem support_rectangle_w1642_s0_0 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1506798891/10000000000 : ℝ)*x 0 + (4636237/8000000 : ℝ)*x 1 + (12290181/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1506798891/10000000000 : ℝ)^4887 ≤ (4561892558839/50000000000000 : ℝ)^3863 := by
    have hnat : (1506798891 : ℕ)^4887*50000000000000^3863 ≤ 4561892558839^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506798891 10000000000 4561892558839 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4636237/8000000 : ℝ)^4887 ≤ (50150120449507/100000000000000 : ℝ)^3863 := by
    have hnat : (4636237 : ℕ)^4887*100000000000000^3863 ≤ 50150120449507^3863*8000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4636237 8000000 50150120449507 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12290181/25000000 : ℝ)^4887 ≤ (1272690450569/3125000000000 : ℝ)^3863 := by
    have hnat : (12290181 : ℕ)^4887*3125000000000^3863 ≤ 1272690450569^3863*25000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12290181 25000000 1272690450569 3125000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1506798891/10000000000 : ℝ), (4636237/8000000 : ℝ), (12290181/25000000 : ℝ)] ![(4561892558839/50000000000000 : ℝ), (50150120449507/100000000000000 : ℝ), (1272690450569/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1506798891/10000000000 : ℝ)|^4887 ≤ (4561892558839/50000000000000 : ℝ)^3863
        have hw : |(-1506798891/10000000000 : ℝ)|=(1506798891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4636237/8000000 : ℝ)|^4887 ≤ (50150120449507/100000000000000 : ℝ)^3863
        have hw : |(4636237/8000000 : ℝ)|=(4636237/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12290181/25000000 : ℝ)|^4887 ≤ (1272690450569/3125000000000 : ℝ)^3863
        have hw : |(12290181/25000000 : ℝ)|=(12290181/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s0_1 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2720360451/5000000000 : ℝ)*x 0 + (-248778899/1250000000 : ℝ)*x 1 + (1229018437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2720360451/5000000000 : ℝ)^4887 ≤ (5787547238053/12500000000000 : ℝ)^3863 := by
    have hnat : (2720360451 : ℕ)^4887*12500000000000^3863 ≤ 5787547238053^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720360451 5000000000 5787547238053 12500000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248778899/1250000000 : ℝ)^4887 ≤ (2594702705499/20000000000000 : ℝ)^3863 := by
    have hnat : (248778899 : ℕ)^4887*20000000000000^3863 ≤ 2594702705499^3863*1250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248778899 1250000000 2594702705499 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229018437/2500000000 : ℝ)^4887 ≤ (40726108545601/100000000000000 : ℝ)^3863 := by
    have hnat : (1229018437 : ℕ)^4887*100000000000000^3863 ≤ 40726108545601^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229018437 2500000000 40726108545601 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2720360451/5000000000 : ℝ), (-248778899/1250000000 : ℝ), (1229018437/2500000000 : ℝ)] ![(5787547238053/12500000000000 : ℝ), (2594702705499/20000000000000 : ℝ), (40726108545601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2720360451/5000000000 : ℝ)|^4887 ≤ (5787547238053/12500000000000 : ℝ)^3863
        have hw : |(2720360451/5000000000 : ℝ)|=(2720360451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248778899/1250000000 : ℝ)|^4887 ≤ (2594702705499/20000000000000 : ℝ)^3863
        have hw : |(-248778899/1250000000 : ℝ)|=(248778899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1229018437/2500000000 : ℝ)|^4887 ≤ (40726108545601/100000000000000 : ℝ)^3863
        have hw : |(1229018437/2500000000 : ℝ)|=(1229018437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s0_2 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5440722991/10000000000 : ℝ)*x 0 + (2458036111/5000000000 : ℝ)*x 1 + (-497557601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5440722991/10000000000 : ℝ)^4887 ≤ (46300400394151/100000000000000 : ℝ)^3863 := by
    have hnat : (5440722991 : ℕ)^4887*100000000000000^3863 ≤ 46300400394151^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440722991 10000000000 46300400394151 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2458036111/5000000000 : ℝ)^4887 ≤ (40726092552721/100000000000000 : ℝ)^3863 := by
    have hnat : (2458036111 : ℕ)^4887*100000000000000^3863 ≤ 40726092552721^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458036111 5000000000 40726092552721 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497557601/2500000000 : ℝ)^4887 ≤ (6486753514611/50000000000000 : ℝ)^3863 := by
    have hnat : (497557601 : ℕ)^4887*50000000000000^3863 ≤ 6486753514611^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497557601 2500000000 6486753514611 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5440722991/10000000000 : ℝ), (2458036111/5000000000 : ℝ), (-497557601/2500000000 : ℝ)] ![(46300400394151/100000000000000 : ℝ), (40726092552721/100000000000000 : ℝ), (6486753514611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5440722991/10000000000 : ℝ)|^4887 ≤ (46300400394151/100000000000000 : ℝ)^3863
        have hw : |(5440722991/10000000000 : ℝ)|=(5440722991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2458036111/5000000000 : ℝ)|^4887 ≤ (40726092552721/100000000000000 : ℝ)^3863
        have hw : |(2458036111/5000000000 : ℝ)|=(2458036111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497557601/2500000000 : ℝ)|^4887 ≤ (6486753514611/50000000000000 : ℝ)^3863
        have hw : |(-497557601/2500000000 : ℝ)|=(497557601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s0_3 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1023593859/2500000000 : ℝ)*x 0 + (770170547/2500000000 : ℝ)*x 1 + (5332540631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023593859/2500000000 : ℝ)^4887 ≤ (16156853186113/50000000000000 : ℝ)^3863 := by
    have hnat : (1023593859 : ℕ)^4887*50000000000000^3863 ≤ 16156853186113^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023593859 2500000000 16156853186113 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (770170547/2500000000 : ℝ)^4887 ≤ (11273738483567/50000000000000 : ℝ)^3863 := by
    have hnat : (770170547 : ℕ)^4887*50000000000000^3863 ≤ 11273738483567^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770170547 2500000000 11273738483567 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5332540631/10000000000 : ℝ)^4887 ≤ (45138816641201/100000000000000 : ℝ)^3863 := by
    have hnat : (5332540631 : ℕ)^4887*100000000000000^3863 ≤ 45138816641201^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5332540631 10000000000 45138816641201 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1023593859/2500000000 : ℝ), (770170547/2500000000 : ℝ), (5332540631/10000000000 : ℝ)] ![(16156853186113/50000000000000 : ℝ), (11273738483567/50000000000000 : ℝ), (45138816641201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1023593859/2500000000 : ℝ)|^4887 ≤ (16156853186113/50000000000000 : ℝ)^3863
        have hw : |(1023593859/2500000000 : ℝ)|=(1023593859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(770170547/2500000000 : ℝ)|^4887 ≤ (11273738483567/50000000000000 : ℝ)^3863
        have hw : |(770170547/2500000000 : ℝ)|=(770170547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5332540631/10000000000 : ℝ)|^4887 ≤ (45138816641201/100000000000000 : ℝ)^3863
        have hw : |(5332540631/10000000000 : ℝ)|=(5332540631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s0_4 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-754593649/5000000000 : ℝ)*x 0 + (197519043/400000000 : ℝ)*x 1 + (2886315841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (754593649/5000000000 : ℝ)^4887 ≤ (914208452049/10000000000000 : ℝ)^3863 := by
    have hnat : (754593649 : ℕ)^4887*10000000000000^3863 ≤ 914208452049^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754593649 5000000000 914208452049 10000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197519043/400000000 : ℝ)^4887 ≤ (40955786075621/100000000000000 : ℝ)^3863 := by
    have hnat : (197519043 : ℕ)^4887*100000000000000^3863 ≤ 40955786075621^3863*400000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197519043 400000000 40955786075621 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2886315841/5000000000 : ℝ)^4887 ≤ (49902129388109/100000000000000 : ℝ)^3863 := by
    have hnat : (2886315841 : ℕ)^4887*100000000000000^3863 ≤ 49902129388109^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2886315841 5000000000 49902129388109 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-754593649/5000000000 : ℝ), (197519043/400000000 : ℝ), (2886315841/5000000000 : ℝ)] ![(914208452049/10000000000000 : ℝ), (40955786075621/100000000000000 : ℝ), (49902129388109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-754593649/5000000000 : ℝ)|^4887 ≤ (914208452049/10000000000000 : ℝ)^3863
        have hw : |(-754593649/5000000000 : ℝ)|=(754593649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(197519043/400000000 : ℝ)|^4887 ≤ (40955786075621/100000000000000 : ℝ)^3863
        have hw : |(197519043/400000000 : ℝ)|=(197519043/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2886315841/5000000000 : ℝ)|^4887 ≤ (49902129388109/100000000000000 : ℝ)^3863
        have hw : |(2886315841/5000000000 : ℝ)|=(2886315841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s0_5 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5200742089/10000000000 : ℝ)*x 0 + (-226734381/2000000000 : ℝ)*x 1 + (5772631613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5200742089/10000000000 : ℝ)^4887 ≤ (1366627734243/3125000000000 : ℝ)^3863 := by
    have hnat : (5200742089 : ℕ)^4887*3125000000000^3863 ≤ 1366627734243^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200742089 10000000000 1366627734243 3125000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226734381/2000000000 : ℝ)^4887 ≤ (1591445964139/25000000000000 : ℝ)^3863 := by
    have hnat : (226734381 : ℕ)^4887*25000000000000^3863 ≤ 1591445964139^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226734381 2000000000 1591445964139 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5772631613/10000000000 : ℝ)^4887 ≤ (24951064316759/50000000000000 : ℝ)^3863 := by
    have hnat : (5772631613 : ℕ)^4887*50000000000000^3863 ≤ 24951064316759^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5772631613 10000000000 24951064316759 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5200742089/10000000000 : ℝ), (-226734381/2000000000 : ℝ), (5772631613/10000000000 : ℝ)] ![(1366627734243/3125000000000 : ℝ), (1591445964139/25000000000000 : ℝ), (24951064316759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5200742089/10000000000 : ℝ)|^4887 ≤ (1366627734243/3125000000000 : ℝ)^3863
        have hw : |(5200742089/10000000000 : ℝ)|=(5200742089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226734381/2000000000 : ℝ)|^4887 ≤ (1591445964139/25000000000000 : ℝ)^3863
        have hw : |(-226734381/2000000000 : ℝ)|=(226734381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5772631613/10000000000 : ℝ)|^4887 ≤ (24951064316759/50000000000000 : ℝ)^3863
        have hw : |(5772631613/10000000000 : ℝ)|=(5772631613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s0_6 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5200742199/10000000000 : ℝ)*x 0 + (721578937/1250000000 : ℝ)*x 1 + (-1133671919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5200742199/10000000000 : ℝ)^4887 ≤ (2733255541621/6250000000000 : ℝ)^3863 := by
    have hnat : (5200742199 : ℕ)^4887*6250000000000^3863 ≤ 2733255541621^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200742199 10000000000 2733255541621 6250000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721578937/1250000000 : ℝ)^4887 ≤ (49902127353993/100000000000000 : ℝ)^3863 := by
    have hnat : (721578937 : ℕ)^4887*100000000000000^3863 ≤ 49902127353993^3863*1250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721578937 1250000000 49902127353993 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133671919/10000000000 : ℝ)^4887 ≤ (6365783956007/100000000000000 : ℝ)^3863 := by
    have hnat : (1133671919 : ℕ)^4887*100000000000000^3863 ≤ 6365783956007^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133671919 10000000000 6365783956007 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5200742199/10000000000 : ℝ), (721578937/1250000000 : ℝ), (-1133671919/10000000000 : ℝ)] ![(2733255541621/6250000000000 : ℝ), (49902127353993/100000000000000 : ℝ), (6365783956007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5200742199/10000000000 : ℝ)|^4887 ≤ (2733255541621/6250000000000 : ℝ)^3863
        have hw : |(5200742199/10000000000 : ℝ)|=(5200742199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(721578937/1250000000 : ℝ)|^4887 ≤ (49902127353993/100000000000000 : ℝ)^3863
        have hw : |(721578937/1250000000 : ℝ)|=(721578937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1133671919/10000000000 : ℝ)|^4887 ≤ (6365783956007/100000000000000 : ℝ)^3863
        have hw : |(-1133671919/10000000000 : ℝ)|=(1133671919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s0_7 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1025123797/2500000000 : ℝ)*x 0 + (2638221203/5000000000 : ℝ)*x 1 + (3138727317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025123797/2500000000 : ℝ)^4887 ≤ (32374819788291/100000000000000 : ℝ)^3863 := by
    have hnat : (1025123797 : ℕ)^4887*100000000000000^3863 ≤ 32374819788291^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025123797 2500000000 32374819788291 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2638221203/5000000000 : ℝ)^4887 ≤ (8907784336501/20000000000000 : ℝ)^3863 := by
    have hnat : (2638221203 : ℕ)^4887*20000000000000^3863 ≤ 8907784336501^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638221203 5000000000 8907784336501 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3138727317/10000000000 : ℝ)^4887 ≤ (5771564627031/25000000000000 : ℝ)^3863 := by
    have hnat : (3138727317 : ℕ)^4887*25000000000000^3863 ≤ 5771564627031^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3138727317 10000000000 5771564627031 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1025123797/2500000000 : ℝ), (2638221203/5000000000 : ℝ), (3138727317/10000000000 : ℝ)] ![(32374819788291/100000000000000 : ℝ), (8907784336501/20000000000000 : ℝ), (5771564627031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1025123797/2500000000 : ℝ)|^4887 ≤ (32374819788291/100000000000000 : ℝ)^3863
        have hw : |(1025123797/2500000000 : ℝ)|=(1025123797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2638221203/5000000000 : ℝ)|^4887 ≤ (8907784336501/20000000000000 : ℝ)^3863
        have hw : |(2638221203/5000000000 : ℝ)|=(2638221203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3138727317/10000000000 : ℝ)|^4887 ≤ (5771564627031/25000000000000 : ℝ)^3863
        have hw : |(3138727317/10000000000 : ℝ)|=(3138727317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1642_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4687/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2941/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4883/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4883 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4883*1^1024 ≤ 0^1024*1^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4883/1024 : ℝ) ≤ (632952778489586987/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4883 ≤ (632952778489586987/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4883*50000000000000000000^1024 ≤ 632952778489586987^1024*5^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 632952778489586987 50000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (632952778489586987/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4883 := by
      have hnat : (1 : ℕ)^1024*1^4883 ≤ 1^4883*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50632952778489586987/50000000000000000000 : ℝ) ≤ (5013207573049107/5000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (50632952778489586987/50000000000000000000 : ℝ)^1024 ≤ (5013207573049107/5000000000000000 : ℝ)^4883 := by
      have hnat : (50632952778489586987 : ℕ)^1024*5000000000000000^4883 ≤ 5013207573049107^4883*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50632952778489586987 50000000000000000000 5013207573049107 5000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013207573049107/5000000000000000 : ℝ)) (X := (50632952778489586987/50000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25632952778489586987/25000000000000000000 : ℝ) ≤ (2513207573049107/2500000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (25632952778489586987/25000000000000000000 : ℝ)^1024 ≤ (2513207573049107/2500000000000000 : ℝ)^4883 := by
      have hnat : (25632952778489586987 : ℕ)^1024*2500000000000000^4883 ≤ 2513207573049107^4883*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25632952778489586987 25000000000000000000 2513207573049107 2500000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513207573049107/2500000000000000 : ℝ)) (X := (25632952778489586987/25000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(13207573049107/2000000000000000 : ℝ)*(0 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(13207573049107/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(632952778489586987/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(13207573049107/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4883/1024 : ℝ) := by
    rw [show (1 : ℝ)+(13207573049107/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5013207573049107/5000000000000000 : ℝ) by norm_num, show 1+(632952778489586987/50000000000000000000 : ℝ)+(0 : ℝ)=(50632952778489586987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(632952778489586987/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(13207573049107/2000000000000000 : ℝ)*(2/5 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(13207573049107/2000000000000000 : ℝ)*(2/5 : ℝ)=(2513207573049107/2500000000000000 : ℝ) by norm_num, show 1+2*(632952778489586987/50000000000000000000 : ℝ)=(25632952778489586987/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(13207573049107/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13207573049107/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(13207573049107/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13207573049107/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(13207573049107/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13207573049107/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1506798891/10000000000 : ℝ)*X 0 0+(4636237/8000000 : ℝ)*X 0 1+(12290181/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2720360451/5000000000 : ℝ)*X 1 0+(-248778899/1250000000 : ℝ)*X 1 1+(1229018437/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5440722991/10000000000 : ℝ)*X 2 0+(2458036111/5000000000 : ℝ)*X 2 1+(-497557601/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1023593859/2500000000 : ℝ)*X 0 0+(770170547/2500000000 : ℝ)*X 0 1+(5332540631/10000000000 : ℝ)*X 0 2+(1023593859/2500000000 : ℝ)*X 1 0+(770170547/2500000000 : ℝ)*X 1 1+(5332540631/10000000000 : ℝ)*X 1 2+(1023593859/2500000000 : ℝ)*X 2 0+(770170547/2500000000 : ℝ)*X 2 1+(5332540631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-754593649/5000000000 : ℝ)*X 0 0+(197519043/400000000 : ℝ)*X 0 1+(2886315841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5200742089/10000000000 : ℝ)*X 1 0+(-226734381/2000000000 : ℝ)*X 1 1+(5772631613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5200742199/10000000000 : ℝ)*X 2 0+(721578937/1250000000 : ℝ)*X 2 1+(-1133671919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1025123797/2500000000 : ℝ)*X 0 0+(2638221203/5000000000 : ℝ)*X 0 1+(3138727317/10000000000 : ℝ)*X 0 2+(1025123797/2500000000 : ℝ)*X 1 0+(2638221203/5000000000 : ℝ)*X 1 1+(3138727317/10000000000 : ℝ)*X 1 2+(1025123797/2500000000 : ℝ)*X 2 0+(2638221203/5000000000 : ℝ)*X 2 1+(3138727317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (204700167969835955882631/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (616408283/50000000000000 : ℝ)*(base19) + (1537640447/100000000000000 : ℝ)*(base23) + (24475547/50000000000000 : ℝ)*(upper3) + (71752229/100000000000000 : ℝ)*(upper4) + (158141849/50000000000000 : ℝ)*(upper5) + (395365637169889/50000000000000 : ℝ)*(major0) + (395365637169889/50000000000000 : ℝ)*(major1) + (395365637169889/50000000000000 : ℝ)*(major2) + (142171453976407/12500000000000 : ℝ)*(sp0) + (4442886463163/390625000000 : ℝ)*(sp1) + (568689314872923/50000000000000 : ℝ)*(sp2) + (88816017318611/20000000000000 : ℝ)*(sp3) + (4267787519/50000000000000 : ℝ)*(sp4) + (404353329/20000000000000 : ℝ)*(sp7) + (4440821083597/1000000000000 : ℝ)*(f.failure) + (568690083693147/50000000000000 : ℝ)*(f.sum) + (189513057739123/50000000000000000000000000000 : ℝ)*base65 + (304601907260877/100000000000000000000000000000 : ℝ)*base68 + (93819150139123/100000000000000000000000000000 : ℝ)*base69 + (451948309139123/100000000000000000000000000000 : ℝ)*base71 + (111925922960877/50000000000000000000000000000 : ℝ)*base74 + (248002072660877/100000000000000000000000000000 : ℝ)*base76 + (320659236139123/100000000000000000000000000000 : ℝ)*base77 + (712929696539123/100000000000000000000000000000 : ℝ)*base79 + (47266029439123/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (175503/100000000000000000000 : ℝ)*base90 + (175503/100000000000000000000 : ℝ)*base92 + (175503/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104578076422342136149557/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (771695991/100000000000000 : ℝ)*(base19) + (804928199/100000000000000 : ℝ)*(base23) + (57536971/100000000000000 : ℝ)*(base32) + (123518571/100000000000000 : ℝ)*(upper3) + (78229001/100000000000000 : ℝ)*(upper5) + (416471960296883/50000000000000 : ℝ)*(major0) + (416471960296883/50000000000000 : ℝ)*(major1) + (416471960296883/50000000000000 : ℝ)*(major2) + (2270002769/100000000000000 : ℝ)*(sp1) + (2441003529/100000000000000 : ℝ)*(sp2) + (299524643723037/25000000000000 : ℝ)*(sp4) + (299523883298347/25000000000000 : ℝ)*(sp5) + (59904766448021/5000000000000 : ℝ)*(sp6) + (467789069320973/100000000000000 : ℝ)*(sp7) + (58473640857243/12500000000000 : ℝ)*(f.failure) + (299524643723037/25000000000000 : ℝ)*(f.sum) + (35827167033481/50000000000000000000000000000 : ℝ)*base65 + (463275244233481/100000000000000000000000000000 : ℝ)*base67 + (485054020333481/100000000000000000000000000000 : ℝ)*base69 + (806622948633481/100000000000000000000000000000 : ℝ)*base71 + (120793054466519/50000000000000000000000000000 : ℝ)*base74 + (514879008333481/100000000000000000000000000000 : ℝ)*base75 + (607331583733481/100000000000000000000000000000 : ℝ)*base77 + (301185178433481/100000000000000000000000000000 : ℝ)*base79 + (92179629216519/50000000000000000000000000000 : ℝ)*base82 + (2735657/1250000000000000000000 : ℝ)*base90 + (2735657/1250000000000000000000 : ℝ)*base92 + (2735657/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1642_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4687/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2941/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1642_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1642_s1_0 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1616021151/10000000000 : ℝ)*x 0 + (2751205903/5000000000 : ℝ)*x 1 + (1027607787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1616021151/10000000000 : ℝ)^4887 ≤ (996834384559/10000000000000 : ℝ)^3863 := by
    have hnat : (1616021151 : ℕ)^4887*10000000000000^3863 ≤ 996834384559^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616021151 10000000000 996834384559 10000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751205903/5000000000 : ℝ)^4887 ≤ (2935345267843/6250000000000 : ℝ)^3863 := by
    have hnat : (2751205903 : ℕ)^4887*6250000000000^3863 ≤ 2935345267843^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751205903 5000000000 2935345267843 6250000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027607787/2000000000 : ℝ)^4887 ≤ (2691633241197/6250000000000 : ℝ)^3863 := by
    have hnat : (1027607787 : ℕ)^4887*6250000000000^3863 ≤ 2691633241197^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027607787 2000000000 2691633241197 6250000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1616021151/10000000000 : ℝ), (2751205903/5000000000 : ℝ), (1027607787/2000000000 : ℝ)] ![(996834384559/10000000000000 : ℝ), (2935345267843/6250000000000 : ℝ), (2691633241197/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1616021151/10000000000 : ℝ)|^4887 ≤ (996834384559/10000000000000 : ℝ)^3863
        have hw : |(-1616021151/10000000000 : ℝ)|=(1616021151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751205903/5000000000 : ℝ)|^4887 ≤ (2935345267843/6250000000000 : ℝ)^3863
        have hw : |(2751205903/5000000000 : ℝ)|=(2751205903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027607787/2000000000 : ℝ)|^4887 ≤ (2691633241197/6250000000000 : ℝ)^3863
        have hw : |(1027607787/2000000000 : ℝ)|=(1027607787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s1_1 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362820531/10000000000 : ℝ)*x 0 + (-180565529/1000000000 : ℝ)*x 1 + (5138038741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362820531/10000000000 : ℝ)^4887 ≤ (22731658185133/50000000000000 : ℝ)^3863 := by
    have hnat : (5362820531 : ℕ)^4887*50000000000000^3863 ≤ 22731658185133^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362820531 10000000000 22731658185133 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180565529/1000000000 : ℝ)^4887 ≤ (5735276905121/50000000000000 : ℝ)^3863 := by
    have hnat : (180565529 : ℕ)^4887*50000000000000^3863 ≤ 5735276905121^3863*1000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180565529 1000000000 5735276905121 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138038741/10000000000 : ℝ)^4887 ≤ (43066129802041/100000000000000 : ℝ)^3863 := by
    have hnat : (5138038741 : ℕ)^4887*100000000000000^3863 ≤ 43066129802041^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138038741 10000000000 43066129802041 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362820531/10000000000 : ℝ), (-180565529/1000000000 : ℝ), (5138038741/10000000000 : ℝ)] ![(22731658185133/50000000000000 : ℝ), (5735276905121/50000000000000 : ℝ), (43066129802041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362820531/10000000000 : ℝ)|^4887 ≤ (22731658185133/50000000000000 : ℝ)^3863
        have hw : |(5362820531/10000000000 : ℝ)|=(5362820531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-180565529/1000000000 : ℝ)|^4887 ≤ (5735276905121/50000000000000 : ℝ)^3863
        have hw : |(-180565529/1000000000 : ℝ)|=(180565529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138038741/10000000000 : ℝ)|^4887 ≤ (43066129802041/100000000000000 : ℝ)^3863
        have hw : |(5138038741/10000000000 : ℝ)|=(5138038741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s1_2 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362821641/10000000000 : ℝ)*x 0 + (256901873/500000000 : ℝ)*x 1 + (-1805655499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362821641/10000000000 : ℝ)^4887 ≤ (11365832068673/25000000000000 : ℝ)^3863 := by
    have hnat : (5362821641 : ℕ)^4887*25000000000000^3863 ≤ 11365832068673^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362821641 10000000000 11365832068673 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256901873/500000000 : ℝ)^4887 ≤ (43066116218743/100000000000000 : ℝ)^3863 := by
    have hnat : (256901873 : ℕ)^4887*100000000000000^3863 ≤ 43066116218743^3863*500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256901873 500000000 43066116218743 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1805655499/10000000000 : ℝ)^4887 ≤ (716909718117/6250000000000 : ℝ)^3863 := by
    have hnat : (1805655499 : ℕ)^4887*6250000000000^3863 ≤ 716909718117^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805655499 10000000000 716909718117 6250000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362821641/10000000000 : ℝ), (256901873/500000000 : ℝ), (-1805655499/10000000000 : ℝ)] ![(11365832068673/25000000000000 : ℝ), (43066116218743/100000000000000 : ℝ), (716909718117/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362821641/10000000000 : ℝ)|^4887 ≤ (11365832068673/25000000000000 : ℝ)^3863
        have hw : |(5362821641/10000000000 : ℝ)|=(5362821641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256901873/500000000 : ℝ)|^4887 ≤ (43066116218743/100000000000000 : ℝ)^3863
        have hw : |(256901873/500000000 : ℝ)|=(256901873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1805655499/10000000000 : ℝ)|^4887 ≤ (716909718117/6250000000000 : ℝ)^3863
        have hw : |(-1805655499/10000000000 : ℝ)|=(1805655499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s1_3 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044714641/2500000000 : ℝ)*x 0 + (3731313933/10000000000 : ℝ)*x 1 + (2332272717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044714641/2500000000 : ℝ)^4887 ≤ (33159504824453/100000000000000 : ℝ)^3863 := by
    have hnat : (1044714641 : ℕ)^4887*100000000000000^3863 ≤ 33159504824453^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044714641 2500000000 33159504824453 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3731313933/10000000000 : ℝ)^4887 ≤ (28732364072731/100000000000000 : ℝ)^3863 := by
    have hnat : (3731313933 : ℕ)^4887*100000000000000^3863 ≤ 28732364072731^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731313933 10000000000 28732364072731 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2332272717/5000000000 : ℝ)^4887 ≤ (19054065545317/50000000000000 : ℝ)^3863 := by
    have hnat : (2332272717 : ℕ)^4887*50000000000000^3863 ≤ 19054065545317^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2332272717 5000000000 19054065545317 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044714641/2500000000 : ℝ), (3731313933/10000000000 : ℝ), (2332272717/5000000000 : ℝ)] ![(33159504824453/100000000000000 : ℝ), (28732364072731/100000000000000 : ℝ), (19054065545317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044714641/2500000000 : ℝ)|^4887 ≤ (33159504824453/100000000000000 : ℝ)^3863
        have hw : |(1044714641/2500000000 : ℝ)|=(1044714641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3731313933/10000000000 : ℝ)|^4887 ≤ (28732364072731/100000000000000 : ℝ)^3863
        have hw : |(3731313933/10000000000 : ℝ)|=(3731313933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2332272717/5000000000 : ℝ)|^4887 ≤ (19054065545317/50000000000000 : ℝ)^3863
        have hw : |(2332272717/5000000000 : ℝ)|=(2332272717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s1_4 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1616188969/10000000000 : ℝ)*x 0 + (2570891817/5000000000 : ℝ)*x 1 + (2749306259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1616188969/10000000000 : ℝ)^4887 ≤ (4984826721969/50000000000000 : ℝ)^3863 := by
    have hnat : (1616188969 : ℕ)^4887*50000000000000^3863 ≤ 4984826721969^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616188969 10000000000 4984826721969 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570891817/5000000000 : ℝ)^4887 ≤ (43105843237617/100000000000000 : ℝ)^3863 := by
    have hnat : (2570891817 : ℕ)^4887*100000000000000^3863 ≤ 43105843237617^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570891817 5000000000 43105843237617 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2749306259/5000000000 : ℝ)^4887 ≤ (46924503291643/100000000000000 : ℝ)^3863 := by
    have hnat : (2749306259 : ℕ)^4887*100000000000000^3863 ≤ 46924503291643^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749306259 5000000000 46924503291643 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1616188969/10000000000 : ℝ), (2570891817/5000000000 : ℝ), (2749306259/5000000000 : ℝ)] ![(4984826721969/50000000000000 : ℝ), (43105843237617/100000000000000 : ℝ), (46924503291643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1616188969/10000000000 : ℝ)|^4887 ≤ (4984826721969/50000000000000 : ℝ)^3863
        have hw : |(-1616188969/10000000000 : ℝ)|=(1616188969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570891817/5000000000 : ℝ)|^4887 ≤ (43105843237617/100000000000000 : ℝ)^3863
        have hw : |(2570891817/5000000000 : ℝ)|=(2570891817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2749306259/5000000000 : ℝ)|^4887 ≤ (46924503291643/100000000000000 : ℝ)^3863
        have hw : |(2749306259/5000000000 : ℝ)|=(2749306259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s1_5 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316369917/2500000000 : ℝ)*x 0 + (-180635133/1250000000 : ℝ)*x 1 + (2749306259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316369917/2500000000 : ℝ)^4887 ≤ (44421886754797/100000000000000 : ℝ)^3863 := by
    have hnat : (1316369917 : ℕ)^4887*100000000000000^3863 ≤ 44421886754797^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316369917 2500000000 44421886754797 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180635133/1250000000 : ℝ)^4887 ≤ (1730721989199/20000000000000 : ℝ)^3863 := by
    have hnat : (180635133 : ℕ)^4887*20000000000000^3863 ≤ 1730721989199^3863*1250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180635133 1250000000 1730721989199 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2749306259/5000000000 : ℝ)^4887 ≤ (46924503291643/100000000000000 : ℝ)^3863 := by
    have hnat : (2749306259 : ℕ)^4887*100000000000000^3863 ≤ 46924503291643^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749306259 5000000000 46924503291643 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316369917/2500000000 : ℝ), (-180635133/1250000000 : ℝ), (2749306259/5000000000 : ℝ)] ![(44421886754797/100000000000000 : ℝ), (1730721989199/20000000000000 : ℝ), (46924503291643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316369917/2500000000 : ℝ)|^4887 ≤ (44421886754797/100000000000000 : ℝ)^3863
        have hw : |(1316369917/2500000000 : ℝ)|=(1316369917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-180635133/1250000000 : ℝ)|^4887 ≤ (1730721989199/20000000000000 : ℝ)^3863
        have hw : |(-180635133/1250000000 : ℝ)|=(180635133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2749306259/5000000000 : ℝ)|^4887 ≤ (46924503291643/100000000000000 : ℝ)^3863
        have hw : |(2749306259/5000000000 : ℝ)|=(2749306259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s1_6 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32909247/62500000 : ℝ)*x 0 + (5498612739/10000000000 : ℝ)*x 1 + (-1445080957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32909247/62500000 : ℝ)^4887 ≤ (44421885175229/100000000000000 : ℝ)^3863 := by
    have hnat : (32909247 : ℕ)^4887*100000000000000^3863 ≤ 44421885175229^3863*62500000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32909247 62500000 44421885175229 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498612739/10000000000 : ℝ)^4887 ≤ (23462252838783/50000000000000 : ℝ)^3863 := by
    have hnat : (5498612739 : ℕ)^4887*50000000000000^3863 ≤ 23462252838783^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498612739 10000000000 23462252838783 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1445080957/10000000000 : ℝ)^4887 ≤ (2163402283849/25000000000000 : ℝ)^3863 := by
    have hnat : (1445080957 : ℕ)^4887*25000000000000^3863 ≤ 2163402283849^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445080957 10000000000 2163402283849 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32909247/62500000 : ℝ), (5498612739/10000000000 : ℝ), (-1445080957/10000000000 : ℝ)] ![(44421885175229/100000000000000 : ℝ), (23462252838783/50000000000000 : ℝ), (2163402283849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32909247/62500000 : ℝ)|^4887 ≤ (44421885175229/100000000000000 : ℝ)^3863
        have hw : |(32909247/62500000 : ℝ)|=(32909247/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498612739/10000000000 : ℝ)|^4887 ≤ (23462252838783/50000000000000 : ℝ)^3863
        have hw : |(5498612739/10000000000 : ℝ)|=(5498612739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1445080957/10000000000 : ℝ)|^4887 ≤ (2163402283849/25000000000000 : ℝ)^3863
        have hw : |(-1445080957/10000000000 : ℝ)|=(1445080957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s1_7 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208964249/500000000 : ℝ)*x 0 + (290934577/625000000 : ℝ)*x 1 + (58453833/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208964249/500000000 : ℝ)^4887 ≤ (8290946362799/25000000000000 : ℝ)^3863 := by
    have hnat : (208964249 : ℕ)^4887*25000000000000^3863 ≤ 8290946362799^3863*500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208964249 500000000 8290946362799 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290934577/625000000 : ℝ)^4887 ≤ (7601803837079/20000000000000 : ℝ)^3863 := by
    have hnat : (290934577 : ℕ)^4887*20000000000000^3863 ≤ 7601803837079^3863*625000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290934577 625000000 7601803837079 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58453833/156250000 : ℝ)^4887 ≤ (28827195347459/100000000000000 : ℝ)^3863 := by
    have hnat : (58453833 : ℕ)^4887*100000000000000^3863 ≤ 28827195347459^3863*156250000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58453833 156250000 28827195347459 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208964249/500000000 : ℝ), (290934577/625000000 : ℝ), (58453833/156250000 : ℝ)] ![(8290946362799/25000000000000 : ℝ), (7601803837079/20000000000000 : ℝ), (28827195347459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208964249/500000000 : ℝ)|^4887 ≤ (8290946362799/25000000000000 : ℝ)^3863
        have hw : |(208964249/500000000 : ℝ)|=(208964249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(290934577/625000000 : ℝ)|^4887 ≤ (7601803837079/20000000000000 : ℝ)^3863
        have hw : |(290934577/625000000 : ℝ)|=(290934577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(58453833/156250000 : ℝ)|^4887 ≤ (28827195347459/100000000000000 : ℝ)^3863
        have hw : |(58453833/156250000 : ℝ)|=(58453833/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1642_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4687/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4823/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17383/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2941/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4687/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2941/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4687/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2941/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4687/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2941/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4687/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2941/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4687/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2941/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4687/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4687/100000 : ℝ) ^ (4883/1024 : ℝ) ≤ (11482326955503/25000000000000000000 : ℝ) := by
    have hpowers : (4687/100000 : ℝ)^4883 ≤ (11482326955503/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4687 : ℕ)^4883*25000000000000000000^1024 ≤ 11482326955503^1024*100000^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4687 100000 11482326955503 25000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4687/100000 : ℝ)) (X := (11482326955503/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2941/12500 : ℝ) ^ (4883/1024 : ℝ) ≤ (4031148083876233/4000000000000000000 : ℝ) := by
    have hpowers : (2941/12500 : ℝ)^4883 ≤ (4031148083876233/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2941 : ℕ)^4883*4000000000000000000^1024 ≤ 4031148083876233^1024*12500^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2941 12500 4031148083876233 4000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2941/12500 : ℝ)) (X := (4031148083876233/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500011482326955503/12500000000000000000 : ℝ) ≤ (80000015410721/80000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (12500011482326955503/12500000000000000000 : ℝ)^1024 ≤ (80000015410721/80000000000000 : ℝ)^4883 := by
      have hnat : (12500011482326955503 : ℕ)^1024*80000000000000^4883 ≤ 80000015410721^4883*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500011482326955503 12500000000000000000 80000015410721 80000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80000015410721/80000000000000 : ℝ)) (X := (12500011482326955503/12500000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100100824631404727837/100000000000000000000 : ℝ) ≤ (312566047584863/312500000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (100100824631404727837/100000000000000000000 : ℝ)^1024 ≤ (312566047584863/312500000000000 : ℝ)^4883 := by
      have hnat : (100100824631404727837 : ℕ)^1024*312500000000000^4883 ≤ 312566047584863^4883*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100100824631404727837 100000000000000000000 312566047584863 312500000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312566047584863/312500000000000 : ℝ)) (X := (100100824631404727837/100000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2004031148083876233/2000000000000000000 : ℝ) ≤ (10004225119091107/10000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (2004031148083876233/2000000000000000000 : ℝ)^1024 ≤ (10004225119091107/10000000000000000 : ℝ)^4883 := by
      have hnat : (2004031148083876233 : ℕ)^1024*10000000000000000^4883 ≤ 10004225119091107^4883*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2004031148083876233 2000000000000000000 10004225119091107 10000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004225119091107/10000000000000000 : ℝ)) (X := (2004031148083876233/2000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11482326955503/25000000000000000000 : ℝ) ≤ ((188390242189750442491/188410000000000000000 : ℝ)+2*(2111596375491/1884100000000000 : ℝ)*(4687/100000 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (188390242189750442491/188410000000000000000 : ℝ)+2*(2111596375491/1884100000000000 : ℝ)*(4687/100000 : ℝ)=(80000015410721/80000000000000 : ℝ) by norm_num, show 1+2*(11482326955503/25000000000000000000 : ℝ)=(12500011482326955503/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4031148083876233/4000000000000000000 : ℝ)+(11482326955503/25000000000000000000 : ℝ) ≤ ((188390242189750442491/188410000000000000000 : ℝ)+(2111596375491/1884100000000000 : ℝ)*((2941/12500 : ℝ)+(4687/100000 : ℝ)))^(4883/1024 : ℝ) := by
    rw [show (188390242189750442491/188410000000000000000 : ℝ)+(2111596375491/1884100000000000 : ℝ)*((2941/12500 : ℝ)+(4687/100000 : ℝ))=(312566047584863/312500000000000 : ℝ) by norm_num, show 1+(4031148083876233/4000000000000000000 : ℝ)+(11482326955503/25000000000000000000 : ℝ)=(100100824631404727837/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4031148083876233/4000000000000000000 : ℝ) ≤ ((188390242189750442491/188410000000000000000 : ℝ)+2*(2111596375491/1884100000000000 : ℝ)*(2941/12500 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (188390242189750442491/188410000000000000000 : ℝ)+2*(2111596375491/1884100000000000 : ℝ)*(2941/12500 : ℝ)=(10004225119091107/10000000000000000 : ℝ) by norm_num, show 1+2*(4031148083876233/4000000000000000000 : ℝ)=(2004031148083876233/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (188390242189750442491/188410000000000000000 : ℝ)*(X 1 0+X 2 0)+(2111596375491/1884100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (4687/100000 : ℝ)) (hi := (2941/12500 : ℝ)) (c := (188390242189750442491/188410000000000000000 : ℝ)) (alpha := (2111596375491/1884100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (188390242189750442491/188410000000000000000 : ℝ)*(X 0 1+X 2 1)+(2111596375491/1884100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (4687/100000 : ℝ)) (hi := (2941/12500 : ℝ)) (c := (188390242189750442491/188410000000000000000 : ℝ)) (alpha := (2111596375491/1884100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (188390242189750442491/188410000000000000000 : ℝ)*(X 0 2+X 1 2)+(2111596375491/1884100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (4687/100000 : ℝ)) (hi := (2941/12500 : ℝ)) (c := (188390242189750442491/188410000000000000000 : ℝ)) (alpha := (2111596375491/1884100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1616021151/10000000000 : ℝ)*X 0 0+(2751205903/5000000000 : ℝ)*X 0 1+(1027607787/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5362820531/10000000000 : ℝ)*X 1 0+(-180565529/1000000000 : ℝ)*X 1 1+(5138038741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362821641/10000000000 : ℝ)*X 2 0+(256901873/500000000 : ℝ)*X 2 1+(-1805655499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1044714641/2500000000 : ℝ)*X 0 0+(3731313933/10000000000 : ℝ)*X 0 1+(2332272717/5000000000 : ℝ)*X 0 2+(1044714641/2500000000 : ℝ)*X 1 0+(3731313933/10000000000 : ℝ)*X 1 1+(2332272717/5000000000 : ℝ)*X 1 2+(1044714641/2500000000 : ℝ)*X 2 0+(3731313933/10000000000 : ℝ)*X 2 1+(2332272717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1616188969/10000000000 : ℝ)*X 0 0+(2570891817/5000000000 : ℝ)*X 0 1+(2749306259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1316369917/2500000000 : ℝ)*X 1 0+(-180635133/1250000000 : ℝ)*X 1 1+(2749306259/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((32909247/62500000 : ℝ)*X 2 0+(5498612739/10000000000 : ℝ)*X 2 1+(-1445080957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((208964249/500000000 : ℝ)*X 0 0+(290934577/625000000 : ℝ)*X 0 1+(58453833/156250000 : ℝ)*X 0 2+(208964249/500000000 : ℝ)*X 1 0+(290934577/625000000 : ℝ)*X 1 1+(58453833/156250000 : ℝ)*X 1 2+(208964249/500000000 : ℝ)*X 2 0+(290934577/625000000 : ℝ)*X 2 1+(58453833/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19738293497374255012298889621/4710250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86818377/50000000000000 : ℝ)*(base1) + (146501949/50000000000000 : ℝ)*(base19) + (121424253/12500000000000 : ℝ)*(base23) + (44414871/50000000000000 : ℝ)*(lower2) + (37001387/25000000000000 : ℝ)*(lower4) + (5313011/10000000000000 : ℝ)*(upper5) + (953996540695477/50000000000000 : ℝ)*(major0) + (953996540695477/50000000000000 : ℝ)*(major1) + (953996540695477/50000000000000 : ℝ)*(major2) + (2744439366837611/100000000000000 : ℝ)*(sp0) + (2744438900196959/100000000000000 : ℝ)*(sp1) + (1372219110903417/50000000000000 : ℝ)*(sp2) + (214309199755467/20000000000000 : ℝ)*(sp3) + (131496737/20000000000000 : ℝ)*(sp7) + (1071546829897773/100000000000000 : ℝ)*(f.failure) + (2744439193200857/100000000000000 : ℝ)*(f.sum) + (737154588353281/94205000000000000000000000000 : ℝ)*base66 + (11143138078862513207/9420500000000000000000000000000000 : ℝ)*base67 + (30946652204544486793/9420500000000000000000000000000000 : ℝ)*base70 + (79515981274661486793/9420500000000000000000000000000000 : ℝ)*base72 + (41618102001411/94205000000000000000000000000 : ℝ)*base74 + (18680500967008513207/9420500000000000000000000000000000 : ℝ)*base75 + (40212989857643986793/9420500000000000000000000000000000 : ℝ)*base78 + (48439321663304486793/9420500000000000000000000000000000 : ℝ)*base80 + (24083042709447/47102500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (79054127/10000000000000000000000 : ℝ)*base90 + (79054127/10000000000000000000000 : ℝ)*base92 + (79054127/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29172567352616931173229/4710250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1207313201/100000000000000 : ℝ)*(base19) + (1177938503/100000000000000 : ℝ)*(base23) + (3396559/20000000000000 : ℝ)*(upper2) + (18840497/12500000000000 : ℝ)*(upper3) + (155423717/100000000000000 : ℝ)*(upper5) + (48708320346861/2500000000000 : ℝ)*(major0) + (48708320346861/2500000000000 : ℝ)*(major1) + (48708320346861/2500000000000 : ℝ)*(major2) + (10891931193/100000000000000 : ℝ)*(sp1) + (5909541331/50000000000000 : ℝ)*(sp2) + (350307927358121/12500000000000 : ℝ)*(sp4) + (1401225659810287/50000000000000 : ℝ)*(sp5) + (1401225210921901/50000000000000 : ℝ)*(sp6) + (547101001218249/50000000000000 : ℝ)*(sp7) + (547101001218249/50000000000000 : ℝ)*(f.failure) + (350307927358121/12500000000000 : ℝ)*(f.sum) + (3032291214409/471025000000000000000000000 : ℝ)*base66 + (1460909724961229249/471025000000000000000000000000000 : ℝ)*base68 + (559753822257970751/471025000000000000000000000000000 : ℝ)*base69 + (837751990400904249/471025000000000000000000000000000 : ℝ)*base72 + (26902797058511/9420500000000000000000000000 : ℝ)*base74 + (206191189868945751/471025000000000000000000000000000 : ℝ)*base75 + (1158148125619579249/471025000000000000000000000000000 : ℝ)*base78 + (1167608318670620751/471025000000000000000000000000000 : ℝ)*base79 + (5985043215669/4710250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (52683549/5000000000000000000000 : ℝ)*base89 + (52683549/5000000000000000000000 : ℝ)*base91 + (52683549/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1642_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4687/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4823/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17383/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1642_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1642_s2_0 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-162611083/1000000000 : ℝ)*x 0 + (1363497353/2500000000 : ℝ)*x 1 + (1294953697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162611083/1000000000 : ℝ)^4887 ≤ (2511786116571/25000000000000 : ℝ)^3863 := by
    have hnat : (162611083 : ℕ)^4887*25000000000000^3863 ≤ 2511786116571^3863*1000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162611083 1000000000 2511786116571 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363497353/2500000000 : ℝ)^4887 ≤ (9288653996027/20000000000000 : ℝ)^3863 := by
    have hnat : (1363497353 : ℕ)^4887*20000000000000^3863 ≤ 9288653996027^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363497353 2500000000 9288653996027 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294953697/2500000000 : ℝ)^4887 ≤ (43509585540601/100000000000000 : ℝ)^3863 := by
    have hnat : (1294953697 : ℕ)^4887*100000000000000^3863 ≤ 43509585540601^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294953697 2500000000 43509585540601 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-162611083/1000000000 : ℝ), (1363497353/2500000000 : ℝ), (1294953697/2500000000 : ℝ)] ![(2511786116571/25000000000000 : ℝ), (9288653996027/20000000000000 : ℝ), (43509585540601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-162611083/1000000000 : ℝ)|^4887 ≤ (2511786116571/25000000000000 : ℝ)^3863
        have hw : |(-162611083/1000000000 : ℝ)|=(162611083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363497353/2500000000 : ℝ)|^4887 ≤ (9288653996027/20000000000000 : ℝ)^3863
        have hw : |(1363497353/2500000000 : ℝ)|=(1363497353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294953697/2500000000 : ℝ)|^4887 ≤ (43509585540601/100000000000000 : ℝ)^3863
        have hw : |(1294953697/2500000000 : ℝ)|=(1294953697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s2_1 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350039969/10000000000 : ℝ)*x 0 + (-88370827/500000000 : ℝ)*x 1 + (5179815499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350039969/10000000000 : ℝ)^4887 ≤ (45326291893871/100000000000000 : ℝ)^3863 := by
    have hnat : (5350039969 : ℕ)^4887*100000000000000^3863 ≤ 45326291893871^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350039969 10000000000 45326291893871 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88370827/500000000 : ℝ)^4887 ≤ (11164115005183/100000000000000 : ℝ)^3863 := by
    have hnat : (88370827 : ℕ)^4887*100000000000000^3863 ≤ 11164115005183^3863*500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88370827 500000000 11164115005183 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179815499/10000000000 : ℝ)^4887 ≤ (4350959309601/10000000000000 : ℝ)^3863 := by
    have hnat : (5179815499 : ℕ)^4887*10000000000000^3863 ≤ 4350959309601^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179815499 10000000000 4350959309601 10000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350039969/10000000000 : ℝ), (-88370827/500000000 : ℝ), (5179815499/10000000000 : ℝ)] ![(45326291893871/100000000000000 : ℝ), (11164115005183/100000000000000 : ℝ), (4350959309601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350039969/10000000000 : ℝ)|^4887 ≤ (45326291893871/100000000000000 : ℝ)^3863
        have hw : |(5350039969/10000000000 : ℝ)|=(5350039969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88370827/500000000 : ℝ)|^4887 ≤ (11164115005183/100000000000000 : ℝ)^3863
        have hw : |(-88370827/500000000 : ℝ)|=(88370827/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179815499/10000000000 : ℝ)|^4887 ≤ (4350959309601/10000000000000 : ℝ)^3863
        have hw : |(5179815499/10000000000 : ℝ)|=(5179815499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s2_2 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350042203/10000000000 : ℝ)*x 0 + (207192563/400000000 : ℝ)*x 1 + (-441853859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350042203/10000000000 : ℝ)^4887 ≤ (45326315837721/100000000000000 : ℝ)^3863 := by
    have hnat : (5350042203 : ℕ)^4887*100000000000000^3863 ≤ 45326315837721^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350042203 10000000000 45326315837721 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207192563/400000000 : ℝ)^4887 ≤ (2175478898197/5000000000000 : ℝ)^3863 := by
    have hnat : (207192563 : ℕ)^4887*5000000000000^3863 ≤ 2175478898197^3863*400000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207192563 400000000 2175478898197 5000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441853859/2500000000 : ℝ)^4887 ≤ (11164106183081/100000000000000 : ℝ)^3863 := by
    have hnat : (441853859 : ℕ)^4887*100000000000000^3863 ≤ 11164106183081^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441853859 2500000000 11164106183081 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350042203/10000000000 : ℝ), (207192563/400000000 : ℝ), (-441853859/2500000000 : ℝ)] ![(45326315837721/100000000000000 : ℝ), (2175478898197/5000000000000 : ℝ), (11164106183081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350042203/10000000000 : ℝ)|^4887 ≤ (45326315837721/100000000000000 : ℝ)^3863
        have hw : |(5350042203/10000000000 : ℝ)|=(5350042203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207192563/400000000 : ℝ)|^4887 ≤ (2175478898197/5000000000000 : ℝ)^3863
        have hw : |(207192563/400000000 : ℝ)|=(207192563/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441853859/2500000000 : ℝ)|^4887 ≤ (11164106183081/100000000000000 : ℝ)^3863
        have hw : |(-441853859/2500000000 : ℝ)|=(441853859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s2_3 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186365211/10000000000 : ℝ)*x 0 + (3846060191/10000000000 : ℝ)*x 1 + (4548275343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186365211/10000000000 : ℝ)^4887 ≤ (16617439044893/50000000000000 : ℝ)^3863 := by
    have hnat : (4186365211 : ℕ)^4887*50000000000000^3863 ≤ 16617439044893^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186365211 10000000000 16617439044893 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3846060191/10000000000 : ℝ)^4887 ≤ (14927345216487/50000000000000 : ℝ)^3863 := by
    have hnat : (3846060191 : ℕ)^4887*50000000000000^3863 ≤ 14927345216487^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3846060191 10000000000 14927345216487 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4548275343/10000000000 : ℝ)^4887 ≤ (18455215731637/50000000000000 : ℝ)^3863 := by
    have hnat : (4548275343 : ℕ)^4887*50000000000000^3863 ≤ 18455215731637^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548275343 10000000000 18455215731637 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186365211/10000000000 : ℝ), (3846060191/10000000000 : ℝ), (4548275343/10000000000 : ℝ)] ![(16617439044893/50000000000000 : ℝ), (14927345216487/50000000000000 : ℝ), (18455215731637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186365211/10000000000 : ℝ)|^4887 ≤ (16617439044893/50000000000000 : ℝ)^3863
        have hw : |(4186365211/10000000000 : ℝ)|=(4186365211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3846060191/10000000000 : ℝ)|^4887 ≤ (14927345216487/50000000000000 : ℝ)^3863
        have hw : |(3846060191/10000000000 : ℝ)|=(3846060191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4548275343/10000000000 : ℝ)|^4887 ≤ (18455215731637/50000000000000 : ℝ)^3863
        have hw : |(4548275343/10000000000 : ℝ)|=(4548275343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s2_4 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-203272621/1250000000 : ℝ)*x 0 + (2590970639/5000000000 : ℝ)*x 1 + (5451840681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203272621/1250000000 : ℝ)^4887 ≤ (5023846350161/50000000000000 : ℝ)^3863 := by
    have hnat : (203272621 : ℕ)^4887*50000000000000^3863 ≤ 5023846350161^3863*1250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203272621 1250000000 5023846350161 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590970639/5000000000 : ℝ)^4887 ≤ (21766091908563/50000000000000 : ℝ)^3863 := by
    have hnat : (2590970639 : ℕ)^4887*50000000000000^3863 ≤ 21766091908563^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590970639 5000000000 21766091908563 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451840681/10000000000 : ℝ)^4887 ≤ (46420123471121/100000000000000 : ℝ)^3863 := by
    have hnat : (5451840681 : ℕ)^4887*100000000000000^3863 ≤ 46420123471121^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451840681 10000000000 46420123471121 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-203272621/1250000000 : ℝ), (2590970639/5000000000 : ℝ), (5451840681/10000000000 : ℝ)] ![(5023846350161/50000000000000 : ℝ), (21766091908563/50000000000000 : ℝ), (46420123471121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-203272621/1250000000 : ℝ)|^4887 ≤ (5023846350161/50000000000000 : ℝ)^3863
        have hw : |(-203272621/1250000000 : ℝ)|=(203272621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590970639/5000000000 : ℝ)|^4887 ≤ (21766091908563/50000000000000 : ℝ)^3863
        have hw : |(2590970639/5000000000 : ℝ)|=(2590970639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451840681/10000000000 : ℝ)|^4887 ≤ (46420123471121/100000000000000 : ℝ)^3863
        have hw : |(5451840681/10000000000 : ℝ)|=(5451840681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s2_5 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276861823/10000000000 : ℝ)*x 0 + (-1495390479/10000000000 : ℝ)*x 1 + (5451840047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276861823/10000000000 : ℝ)^4887 ≤ (44543400534713/100000000000000 : ℝ)^3863 := by
    have hnat : (5276861823 : ℕ)^4887*100000000000000^3863 ≤ 44543400534713^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276861823 10000000000 44543400534713 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1495390479/10000000000 : ℝ)^4887 ≤ (1807296561297/20000000000000 : ℝ)^3863 := by
    have hnat : (1495390479 : ℕ)^4887*20000000000000^3863 ≤ 1807296561297^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1495390479 10000000000 1807296561297 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451840047/10000000000 : ℝ)^4887 ≤ (23210058320959/50000000000000 : ℝ)^3863 := by
    have hnat : (5451840047 : ℕ)^4887*50000000000000^3863 ≤ 23210058320959^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451840047 10000000000 23210058320959 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276861823/10000000000 : ℝ), (-1495390479/10000000000 : ℝ), (5451840047/10000000000 : ℝ)] ![(44543400534713/100000000000000 : ℝ), (1807296561297/20000000000000 : ℝ), (23210058320959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276861823/10000000000 : ℝ)|^4887 ≤ (44543400534713/100000000000000 : ℝ)^3863
        have hw : |(5276861823/10000000000 : ℝ)|=(5276861823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1495390479/10000000000 : ℝ)|^4887 ≤ (1807296561297/20000000000000 : ℝ)^3863
        have hw : |(-1495390479/10000000000 : ℝ)|=(1495390479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451840047/10000000000 : ℝ)|^4887 ≤ (23210058320959/50000000000000 : ℝ)^3863
        have hw : |(5451840047/10000000000 : ℝ)|=(5451840047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s2_6 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263843133/500000000 : ℝ)*x 0 + (2725919791/5000000000 : ℝ)*x 1 + (-299077993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263843133/500000000 : ℝ)^4887 ≤ (44543409472927/100000000000000 : ℝ)^3863 := by
    have hnat : (263843133 : ℕ)^4887*100000000000000^3863 ≤ 44543409472927^3863*500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263843133 500000000 44543409472927 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725919791/5000000000 : ℝ)^4887 ≤ (23210055816559/50000000000000 : ℝ)^3863 := by
    have hnat : (2725919791 : ℕ)^4887*50000000000000^3863 ≤ 23210055816559^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725919791 5000000000 23210055816559 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299077993/2000000000 : ℝ)^4887 ≤ (2259119719273/25000000000000 : ℝ)^3863 := by
    have hnat : (299077993 : ℕ)^4887*25000000000000^3863 ≤ 2259119719273^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299077993 2000000000 2259119719273 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263843133/500000000 : ℝ), (2725919791/5000000000 : ℝ), (-299077993/2000000000 : ℝ)] ![(44543409472927/100000000000000 : ℝ), (23210055816559/50000000000000 : ℝ), (2259119719273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263843133/500000000 : ℝ)|^4887 ≤ (44543409472927/100000000000000 : ℝ)^3863
        have hw : |(263843133/500000000 : ℝ)|=(263843133/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725919791/5000000000 : ℝ)|^4887 ≤ (23210055816559/50000000000000 : ℝ)^3863
        have hw : |(2725919791/5000000000 : ℝ)|=(2725919791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-299077993/2000000000 : ℝ)|^4887 ≤ (2259119719273/25000000000000 : ℝ)^3863
        have hw : |(-299077993/2000000000 : ℝ)|=(299077993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s2_7 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093274093/5000000000 : ℝ)*x 0 + (2271414269/5000000000 : ℝ)*x 1 + (770313101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093274093/5000000000 : ℝ)^4887 ≤ (33236715765517/100000000000000 : ℝ)^3863 := by
    have hnat : (2093274093 : ℕ)^4887*100000000000000^3863 ≤ 33236715765517^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093274093 5000000000 33236715765517 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2271414269/5000000000 : ℝ)^4887 ≤ (7370904205587/20000000000000 : ℝ)^3863 := by
    have hnat : (2271414269 : ℕ)^4887*20000000000000^3863 ≤ 7370904205587^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271414269 5000000000 7370904205587 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (770313101/2000000000 : ℝ)^4887 ≤ (29908763198029/100000000000000 : ℝ)^3863 := by
    have hnat : (770313101 : ℕ)^4887*100000000000000^3863 ≤ 29908763198029^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770313101 2000000000 29908763198029 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093274093/5000000000 : ℝ), (2271414269/5000000000 : ℝ), (770313101/2000000000 : ℝ)] ![(33236715765517/100000000000000 : ℝ), (7370904205587/20000000000000 : ℝ), (29908763198029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093274093/5000000000 : ℝ)|^4887 ≤ (33236715765517/100000000000000 : ℝ)^3863
        have hw : |(2093274093/5000000000 : ℝ)|=(2093274093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2271414269/5000000000 : ℝ)|^4887 ≤ (7370904205587/20000000000000 : ℝ)^3863
        have hw : |(2271414269/5000000000 : ℝ)|=(2271414269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(770313101/2000000000 : ℝ)|^4887 ≤ (29908763198029/100000000000000 : ℝ)^3863
        have hw : |(770313101/2000000000 : ℝ)|=(770313101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1642_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4823/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2637/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4093/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4823/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4823/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4823/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4823/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4823/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4823/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4823/50000 : ℝ) ^ (4883/1024 : ℝ) ≤ (358710726017109/25000000000000000000 : ℝ) := by
    have hpowers : (4823/50000 : ℝ)^4883 ≤ (358710726017109/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4823 : ℕ)^4883*25000000000000000000^1024 ≤ 358710726017109^1024*50000^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4823 50000 358710726017109 25000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4823/50000 : ℝ)) (X := (358710726017109/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17383/100000 : ℝ) ^ (4883/1024 : ℝ) ≤ (4759082306215717/20000000000000000000 : ℝ) := by
    have hpowers : (17383/100000 : ℝ)^4883 ≤ (4759082306215717/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17383 : ℕ)^4883*20000000000000000000^1024 ≤ 4759082306215717^1024*100000^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17383 100000 4759082306215717 20000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17383/100000 : ℝ)) (X := (4759082306215717/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500358710726017109/12500000000000000000 : ℝ) ≤ (5000030089340021/5000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (12500358710726017109/12500000000000000000 : ℝ)^1024 ≤ (5000030089340021/5000000000000000 : ℝ)^4883 := by
      have hnat : (12500358710726017109 : ℕ)^1024*5000000000000000^4883 ≤ 5000030089340021^4883*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500358710726017109 12500000000000000000 5000030089340021 5000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000030089340021/5000000000000000 : ℝ)) (X := (12500358710726017109/12500000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025230254435147021/100000000000000000000 : ℝ) ≤ (1000052904372709/1000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (100025230254435147021/100000000000000000000 : ℝ)^1024 ≤ (1000052904372709/1000000000000000 : ℝ)^4883 := by
      have hnat : (100025230254435147021 : ℕ)^1024*1000000000000000^4883 ≤ 1000052904372709^4883*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025230254435147021 100000000000000000000 1000052904372709 1000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000052904372709/1000000000000000 : ℝ)) (X := (100025230254435147021/100000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004759082306215717/10000000000000000000 : ℝ) ≤ (5000498954387069/5000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (10004759082306215717/10000000000000000000 : ℝ)^1024 ≤ (5000498954387069/5000000000000000 : ℝ)^4883 := by
      have hnat : (10004759082306215717 : ℕ)^1024*5000000000000000^4883 ≤ 5000498954387069^4883*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004759082306215717 10000000000000000000 5000498954387069 5000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000498954387069/5000000000000000 : ℝ)) (X := (10004759082306215717/10000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(358710726017109/25000000000000000000 : ℝ) ≤ ((12893570042993305823/12895000000000000000 : ℝ)+2*(19536043627/32237500000000 : ℝ)*(4823/50000 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (12893570042993305823/12895000000000000000 : ℝ)+2*(19536043627/32237500000000 : ℝ)*(4823/50000 : ℝ)=(5000030089340021/5000000000000000 : ℝ) by norm_num, show 1+2*(358710726017109/25000000000000000000 : ℝ)=(12500358710726017109/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4759082306215717/20000000000000000000 : ℝ)+(358710726017109/25000000000000000000 : ℝ) ≤ ((12893570042993305823/12895000000000000000 : ℝ)+(19536043627/32237500000000 : ℝ)*((17383/100000 : ℝ)+(4823/50000 : ℝ)))^(4883/1024 : ℝ) := by
    rw [show (12893570042993305823/12895000000000000000 : ℝ)+(19536043627/32237500000000 : ℝ)*((17383/100000 : ℝ)+(4823/50000 : ℝ))=(1000052904372709/1000000000000000 : ℝ) by norm_num, show 1+(4759082306215717/20000000000000000000 : ℝ)+(358710726017109/25000000000000000000 : ℝ)=(100025230254435147021/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4759082306215717/20000000000000000000 : ℝ) ≤ ((12893570042993305823/12895000000000000000 : ℝ)+2*(19536043627/32237500000000 : ℝ)*(17383/100000 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (12893570042993305823/12895000000000000000 : ℝ)+2*(19536043627/32237500000000 : ℝ)*(17383/100000 : ℝ)=(5000498954387069/5000000000000000 : ℝ) by norm_num, show 1+2*(4759082306215717/20000000000000000000 : ℝ)=(10004759082306215717/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12893570042993305823/12895000000000000000 : ℝ)*(X 1 0+X 2 0)+(19536043627/32237500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (4823/50000 : ℝ)) (hi := (17383/100000 : ℝ)) (c := (12893570042993305823/12895000000000000000 : ℝ)) (alpha := (19536043627/32237500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12893570042993305823/12895000000000000000 : ℝ)*(X 0 1+X 2 1)+(19536043627/32237500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (4823/50000 : ℝ)) (hi := (17383/100000 : ℝ)) (c := (12893570042993305823/12895000000000000000 : ℝ)) (alpha := (19536043627/32237500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12893570042993305823/12895000000000000000 : ℝ)*(X 0 2+X 1 2)+(19536043627/32237500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (4823/50000 : ℝ)) (hi := (17383/100000 : ℝ)) (c := (12893570042993305823/12895000000000000000 : ℝ)) (alpha := (19536043627/32237500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-162611083/1000000000 : ℝ)*X 0 0+(1363497353/2500000000 : ℝ)*X 0 1+(1294953697/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350039969/10000000000 : ℝ)*X 1 0+(-88370827/500000000 : ℝ)*X 1 1+(5179815499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350042203/10000000000 : ℝ)*X 2 0+(207192563/400000000 : ℝ)*X 2 1+(-441853859/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4186365211/10000000000 : ℝ)*X 0 0+(3846060191/10000000000 : ℝ)*X 0 1+(4548275343/10000000000 : ℝ)*X 0 2+(4186365211/10000000000 : ℝ)*X 1 0+(3846060191/10000000000 : ℝ)*X 1 1+(4548275343/10000000000 : ℝ)*X 1 2+(4186365211/10000000000 : ℝ)*X 2 0+(3846060191/10000000000 : ℝ)*X 2 1+(4548275343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-203272621/1250000000 : ℝ)*X 0 0+(2590970639/5000000000 : ℝ)*X 0 1+(5451840681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276861823/10000000000 : ℝ)*X 1 0+(-1495390479/10000000000 : ℝ)*X 1 1+(5451840047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((263843133/500000000 : ℝ)*X 2 0+(2725919791/5000000000 : ℝ)*X 2 1+(-299077993/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2093274093/5000000000 : ℝ)*X 0 0+(2271414269/5000000000 : ℝ)*X 0 1+(770313101/2000000000 : ℝ)*X 0 2+(2093274093/5000000000 : ℝ)*X 1 0+(2271414269/5000000000 : ℝ)*X 1 1+(770313101/2000000000 : ℝ)*X 1 2+(2093274093/5000000000 : ℝ)*X 2 0+(2271414269/5000000000 : ℝ)*X 2 1+(770313101/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32517195832891195162797/6447500000000000000000000000 : ℝ) := by norm_num
    linear_combination (27153319/50000000000000 : ℝ)*(base19) + (1469248797/100000000000000 : ℝ)*(base23) + (15981877/12500000000000 : ℝ)*(upper4) + (613707/160000000000 : ℝ)*(upper5) + (633926028739271/25000000000000 : ℝ)*(major0) + (633926028739271/25000000000000 : ℝ)*(major1) + (633926028739271/25000000000000 : ℝ)*(major2) + (364731275482227/10000000000000 : ℝ)*(sp0) + (911830798968079/25000000000000 : ℝ)*(sp1) + (455916419027101/12500000000000 : ℝ)*(sp2) + (178008750251529/12500000000000 : ℝ)*(sp3) + (10033321667/50000000000000 : ℝ)*(sp4) + (9571286651/100000000000000 : ℝ)*(sp5) + (5238323639/100000000000000 : ℝ)*(sp7) + (2781396953781/195312500000 : ℝ)*(f.failure) + (911833205366401/25000000000000 : ℝ)*(f.sum) + (22774822619357/6447500000000000000000000000 : ℝ)*base65 + (2129007532138125033/322375000000000000000000000000000 : ℝ)*base67 + (149574967623000033/322375000000000000000000000000000 : ℝ)*base69 + (724088780319749967/322375000000000000000000000000000 : ℝ)*base72 + (97165941684969/12895000000000000000000000000 : ℝ)*base73 + (2624055414101124967/322375000000000000000000000000000 : ℝ)*base76 + (3036762132653625033/322375000000000000000000000000000 : ℝ)*base77 + (659544763378374967/322375000000000000000000000000000 : ℝ)*base80 + (36522608948559/12895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (210731/19531250000000000000 : ℝ)*base89 + (210731/19531250000000000000 : ℝ)*base91 + (210731/19531250000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52945948976105106245413299/16118750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216032437/100000000000000 : ℝ)*(base19) + (537590443/50000000000000 : ℝ)*(base23) + (523723/390625000000 : ℝ)*(lower2) + (24933997/100000000000000 : ℝ)*(lower3) + (209037487/100000000000000 : ℝ)*(lower4) + (64396533601679/2500000000000 : ℝ)*(major0) + (64396533601679/2500000000000 : ℝ)*(major1) + (64396533601679/2500000000000 : ℝ)*(major2) + (513342661/12500000000000 : ℝ)*(sp0) + (4665240451/50000000000000 : ℝ)*(sp2) + (3705090554635153/100000000000000 : ℝ)*(sp4) + (926273611336001/25000000000000 : ℝ)*(sp5) + (3705084255714653/100000000000000 : ℝ)*(sp6) + (289325583453289/20000000000000 : ℝ)*(sp7) + (289325583453289/20000000000000 : ℝ)*(f.failure) + (3705094661376441/100000000000000 : ℝ)*(f.sum) + (8308380655271/1289500000000000000000000000 : ℝ)*base66 + (28521564848523183/32237500000000000000000000000000 : ℝ)*base68 + (32593956830251817/32237500000000000000000000000000 : ℝ)*base69 + (17243355532751817/32237500000000000000000000000000 : ℝ)*base71 + (3479753978943/1289500000000000000000000000 : ℝ)*base73 + (52326464461139317/32237500000000000000000000000000 : ℝ)*base75 + (42823657236176817/32237500000000000000000000000000 : ℝ)*base77 + (76404004385698183/32237500000000000000000000000000 : ℝ)*base80 + (441695035621/128950000000000000000000000 : ℝ)*base82 + (13193411/2000000000000000000000 : ℝ)*base90 + (13193411/2000000000000000000000 : ℝ)*base92 + (13193411/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1642_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4823/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1642_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1642_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1642_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1642_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1642_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1642_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
