-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1581_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:02.303506+00:00
-- url     : https://prove2.me/submissions/c66e175f-1a39-41a8-af83-8843bd7d212f

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
theorem support_rectangle_w1581_s3_0 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22130973/125000000 : ℝ)*x 0 + (1085173401/2000000000 : ℝ)*x 1 + (5219096209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22130973/125000000 : ℝ)^4659 ≤ (67944352577/625000000000 : ℝ)^3635 := by
    have hnat : (22130973 : ℕ)^4659*625000000000^3635 ≤ 67944352577^3635*125000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22130973 125000000 67944352577 625000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085173401/2000000000 : ℝ)^4659 ≤ (22836924141043/50000000000000 : ℝ)^3635 := by
    have hnat : (1085173401 : ℕ)^4659*50000000000000^3635 ≤ 22836924141043^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085173401 2000000000 22836924141043 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219096209/10000000000 : ℝ)^4659 ≤ (1738202211679/4000000000000 : ℝ)^3635 := by
    have hnat : (5219096209 : ℕ)^4659*4000000000000^3635 ≤ 1738202211679^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219096209 10000000000 1738202211679 4000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22130973/125000000 : ℝ), (1085173401/2000000000 : ℝ), (5219096209/10000000000 : ℝ)] ![(67944352577/625000000000 : ℝ), (22836924141043/50000000000000 : ℝ), (1738202211679/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22130973/125000000 : ℝ)|^4659 ≤ (67944352577/625000000000 : ℝ)^3635
        have hw : |(-22130973/125000000 : ℝ)|=(22130973/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085173401/2000000000 : ℝ)|^4659 ≤ (22836924141043/50000000000000 : ℝ)^3635
        have hw : |(1085173401/2000000000 : ℝ)|=(1085173401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219096209/10000000000 : ℝ)|^4659 ≤ (1738202211679/4000000000000 : ℝ)^3635
        have hw : |(5219096209/10000000000 : ℝ)|=(5219096209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s3_1 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347899713/10000000000 : ℝ)*x 0 + (-187627057/1000000000 : ℝ)*x 1 + (2609548097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347899713/10000000000 : ℝ)^4659 ≤ (44834356870571/100000000000000 : ℝ)^3635 := by
    have hnat : (5347899713 : ℕ)^4659*100000000000000^3635 ≤ 44834356870571^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347899713 10000000000 44834356870571 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187627057/1000000000 : ℝ)^4659 ≤ (1171058797781/10000000000000 : ℝ)^3635 := by
    have hnat : (187627057 : ℕ)^4659*10000000000000^3635 ≤ 1171058797781^3635*1000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187627057 1000000000 1171058797781 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609548097/5000000000 : ℝ)^4659 ≤ (43455055131899/100000000000000 : ℝ)^3635 := by
    have hnat : (2609548097 : ℕ)^4659*100000000000000^3635 ≤ 43455055131899^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609548097 5000000000 43455055131899 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347899713/10000000000 : ℝ), (-187627057/1000000000 : ℝ), (2609548097/5000000000 : ℝ)] ![(44834356870571/100000000000000 : ℝ), (1171058797781/10000000000000 : ℝ), (43455055131899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347899713/10000000000 : ℝ)|^4659 ≤ (44834356870571/100000000000000 : ℝ)^3635
        have hw : |(5347899713/10000000000 : ℝ)|=(5347899713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-187627057/1000000000 : ℝ)|^4659 ≤ (1171058797781/10000000000000 : ℝ)^3635
        have hw : |(-187627057/1000000000 : ℝ)|=(187627057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609548097/5000000000 : ℝ)|^4659 ≤ (43455055131899/100000000000000 : ℝ)^3635
        have hw : |(2609548097/5000000000 : ℝ)|=(2609548097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s3_2 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673949883/5000000000 : ℝ)*x 0 + (5219096107/10000000000 : ℝ)*x 1 + (-375254123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673949883/5000000000 : ℝ)^4659 ≤ (11208589360017/25000000000000 : ℝ)^3635 := by
    have hnat : (2673949883 : ℕ)^4659*25000000000000^3635 ≤ 11208589360017^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673949883 5000000000 11208589360017 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219096107/10000000000 : ℝ)^4659 ≤ (21727527101731/50000000000000 : ℝ)^3635 := by
    have hnat : (5219096107 : ℕ)^4659*50000000000000^3635 ≤ 21727527101731^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219096107 10000000000 21727527101731 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375254123/2000000000 : ℝ)^4659 ≤ (2342117667559/20000000000000 : ℝ)^3635 := by
    have hnat : (375254123 : ℕ)^4659*20000000000000^3635 ≤ 2342117667559^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375254123 2000000000 2342117667559 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673949883/5000000000 : ℝ), (5219096107/10000000000 : ℝ), (-375254123/2000000000 : ℝ)] ![(11208589360017/25000000000000 : ℝ), (21727527101731/50000000000000 : ℝ), (2342117667559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673949883/5000000000 : ℝ)|^4659 ≤ (11208589360017/25000000000000 : ℝ)^3635
        have hw : |(2673949883/5000000000 : ℝ)|=(2673949883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219096107/10000000000 : ℝ)|^4659 ≤ (21727527101731/50000000000000 : ℝ)^3635
        have hw : |(5219096107/10000000000 : ℝ)|=(5219096107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-375254123/2000000000 : ℝ)|^4659 ≤ (2342117667559/20000000000000 : ℝ)^3635
        have hw : |(-375254123/2000000000 : ℝ)|=(375254123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s3_3 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238548669/10000000000 : ℝ)*x 0 + (499799527/1250000000 : ℝ)*x 1 + (1122537839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238548669/10000000000 : ℝ)^4659 ≤ (8320360788201/25000000000000 : ℝ)^3635 := by
    have hnat : (4238548669 : ℕ)^4659*25000000000000^3635 ≤ 8320360788201^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238548669 10000000000 8320360788201 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499799527/1250000000 : ℝ)^4659 ≤ (15442045386771/50000000000000 : ℝ)^3635 := by
    have hnat : (499799527 : ℕ)^4659*50000000000000^3635 ≤ 15442045386771^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499799527 1250000000 15442045386771 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122537839/2500000000 : ℝ)^4659 ≤ (35834466058691/100000000000000 : ℝ)^3635 := by
    have hnat : (1122537839 : ℕ)^4659*100000000000000^3635 ≤ 35834466058691^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122537839 2500000000 35834466058691 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238548669/10000000000 : ℝ), (499799527/1250000000 : ℝ), (1122537839/2500000000 : ℝ)] ![(8320360788201/25000000000000 : ℝ), (15442045386771/50000000000000 : ℝ), (35834466058691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238548669/10000000000 : ℝ)|^4659 ≤ (8320360788201/25000000000000 : ℝ)^3635
        have hw : |(4238548669/10000000000 : ℝ)|=(4238548669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499799527/1250000000 : ℝ)|^4659 ≤ (15442045386771/50000000000000 : ℝ)^3635
        have hw : |(499799527/1250000000 : ℝ)|=(499799527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122537839/2500000000 : ℝ)|^4659 ≤ (35834466058691/100000000000000 : ℝ)^3635
        have hw : |(1122537839/2500000000 : ℝ)|=(1122537839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s3_4 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1770505567/10000000000 : ℝ)*x 0 + (5220190209/10000000000 : ℝ)*x 1 + (43398117/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1770505567/10000000000 : ℝ)^4659 ≤ (1087131462249/10000000000000 : ℝ)^3635 := by
    have hnat : (1770505567 : ℕ)^4659*10000000000000^3635 ≤ 1087131462249^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770505567 10000000000 1087131462249 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220190209/10000000000 : ℝ)^4659 ≤ (43466730468159/100000000000000 : ℝ)^3635 := by
    have hnat : (5220190209 : ℕ)^4659*100000000000000^3635 ≤ 43466730468159^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220190209 10000000000 43466730468159 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43398117/80000000 : ℝ)^4659 ≤ (11415488723077/25000000000000 : ℝ)^3635 := by
    have hnat : (43398117 : ℕ)^4659*25000000000000^3635 ≤ 11415488723077^3635*80000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43398117 80000000 11415488723077 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1770505567/10000000000 : ℝ), (5220190209/10000000000 : ℝ), (43398117/80000000 : ℝ)] ![(1087131462249/10000000000000 : ℝ), (43466730468159/100000000000000 : ℝ), (11415488723077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1770505567/10000000000 : ℝ)|^4659 ≤ (1087131462249/10000000000000 : ℝ)^3635
        have hw : |(-1770505567/10000000000 : ℝ)|=(1770505567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220190209/10000000000 : ℝ)|^4659 ≤ (43466730468159/100000000000000 : ℝ)^3635
        have hw : |(5220190209/10000000000 : ℝ)|=(5220190209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43398117/80000000 : ℝ)|^4659 ≤ (11415488723077/25000000000000 : ℝ)^3635
        have hw : |(43398117/80000000 : ℝ)|=(43398117/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s3_5 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646562241/5000000000 : ℝ)*x 0 + (-417650619/2500000000 : ℝ)*x 1 + (2712382041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646562241/5000000000 : ℝ)^4659 ≤ (8849327051461/20000000000000 : ℝ)^3635 := by
    have hnat : (2646562241 : ℕ)^4659*20000000000000^3635 ≤ 8849327051461^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646562241 5000000000 8849327051461 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417650619/2500000000 : ℝ)^4659 ≤ (10091415689159/100000000000000 : ℝ)^3635 := by
    have hnat : (417650619 : ℕ)^4659*100000000000000^3635 ≤ 10091415689159^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417650619 2500000000 10091415689159 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712382041/5000000000 : ℝ)^4659 ≤ (22830974517071/50000000000000 : ℝ)^3635 := by
    have hnat : (2712382041 : ℕ)^4659*50000000000000^3635 ≤ 22830974517071^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712382041 5000000000 22830974517071 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646562241/5000000000 : ℝ), (-417650619/2500000000 : ℝ), (2712382041/5000000000 : ℝ)] ![(8849327051461/20000000000000 : ℝ), (10091415689159/100000000000000 : ℝ), (22830974517071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646562241/5000000000 : ℝ)|^4659 ≤ (8849327051461/20000000000000 : ℝ)^3635
        have hw : |(2646562241/5000000000 : ℝ)|=(2646562241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417650619/2500000000 : ℝ)|^4659 ≤ (10091415689159/100000000000000 : ℝ)^3635
        have hw : |(-417650619/2500000000 : ℝ)|=(417650619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712382041/5000000000 : ℝ)|^4659 ≤ (22830974517071/50000000000000 : ℝ)^3635
        have hw : |(2712382041/5000000000 : ℝ)|=(2712382041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s3_6 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661640657/1250000000 : ℝ)*x 0 + (84761941/156250000 : ℝ)*x 1 + (-208825151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661640657/1250000000 : ℝ)^4659 ≤ (44246643550033/100000000000000 : ℝ)^3635 := by
    have hnat : (661640657 : ℕ)^4659*100000000000000^3635 ≤ 44246643550033^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661640657 1250000000 44246643550033 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84761941/156250000 : ℝ)^4659 ≤ (1426935955191/3125000000000 : ℝ)^3635 := by
    have hnat : (84761941 : ℕ)^4659*3125000000000^3635 ≤ 1426935955191^3635*156250000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84761941 156250000 1426935955191 3125000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208825151/1250000000 : ℝ)^4659 ≤ (2018281174397/20000000000000 : ℝ)^3635 := by
    have hnat : (208825151 : ℕ)^4659*20000000000000^3635 ≤ 2018281174397^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208825151 1250000000 2018281174397 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661640657/1250000000 : ℝ), (84761941/156250000 : ℝ), (-208825151/1250000000 : ℝ)] ![(44246643550033/100000000000000 : ℝ), (1426935955191/3125000000000 : ℝ), (2018281174397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661640657/1250000000 : ℝ)|^4659 ≤ (44246643550033/100000000000000 : ℝ)^3635
        have hw : |(661640657/1250000000 : ℝ)|=(661640657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84761941/156250000 : ℝ)|^4659 ≤ (1426935955191/3125000000000 : ℝ)^3635
        have hw : |(84761941/156250000 : ℝ)|=(84761941/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208825151/1250000000 : ℝ)|^4659 ≤ (2018281174397/20000000000000 : ℝ)^3635
        have hw : |(-208825151/1250000000 : ℝ)|=(208825151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s3_7 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2119306787/5000000000 : ℝ)*x 0 + (2243774687/5000000000 : ℝ)*x 1 + (4001018183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119306787/5000000000 : ℝ)^4659 ≤ (33282096362107/100000000000000 : ℝ)^3635 := by
    have hnat : (2119306787 : ℕ)^4659*100000000000000^3635 ≤ 33282096362107^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119306787 5000000000 33282096362107 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243774687/5000000000 : ℝ)^4659 ≤ (35807852859423/100000000000000 : ℝ)^3635 := by
    have hnat : (2243774687 : ℕ)^4659*100000000000000^3635 ≤ 35807852859423^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243774687 5000000000 35807852859423 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4001018183/10000000000 : ℝ)^4659 ≤ (15455025384571/50000000000000 : ℝ)^3635 := by
    have hnat : (4001018183 : ℕ)^4659*50000000000000^3635 ≤ 15455025384571^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001018183 10000000000 15455025384571 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2119306787/5000000000 : ℝ), (2243774687/5000000000 : ℝ), (4001018183/10000000000 : ℝ)] ![(33282096362107/100000000000000 : ℝ), (35807852859423/100000000000000 : ℝ), (15455025384571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2119306787/5000000000 : ℝ)|^4659 ≤ (33282096362107/100000000000000 : ℝ)^3635
        have hw : |(2119306787/5000000000 : ℝ)|=(2119306787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243774687/5000000000 : ℝ)|^4659 ≤ (35807852859423/100000000000000 : ℝ)^3635
        have hw : |(2243774687/5000000000 : ℝ)|=(2243774687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4001018183/10000000000 : ℝ)|^4659 ≤ (15455025384571/50000000000000 : ℝ)^3635
        have hw : |(4001018183/10000000000 : ℝ)|=(4001018183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s3_8 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46455953/10000000000 : ℝ)*x 0 + (2909053809/5000000000 : ℝ)*x 1 + (5818235007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46455953/10000000000 : ℝ)^4659 ≤ (12786267459/12500000000000 : ℝ)^3635 := by
    have hnat : (46455953 : ℕ)^4659*12500000000000^3635 ≤ 12786267459^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46455953 10000000000 12786267459 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2909053809/5000000000 : ℝ)^4659 ≤ (49948154067069/100000000000000 : ℝ)^3635 := by
    have hnat : (2909053809 : ℕ)^4659*100000000000000^3635 ≤ 49948154067069^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2909053809 5000000000 49948154067069 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5818235007/10000000000 : ℝ)^4659 ≤ (49949555780567/100000000000000 : ℝ)^3635 := by
    have hnat : (5818235007 : ℕ)^4659*100000000000000^3635 ≤ 49949555780567^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5818235007 10000000000 49949555780567 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46455953/10000000000 : ℝ), (2909053809/5000000000 : ℝ), (5818235007/10000000000 : ℝ)] ![(12786267459/12500000000000 : ℝ), (49948154067069/100000000000000 : ℝ), (49949555780567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46455953/10000000000 : ℝ)|^4659 ≤ (12786267459/12500000000000 : ℝ)^3635
        have hw : |(-46455953/10000000000 : ℝ)|=(46455953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2909053809/5000000000 : ℝ)|^4659 ≤ (49948154067069/100000000000000 : ℝ)^3635
        have hw : |(2909053809/5000000000 : ℝ)|=(2909053809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5818235007/10000000000 : ℝ)|^4659 ≤ (49949555780567/100000000000000 : ℝ)^3635
        have hw : |(5818235007/10000000000 : ℝ)|=(5818235007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s3_9 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (230463629/2000000000 : ℝ)*x 0 + (110963777/156250000 : ℝ)*x 1 + (-3831469953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230463629/2000000000 : ℝ)^4659 ≤ (3134599484029/50000000000000 : ℝ)^3635 := by
    have hnat : (230463629 : ℕ)^4659*50000000000000^3635 ≤ 3134599484029^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230463629 2000000000 3134599484029 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110963777/156250000 : ℝ)^4659 ≤ (64489471525689/100000000000000 : ℝ)^3635 := by
    have hnat : (110963777 : ℕ)^4659*100000000000000^3635 ≤ 64489471525689^3635*156250000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110963777 156250000 64489471525689 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3831469953/10000000000 : ℝ)^4659 ≤ (29241329489107/100000000000000 : ℝ)^3635 := by
    have hnat : (3831469953 : ℕ)^4659*100000000000000^3635 ≤ 29241329489107^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3831469953 10000000000 29241329489107 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(230463629/2000000000 : ℝ), (110963777/156250000 : ℝ), (-3831469953/10000000000 : ℝ)] ![(3134599484029/50000000000000 : ℝ), (64489471525689/100000000000000 : ℝ), (29241329489107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(230463629/2000000000 : ℝ)|^4659 ≤ (3134599484029/50000000000000 : ℝ)^3635
        have hw : |(230463629/2000000000 : ℝ)|=(230463629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110963777/156250000 : ℝ)|^4659 ≤ (64489471525689/100000000000000 : ℝ)^3635
        have hw : |(110963777/156250000 : ℝ)|=(110963777/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3831469953/10000000000 : ℝ)|^4659 ≤ (29241329489107/100000000000000 : ℝ)^3635
        have hw : |(-3831469953/10000000000 : ℝ)|=(3831469953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s3_10 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1839376233/10000000000 : ℝ)*x 0 + (355711477/625000000 : ℝ)*x 1 + (4894862211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1839376233/10000000000 : ℝ)^4659 ≤ (178379174321/1562500000000 : ℝ)^3635 := by
    have hnat : (1839376233 : ℕ)^4659*1562500000000^3635 ≤ 178379174321^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839376233 10000000000 178379174321 1562500000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355711477/625000000 : ℝ)^4659 ≤ (48558062680461/100000000000000 : ℝ)^3635 := by
    have hnat : (355711477 : ℕ)^4659*100000000000000^3635 ≤ 48558062680461^3635*625000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355711477 625000000 48558062680461 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4894862211/10000000000 : ℝ)^4659 ≤ (40025670144923/100000000000000 : ℝ)^3635 := by
    have hnat : (4894862211 : ℕ)^4659*100000000000000^3635 ≤ 40025670144923^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4894862211 10000000000 40025670144923 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1839376233/10000000000 : ℝ), (355711477/625000000 : ℝ), (4894862211/10000000000 : ℝ)] ![(178379174321/1562500000000 : ℝ), (48558062680461/100000000000000 : ℝ), (40025670144923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1839376233/10000000000 : ℝ)|^4659 ≤ (178379174321/1562500000000 : ℝ)^3635
        have hw : |(1839376233/10000000000 : ℝ)|=(1839376233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(355711477/625000000 : ℝ)|^4659 ≤ (48558062680461/100000000000000 : ℝ)^3635
        have hw : |(355711477/625000000 : ℝ)|=(355711477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4894862211/10000000000 : ℝ)|^4659 ≤ (40025670144923/100000000000000 : ℝ)^3635
        have hw : |(4894862211/10000000000 : ℝ)|=(4894862211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1581_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    (1391/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7757/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15783/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15783/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15783/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15783/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15783/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15783/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (68/625 : ℝ) ^ (4657/1024 : ℝ) ≤ (2078266421786461/50000000000000000000 : ℝ) := by
    have hpowers : (68/625 : ℝ)^4657 ≤ (2078266421786461/50000000000000000000 : ℝ)^1024 := by
      have hnat : (68 : ℕ)^4657*50000000000000000000^1024 ≤ 2078266421786461^1024*625^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68 625 2078266421786461 50000000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68/625 : ℝ)) (X := (2078266421786461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15783/100000 : ℝ) ^ (4657/1024 : ℝ) ≤ (5641896703211889/25000000000000000000 : ℝ) := by
    have hpowers : (15783/100000 : ℝ)^4657 ≤ (5641896703211889/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15783 : ℕ)^4657*25000000000000000000^1024 ≤ 5641896703211889^1024*100000^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15783 100000 5641896703211889 25000000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15783/100000 : ℝ)) (X := (5641896703211889/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002078266421786461/25000000000000000000 : ℝ) ≤ (200003655702491/200000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (25002078266421786461/25000000000000000000 : ℝ)^1024 ≤ (200003655702491/200000000000000 : ℝ)^4657 := by
      have hnat : (25002078266421786461 : ℕ)^1024*200000000000000^4657 ≤ 200003655702491^4657*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002078266421786461 25000000000000000000 200003655702491 200000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200003655702491/200000000000000 : ℝ)) (X := (25002078266421786461/25000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013362059828210239/50000000000000000000 : ℝ) ≤ (2500146889877673/2500000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (50013362059828210239/50000000000000000000 : ℝ)^1024 ≤ (2500146889877673/2500000000000000 : ℝ)^4657 := by
      have hnat : (50013362059828210239 : ℕ)^1024*2500000000000000^4657 ≤ 2500146889877673^4657*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013362059828210239 50000000000000000000 2500146889877673 2500000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500146889877673/2500000000000000 : ℝ)) (X := (50013362059828210239/50000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505641896703211889/12500000000000000000 : ℝ) ≤ (5000496166948417/5000000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (12505641896703211889/12500000000000000000 : ℝ)^1024 ≤ (5000496166948417/5000000000000000 : ℝ)^4657 := by
      have hnat : (12505641896703211889 : ℕ)^1024*5000000000000000^4657 ≤ 5000496166948417^4657*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505641896703211889 12500000000000000000 5000496166948417 5000000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000496166948417/5000000000000000 : ℝ)) (X := (12505641896703211889/12500000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2078266421786461/50000000000000000000 : ℝ) ≤ ((4902208830482321873/4903000000000000000 : ℝ)+2*(202387193071/245150000000000 : ℝ)*(68/625 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (4902208830482321873/4903000000000000000 : ℝ)+2*(202387193071/245150000000000 : ℝ)*(68/625 : ℝ)=(200003655702491/200000000000000 : ℝ) by norm_num, show 1+2*(2078266421786461/50000000000000000000 : ℝ)=(25002078266421786461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5641896703211889/25000000000000000000 : ℝ)+(2078266421786461/50000000000000000000 : ℝ) ≤ ((4902208830482321873/4903000000000000000 : ℝ)+(202387193071/245150000000000 : ℝ)*((15783/100000 : ℝ)+(68/625 : ℝ)))^(4657/1024 : ℝ) := by
    rw [show (4902208830482321873/4903000000000000000 : ℝ)+(202387193071/245150000000000 : ℝ)*((15783/100000 : ℝ)+(68/625 : ℝ))=(2500146889877673/2500000000000000 : ℝ) by norm_num, show 1+(5641896703211889/25000000000000000000 : ℝ)+(2078266421786461/50000000000000000000 : ℝ)=(50013362059828210239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5641896703211889/25000000000000000000 : ℝ) ≤ ((4902208830482321873/4903000000000000000 : ℝ)+2*(202387193071/245150000000000 : ℝ)*(15783/100000 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (4902208830482321873/4903000000000000000 : ℝ)+2*(202387193071/245150000000000 : ℝ)*(15783/100000 : ℝ)=(5000496166948417/5000000000000000 : ℝ) by norm_num, show 1+2*(5641896703211889/25000000000000000000 : ℝ)=(12505641896703211889/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4902208830482321873/4903000000000000000 : ℝ)*(X 1 0+X 2 0)+(202387193071/245150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (15783/100000 : ℝ)) (c := (4902208830482321873/4903000000000000000 : ℝ)) (alpha := (202387193071/245150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4902208830482321873/4903000000000000000 : ℝ)*(X 0 1+X 2 1)+(202387193071/245150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (15783/100000 : ℝ)) (c := (4902208830482321873/4903000000000000000 : ℝ)) (alpha := (202387193071/245150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4902208830482321873/4903000000000000000 : ℝ)*(X 0 2+X 1 2)+(202387193071/245150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (15783/100000 : ℝ)) (c := (4902208830482321873/4903000000000000000 : ℝ)) (alpha := (202387193071/245150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-22130973/125000000 : ℝ)*X 0 0+(1085173401/2000000000 : ℝ)*X 0 1+(5219096209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347899713/10000000000 : ℝ)*X 1 0+(-187627057/1000000000 : ℝ)*X 1 1+(2609548097/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673949883/5000000000 : ℝ)*X 2 0+(5219096107/10000000000 : ℝ)*X 2 1+(-375254123/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4238548669/10000000000 : ℝ)*X 0 0+(499799527/1250000000 : ℝ)*X 0 1+(1122537839/2500000000 : ℝ)*X 0 2+(4238548669/10000000000 : ℝ)*X 1 0+(499799527/1250000000 : ℝ)*X 1 1+(1122537839/2500000000 : ℝ)*X 1 2+(4238548669/10000000000 : ℝ)*X 2 0+(499799527/1250000000 : ℝ)*X 2 1+(1122537839/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1770505567/10000000000 : ℝ)*X 0 0+(5220190209/10000000000 : ℝ)*X 0 1+(43398117/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646562241/5000000000 : ℝ)*X 1 0+(-417650619/2500000000 : ℝ)*X 1 1+(2712382041/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661640657/1250000000 : ℝ)*X 2 0+(84761941/156250000 : ℝ)*X 2 1+(-208825151/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2119306787/5000000000 : ℝ)*X 0 0+(2243774687/5000000000 : ℝ)*X 0 1+(4001018183/10000000000 : ℝ)*X 0 2+(2119306787/5000000000 : ℝ)*X 1 0+(2243774687/5000000000 : ℝ)*X 1 1+(4001018183/10000000000 : ℝ)*X 1 2+(2119306787/5000000000 : ℝ)*X 2 0+(2243774687/5000000000 : ℝ)*X 2 1+(4001018183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-46455953/10000000000 : ℝ)*X 0 0+(2909053809/5000000000 : ℝ)*X 0 1+(5818235007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((230463629/2000000000 : ℝ)*X 2 0+(110963777/156250000 : ℝ)*X 2 1+(-3831469953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1839376233/10000000000 : ℝ)*X 0 0+(355711477/625000000 : ℝ)*X 0 1+(4894862211/10000000000 : ℝ)*X 0 2+(1839376233/10000000000 : ℝ)*X 1 0+(355711477/625000000 : ℝ)*X 1 1+(4894862211/10000000000 : ℝ)*X 1 2+(1839376233/10000000000 : ℝ)*X 2 0+(355711477/625000000 : ℝ)*X 2 1+(4894862211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s3_10 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (619525538643880547037163809/61287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32426853/25000000000000 : ℝ)*(lower3) + (277376411/100000000000000 : ℝ)*(lower5) + (858727155836989/25000000000000 : ℝ)*(major0) + (858727155836989/25000000000000 : ℝ)*(major1) + (3434908623347957/100000000000000 : ℝ)*(major2) + (4836277587732539/100000000000000 : ℝ)*(sp0) + (483627885110059/10000000000000 : ℝ)*(sp1) + (4836280401546553/100000000000000 : ℝ)*(sp2) + (1016767144855039/50000000000000 : ℝ)*(sp3) + (222233619/50000000000000 : ℝ)*(sp4) + (816428591/50000000000000 : ℝ)*(sp5) + (490351599/20000000000000 : ℝ)*(sp8) + (41205609/50000000000000 : ℝ)*(sp9) + (1068038799/50000000000000 : ℝ)*(sp10) + (508384106446919/25000000000000 : ℝ)*(f.failure) + (4836280483957771/100000000000000 : ℝ)*(f.sum) + (11454411263651/12257500000000000000000000000 : ℝ)*base66 + (626220394235429603/122575000000000000000000000000000 : ℝ)*base68 + (3918426514365116539/490300000000000000000000000000000 : ℝ)*base70 + (159058821853645397/122575000000000000000000000000000 : ℝ)*base71 + (112904644582957/24515000000000000000000000000 : ℝ)*base74 + (1056323978809483461/490300000000000000000000000000000 : ℝ)*base75 + (399409708912240397/122575000000000000000000000000000 : ℝ)*base77 + (78966429654615397/122575000000000000000000000000000 : ℝ)*base79 + (188263163582203/24515000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (22309059/2500000000000000000000 : ℝ)*base89 + (22309059/2500000000000000000000 : ℝ)*base91 + (2690941/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5640050696134978662574203/2451500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (351703047/100000000000000 : ℝ)*(lower3) + (26322339/50000000000000 : ℝ)*(lower5) + (69435826430737/2000000000000 : ℝ)*(major0) + (69435826430737/2000000000000 : ℝ)*(major1) + (69435826430737/2000000000000 : ℝ)*(major2) + (362425201/4000000000000 : ℝ)*(sp2) + (115631737/3125000000000 : ℝ)*(sp3) + (15275651979447/312500000000 : ℝ)*(sp4) + (1222052706511377/25000000000000 : ℝ)*(sp5) + (2444100365928449/50000000000000 : ℝ)*(sp6) + (16057556011747/781250000000 : ℝ)*(sp7) + (548155617/25000000000000 : ℝ)*(sp8) + (206711717/20000000000000 : ℝ)*(sp9) + (435310277/50000000000000 : ℝ)*(sp10) + (1027685870169877/50000000000000 : ℝ)*(f.failure) + (1222052706511377/25000000000000 : ℝ)*(f.sum) + (4529755455847/2451500000000000000000000000 : ℝ)*base66 + (48731252002289599/9806000000000000000000000000000 : ℝ)*base68 + (201169920601261599/9806000000000000000000000000000 : ℝ)*base70 + (13848227937442401/9806000000000000000000000000000 : ℝ)*base71 + (4099654882199/1225750000000000000000000000 : ℝ)*base73 + (116755424403541599/9806000000000000000000000000000 : ℝ)*base76 + (92711495259199599/9806000000000000000000000000000 : ℝ)*base78 + (26011614136427599/9806000000000000000000000000000 : ℝ)*base80 + (14426959061423/2451500000000000000000000000 : ℝ)*base82 + (14063497/5000000000000000000000 : ℝ)*base89 + (14063497/5000000000000000000000 : ℝ)*base91 + (14063497/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1581_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7757/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1581_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1581_s4_0 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1770676123/10000000000 : ℝ)*x 0 + (2712266633/5000000000 : ℝ)*x 1 + (652537289/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1770676123/10000000000 : ℝ)^4659 ≤ (10872656911263/100000000000000 : ℝ)^3635 := by
    have hnat : (1770676123 : ℕ)^4659*100000000000000^3635 ≤ 10872656911263^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770676123 10000000000 10872656911263 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712266633/5000000000 : ℝ)^4659 ≤ (45659458885957/100000000000000 : ℝ)^3635 := by
    have hnat : (2712266633 : ℕ)^4659*100000000000000^3635 ≤ 45659458885957^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712266633 5000000000 45659458885957 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652537289/1250000000 : ℝ)^4659 ≤ (43467884181607/100000000000000 : ℝ)^3635 := by
    have hnat : (652537289 : ℕ)^4659*100000000000000^3635 ≤ 43467884181607^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652537289 1250000000 43467884181607 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1770676123/10000000000 : ℝ), (2712266633/5000000000 : ℝ), (652537289/1250000000 : ℝ)] ![(10872656911263/100000000000000 : ℝ), (45659458885957/100000000000000 : ℝ), (43467884181607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1770676123/10000000000 : ℝ)|^4659 ≤ (10872656911263/100000000000000 : ℝ)^3635
        have hw : |(-1770676123/10000000000 : ℝ)|=(1770676123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712266633/5000000000 : ℝ)|^4659 ≤ (45659458885957/100000000000000 : ℝ)^3635
        have hw : |(2712266633/5000000000 : ℝ)|=(2712266633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652537289/1250000000 : ℝ)|^4659 ≤ (43467884181607/100000000000000 : ℝ)^3635
        have hw : |(652537289/1250000000 : ℝ)|=(652537289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s4_1 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347545543/10000000000 : ℝ)*x 0 + (-234392903/1250000000 : ℝ)*x 1 + (5220297767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347545543/10000000000 : ℝ)^4659 ≤ (44830551265603/100000000000000 : ℝ)^3635 := by
    have hnat : (5347545543 : ℕ)^4659*100000000000000^3635 ≤ 44830551265603^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347545543 10000000000 44830551265603 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234392903/1250000000 : ℝ)^4659 ≤ (11701570356433/100000000000000 : ℝ)^3635 := by
    have hnat : (234392903 : ℕ)^4659*100000000000000^3635 ≤ 11701570356433^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234392903 1250000000 11701570356433 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220297767/10000000000 : ℝ)^4659 ≤ (43467878365157/100000000000000 : ℝ)^3635 := by
    have hnat : (5220297767 : ℕ)^4659*100000000000000^3635 ≤ 43467878365157^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220297767 10000000000 43467878365157 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347545543/10000000000 : ℝ), (-234392903/1250000000 : ℝ), (5220297767/10000000000 : ℝ)] ![(44830551265603/100000000000000 : ℝ), (11701570356433/100000000000000 : ℝ), (43467878365157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347545543/10000000000 : ℝ)|^4659 ≤ (44830551265603/100000000000000 : ℝ)^3635
        have hw : |(5347545543/10000000000 : ℝ)|=(5347545543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234392903/1250000000 : ℝ)|^4659 ≤ (11701570356433/100000000000000 : ℝ)^3635
        have hw : |(-234392903/1250000000 : ℝ)|=(234392903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220297767/10000000000 : ℝ)|^4659 ≤ (43467878365157/100000000000000 : ℝ)^3635
        have hw : |(5220297767/10000000000 : ℝ)|=(5220297767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s4_2 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347545853/10000000000 : ℝ)*x 0 + (652537167/1250000000 : ℝ)*x 1 + (-937571691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347545853/10000000000 : ℝ)^4659 ≤ (11207638649141/25000000000000 : ℝ)^3635 := by
    have hnat : (5347545853 : ℕ)^4659*25000000000000^3635 ≤ 11207638649141^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347545853 10000000000 11207638649141 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652537167/1250000000 : ℝ)^4659 ≤ (43467873765359/100000000000000 : ℝ)^3635 := by
    have hnat : (652537167 : ℕ)^4659*100000000000000^3635 ≤ 43467873765359^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652537167 1250000000 43467873765359 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937571691/5000000000 : ℝ)^4659 ≤ (2340314324033/20000000000000 : ℝ)^3635 := by
    have hnat : (937571691 : ℕ)^4659*20000000000000^3635 ≤ 2340314324033^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937571691 5000000000 2340314324033 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347545853/10000000000 : ℝ), (652537167/1250000000 : ℝ), (-937571691/5000000000 : ℝ)] ![(11207638649141/25000000000000 : ℝ), (43467873765359/100000000000000 : ℝ), (2340314324033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347545853/10000000000 : ℝ)|^4659 ≤ (11207638649141/25000000000000 : ℝ)^3635
        have hw : |(5347545853/10000000000 : ℝ)|=(5347545853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652537167/1250000000 : ℝ)|^4659 ≤ (43467873765359/100000000000000 : ℝ)^3635
        have hw : |(652537167/1250000000 : ℝ)|=(652537167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-937571691/5000000000 : ℝ)|^4659 ≤ (2340314324033/20000000000000 : ℝ)^3635
        have hw : |(-937571691/5000000000 : ℝ)|=(937571691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s4_3 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238674397/10000000000 : ℝ)*x 0 + (2000698223/5000000000 : ℝ)*x 1 + (56089041/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238674397/10000000000 : ℝ)^4659 ≤ (16641354246191/50000000000000 : ℝ)^3635 := by
    have hnat : (4238674397 : ℕ)^4659*50000000000000^3635 ≤ 16641354246191^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238674397 10000000000 16641354246191 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000698223/5000000000 : ℝ)^4659 ≤ (30913796332383/100000000000000 : ℝ)^3635 := by
    have hnat : (2000698223 : ℕ)^4659*100000000000000^3635 ≤ 30913796332383^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000698223 5000000000 30913796332383 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56089041/125000000 : ℝ)^4659 ≤ (17901747581631/50000000000000 : ℝ)^3635 := by
    have hnat : (56089041 : ℕ)^4659*50000000000000^3635 ≤ 17901747581631^3635*125000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56089041 125000000 17901747581631 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238674397/10000000000 : ℝ), (2000698223/5000000000 : ℝ), (56089041/125000000 : ℝ)] ![(16641354246191/50000000000000 : ℝ), (30913796332383/100000000000000 : ℝ), (17901747581631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238674397/10000000000 : ℝ)|^4659 ≤ (16641354246191/50000000000000 : ℝ)^3635
        have hw : |(4238674397/10000000000 : ℝ)|=(4238674397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2000698223/5000000000 : ℝ)|^4659 ≤ (30913796332383/100000000000000 : ℝ)^3635
        have hw : |(2000698223/5000000000 : ℝ)|=(2000698223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56089041/125000000 : ℝ)|^4659 ≤ (17901747581631/50000000000000 : ℝ)^3635
        have hw : |(56089041/125000000 : ℝ)|=(56089041/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s4_4 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-442675753/2500000000 : ℝ)*x 0 + (5221365003/10000000000 : ℝ)*x 1 + (542345837/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442675753/2500000000 : ℝ)^4659 ≤ (434914741323/4000000000000 : ℝ)^3635 := by
    have hnat : (442675753 : ℕ)^4659*4000000000000^3635 ≤ 434914741323^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442675753 2500000000 434914741323 4000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221365003/10000000000 : ℝ)^4659 ≤ (21739634323021/50000000000000 : ℝ)^3635 := by
    have hnat : (5221365003 : ℕ)^4659*50000000000000^3635 ≤ 21739634323021^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221365003 10000000000 21739634323021 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542345837/1000000000 : ℝ)^4659 ≤ (9129572562257/20000000000000 : ℝ)^3635 := by
    have hnat : (542345837 : ℕ)^4659*20000000000000^3635 ≤ 9129572562257^3635*1000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542345837 1000000000 9129572562257 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442675753/2500000000 : ℝ), (5221365003/10000000000 : ℝ), (542345837/1000000000 : ℝ)] ![(434914741323/4000000000000 : ℝ), (21739634323021/50000000000000 : ℝ), (9129572562257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442675753/2500000000 : ℝ)|^4659 ≤ (434914741323/4000000000000 : ℝ)^3635
        have hw : |(-442675753/2500000000 : ℝ)|=(442675753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221365003/10000000000 : ℝ)|^4659 ≤ (21739634323021/50000000000000 : ℝ)^3635
        have hw : |(5221365003/10000000000 : ℝ)|=(5221365003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542345837/1000000000 : ℝ)|^4659 ≤ (9129572562257/20000000000000 : ℝ)^3635
        have hw : |(542345837/1000000000 : ℝ)|=(542345837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s4_5 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646721269/5000000000 : ℝ)*x 0 + (-1671982031/10000000000 : ℝ)*x 1 + (5423458037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646721269/5000000000 : ℝ)^4659 ≤ (553125537197/1250000000000 : ℝ)^3635 := by
    have hnat : (2646721269 : ℕ)^4659*1250000000000^3635 ≤ 553125537197^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646721269 5000000000 553125537197 1250000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1671982031/10000000000 : ℝ)^4659 ≤ (10102097792911/100000000000000 : ℝ)^3635 := by
    have hnat : (1671982031 : ℕ)^4659*100000000000000^3635 ≤ 10102097792911^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1671982031 10000000000 10102097792911 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423458037/10000000000 : ℝ)^4659 ≤ (45647859218951/100000000000000 : ℝ)^3635 := by
    have hnat : (5423458037 : ℕ)^4659*100000000000000^3635 ≤ 45647859218951^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423458037 10000000000 45647859218951 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646721269/5000000000 : ℝ), (-1671982031/10000000000 : ℝ), (5423458037/10000000000 : ℝ)] ![(553125537197/1250000000000 : ℝ), (10102097792911/100000000000000 : ℝ), (45647859218951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646721269/5000000000 : ℝ)|^4659 ≤ (553125537197/1250000000000 : ℝ)^3635
        have hw : |(2646721269/5000000000 : ℝ)|=(2646721269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1671982031/10000000000 : ℝ)|^4659 ≤ (10102097792911/100000000000000 : ℝ)^3635
        have hw : |(-1671982031/10000000000 : ℝ)|=(1671982031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423458037/10000000000 : ℝ)|^4659 ≤ (45647859218951/100000000000000 : ℝ)^3635
        have hw : |(5423458037/10000000000 : ℝ)|=(5423458037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s4_6 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323360527/2500000000 : ℝ)*x 0 + (5423458163/10000000000 : ℝ)*x 1 + (-33439649/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323360527/2500000000 : ℝ)^4659 ≤ (44250038368611/100000000000000 : ℝ)^3635 := by
    have hnat : (1323360527 : ℕ)^4659*100000000000000^3635 ≤ 44250038368611^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323360527 2500000000 44250038368611 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423458163/10000000000 : ℝ)^4659 ≤ (45647860578213/100000000000000 : ℝ)^3635 := by
    have hnat : (5423458163 : ℕ)^4659*100000000000000^3635 ≤ 45647860578213^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423458163 10000000000 45647860578213 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33439649/200000000 : ℝ)^4659 ≤ (2525525259417/25000000000000 : ℝ)^3635 := by
    have hnat : (33439649 : ℕ)^4659*25000000000000^3635 ≤ 2525525259417^3635*200000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33439649 200000000 2525525259417 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323360527/2500000000 : ℝ), (5423458163/10000000000 : ℝ), (-33439649/200000000 : ℝ)] ![(44250038368611/100000000000000 : ℝ), (45647860578213/100000000000000 : ℝ), (2525525259417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323360527/2500000000 : ℝ)|^4659 ≤ (44250038368611/100000000000000 : ℝ)^3635
        have hw : |(1323360527/2500000000 : ℝ)|=(1323360527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423458163/10000000000 : ℝ)|^4659 ≤ (45647860578213/100000000000000 : ℝ)^3635
        have hw : |(5423458163/10000000000 : ℝ)|=(5423458163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33439649/200000000 : ℝ)|^4659 ≤ (2525525259417/25000000000000 : ℝ)^3635
        have hw : |(-33439649/200000000 : ℝ)|=(33439649/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s4_7 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33909897/80000000 : ℝ)*x 0 + (2242292229/5000000000 : ℝ)*x 1 + (80079087/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33909897/80000000 : ℝ)^4659 ≤ (33283339797407/100000000000000 : ℝ)^3635 := by
    have hnat : (33909897 : ℕ)^4659*100000000000000^3635 ≤ 33283339797407^3635*80000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33909897 80000000 33283339797407 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242292229/5000000000 : ℝ)^4659 ≤ (17888766425937/50000000000000 : ℝ)^3635 := by
    have hnat : (2242292229 : ℕ)^4659*50000000000000^3635 ≤ 17888766425937^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242292229 5000000000 17888766425937 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80079087/200000000 : ℝ)^4659 ≤ (966847729241/3125000000000 : ℝ)^3635 := by
    have hnat : (80079087 : ℕ)^4659*3125000000000^3635 ≤ 966847729241^3635*200000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80079087 200000000 966847729241 3125000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33909897/80000000 : ℝ), (2242292229/5000000000 : ℝ), (80079087/200000000 : ℝ)] ![(33283339797407/100000000000000 : ℝ), (17888766425937/50000000000000 : ℝ), (966847729241/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33909897/80000000 : ℝ)|^4659 ≤ (33283339797407/100000000000000 : ℝ)^3635
        have hw : |(33909897/80000000 : ℝ)|=(33909897/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242292229/5000000000 : ℝ)|^4659 ≤ (17888766425937/50000000000000 : ℝ)^3635
        have hw : |(2242292229/5000000000 : ℝ)|=(2242292229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80079087/200000000 : ℝ)|^4659 ≤ (966847729241/3125000000000 : ℝ)^3635
        have hw : |(80079087/200000000 : ℝ)|=(80079087/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1581_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7757/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5577/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15487/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7757/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1391/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7757/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1391/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7757/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1391/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7757/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1391/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7757/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1391/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7757/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1391/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1391/12500 : ℝ) ^ (4657/1024 : ℝ) ≤ (4605179847529873/100000000000000000000 : ℝ) := by
    have hpowers : (1391/12500 : ℝ)^4657 ≤ (4605179847529873/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1391 : ℕ)^4657*100000000000000000000^1024 ≤ 4605179847529873^1024*12500^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1391 12500 4605179847529873 100000000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1391/12500 : ℝ)) (X := (4605179847529873/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7757/50000 : ℝ) ^ (4657/1024 : ℝ) ≤ (20870454683614711/100000000000000000000 : ℝ) := by
    have hpowers : (7757/50000 : ℝ)^4657 ≤ (20870454683614711/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7757 : ℕ)^4657*100000000000000000000^1024 ≤ 20870454683614711^1024*50000^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7757 50000 20870454683614711 100000000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7757/50000 : ℝ)) (X := (20870454683614711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004605179847529873/50000000000000000000 : ℝ) ≤ (2500050628459931/2500000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (50004605179847529873/50000000000000000000 : ℝ)^1024 ≤ (2500050628459931/2500000000000000 : ℝ)^4657 := by
      have hnat : (50004605179847529873 : ℕ)^1024*2500000000000000^4657 ≤ 2500050628459931^4657*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004605179847529873 50000000000000000000 2500050628459931 2500000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500050628459931/2500000000000000 : ℝ)) (X := (50004605179847529873/50000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503184454316393073/12500000000000000000 : ℝ) ≤ (1250070014112863/1250000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (12503184454316393073/12500000000000000000 : ℝ)^1024 ≤ (1250070014112863/1250000000000000 : ℝ)^4657 := by
      have hnat : (12503184454316393073 : ℕ)^1024*1250000000000000^4657 ≤ 1250070014112863^4657*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503184454316393073 12500000000000000000 1250070014112863 1250000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250070014112863/1250000000000000 : ℝ)) (X := (12503184454316393073/12500000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020870454683614711/50000000000000000000 : ℝ) ≤ (2500229427991521/2500000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (50020870454683614711/50000000000000000000 : ℝ)^1024 ≤ (2500229427991521/2500000000000000 : ℝ)^4657 := by
      have hnat : (50020870454683614711 : ℕ)^1024*2500000000000000^4657 ≤ 2500229427991521^4657*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020870454683614711 50000000000000000000 2500229427991521 2500000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500229427991521/2500000000000000 : ℝ)) (X := (50020870454683614711/50000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4605179847529873/100000000000000000000 : ℝ) ≤ ((5481616187618861923/5482500000000000000 : ℝ)+2*(17879953159/21930000000000 : ℝ)*(1391/12500 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (5481616187618861923/5482500000000000000 : ℝ)+2*(17879953159/21930000000000 : ℝ)*(1391/12500 : ℝ)=(2500050628459931/2500000000000000 : ℝ) by norm_num, show 1+2*(4605179847529873/100000000000000000000 : ℝ)=(50004605179847529873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20870454683614711/100000000000000000000 : ℝ)+(4605179847529873/100000000000000000000 : ℝ) ≤ ((5481616187618861923/5482500000000000000 : ℝ)+(17879953159/21930000000000 : ℝ)*((7757/50000 : ℝ)+(1391/12500 : ℝ)))^(4657/1024 : ℝ) := by
    rw [show (5481616187618861923/5482500000000000000 : ℝ)+(17879953159/21930000000000 : ℝ)*((7757/50000 : ℝ)+(1391/12500 : ℝ))=(1250070014112863/1250000000000000 : ℝ) by norm_num, show 1+(20870454683614711/100000000000000000000 : ℝ)+(4605179847529873/100000000000000000000 : ℝ)=(12503184454316393073/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20870454683614711/100000000000000000000 : ℝ) ≤ ((5481616187618861923/5482500000000000000 : ℝ)+2*(17879953159/21930000000000 : ℝ)*(7757/50000 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (5481616187618861923/5482500000000000000 : ℝ)+2*(17879953159/21930000000000 : ℝ)*(7757/50000 : ℝ)=(2500229427991521/2500000000000000 : ℝ) by norm_num, show 1+2*(20870454683614711/100000000000000000000 : ℝ)=(50020870454683614711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5481616187618861923/5482500000000000000 : ℝ)*(X 1 0+X 2 0)+(17879953159/21930000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (7757/50000 : ℝ)) (c := (5481616187618861923/5482500000000000000 : ℝ)) (alpha := (17879953159/21930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5481616187618861923/5482500000000000000 : ℝ)*(X 0 1+X 2 1)+(17879953159/21930000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (7757/50000 : ℝ)) (c := (5481616187618861923/5482500000000000000 : ℝ)) (alpha := (17879953159/21930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5481616187618861923/5482500000000000000 : ℝ)*(X 0 2+X 1 2)+(17879953159/21930000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (7757/50000 : ℝ)) (c := (5481616187618861923/5482500000000000000 : ℝ)) (alpha := (17879953159/21930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1770676123/10000000000 : ℝ)*X 0 0+(2712266633/5000000000 : ℝ)*X 0 1+(652537289/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347545543/10000000000 : ℝ)*X 1 0+(-234392903/1250000000 : ℝ)*X 1 1+(5220297767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347545853/10000000000 : ℝ)*X 2 0+(652537167/1250000000 : ℝ)*X 2 1+(-937571691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4238674397/10000000000 : ℝ)*X 0 0+(2000698223/5000000000 : ℝ)*X 0 1+(56089041/125000000 : ℝ)*X 0 2+(4238674397/10000000000 : ℝ)*X 1 0+(2000698223/5000000000 : ℝ)*X 1 1+(56089041/125000000 : ℝ)*X 1 2+(4238674397/10000000000 : ℝ)*X 2 0+(2000698223/5000000000 : ℝ)*X 2 1+(56089041/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-442675753/2500000000 : ℝ)*X 0 0+(5221365003/10000000000 : ℝ)*X 0 1+(542345837/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646721269/5000000000 : ℝ)*X 1 0+(-1671982031/10000000000 : ℝ)*X 1 1+(5423458037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323360527/2500000000 : ℝ)*X 2 0+(5423458163/10000000000 : ℝ)*X 2 1+(-33439649/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33909897/80000000 : ℝ)*X 0 0+(2242292229/5000000000 : ℝ)*X 0 1+(80079087/200000000 : ℝ)*X 0 2+(33909897/80000000 : ℝ)*X 1 0+(2242292229/5000000000 : ℝ)*X 1 1+(80079087/200000000 : ℝ)*X 1 2+(33909897/80000000 : ℝ)*X 2 0+(2242292229/5000000000 : ℝ)*X 2 1+(80079087/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (255209621217429659459792563/45687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266390009/50000000000000 : ℝ)*(base19) + (23343777/5000000000000 : ℝ)*(base23) + (1877337/1562500000000 : ℝ)*(lower2) + (217055793/100000000000000 : ℝ)*(upper5) + (1738772334392227/50000000000000 : ℝ)*(major0) + (1738772334392227/50000000000000 : ℝ)*(major1) + (1738772334392227/50000000000000 : ℝ)*(major2) + (2448155655669697/50000000000000 : ℝ)*(sp0) + (4896310178246019/100000000000000 : ℝ)*(sp1) + (2448148941473243/50000000000000 : ℝ)*(sp2) + (2058774646897983/100000000000000 : ℝ)*(sp3) + (300156679/50000000000000 : ℝ)*(sp5) + (1620189671/12500000000000 : ℝ)*(sp6) + (127725283/4000000000000 : ℝ)*(sp7) + (1029388920015029/50000000000000 : ℝ)*(f.failure) + (2448155655669697/50000000000000 : ℝ)*(f.sum) + (27357170341/27412500000000000000000000 : ℝ)*base66 + (24799579994506453/6375000000000000000000000000000 : ℝ)*base68 + (48995789512756453/6375000000000000000000000000000 : ℝ)*base70 + (38473011335131453/6375000000000000000000000000000 : ℝ)*base72 + (993821801347/219300000000000000000000000 : ℝ)*base73 + (88320581942881453/6375000000000000000000000000000 : ℝ)*base76 + (39410062264006453/6375000000000000000000000000000 : ℝ)*base78 + (20164671154006453/6375000000000000000000000000000 : ℝ)*base80 + (367457615281/1096500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (14393769/5000000000000000000000 : ℝ)*base89 + (14393769/5000000000000000000000 : ℝ)*base91 + (14393769/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (957438681126735535068098023/91375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (668277549/25000000000000 : ℝ)*(base19) + (1173643571/50000000000000 : ℝ)*(base23) + (104125891/100000000000000 : ℝ)*(upper2) + (107018049/50000000000000 : ℝ)*(upper3) + (349712773/100000000000000 : ℝ)*(upper5) + (3514403106194299/100000000000000 : ℝ)*(major0) + (3514403106194299/100000000000000 : ℝ)*(major1) + (3514403106194299/100000000000000 : ℝ)*(major2) + (20785282101/50000000000000 : ℝ)*(sp1) + (29773095289/100000000000000 : ℝ)*(sp2) + (2474103535707451/50000000000000 : ℝ)*(sp4) + (618520353467563/12500000000000 : ℝ)*(sp5) + (618521868879059/12500000000000 : ℝ)*(sp6) + (41611975834057/2000000000000 : ℝ)*(sp7) + (41611975834057/2000000000000 : ℝ)*(f.failure) + (2474103535707451/50000000000000 : ℝ)*(f.sum) + (785926238267/274125000000000000000000000 : ℝ)*base66 + (17067506091547139/12750000000000000000000000000000 : ℝ)*base67 + (11940128858047139/12750000000000000000000000000000 : ℝ)*base69 + (154286358296047139/12750000000000000000000000000000 : ℝ)*base71 + (5356368489761/1096500000000000000000000000 : ℝ)*base74 + (8527928627452861/12750000000000000000000000000000 : ℝ)*base76 + (22625948444797139/12750000000000000000000000000000 : ℝ)*base77 + (61878509166952861/12750000000000000000000000000000 : ℝ)*base80 + (797083271851/548250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2081523/200000000000000000000 : ℝ)*base90 + (2081523/200000000000000000000 : ℝ)*base92 + (2081523/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1581_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7757/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1581_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1581_s5_0 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1770693733/10000000000 : ℝ)*x 0 + (2712203053/5000000000 : ℝ)*x 1 + (1305103467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1770693733/10000000000 : ℝ)^4659 ≤ (5436397752693/50000000000000 : ℝ)^3635 := by
    have hnat : (1770693733 : ℕ)^4659*50000000000000^3635 ≤ 5436397752693^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770693733 10000000000 5436397752693 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712203053/5000000000 : ℝ)^4659 ≤ (9131617407737/20000000000000 : ℝ)^3635 := by
    have hnat : (2712203053 : ℕ)^4659*20000000000000^3635 ≤ 9131617407737^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712203053 5000000000 9131617407737 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305103467/2500000000 : ℝ)^4659 ≤ (10867279360887/25000000000000 : ℝ)^3635 := by
    have hnat : (1305103467 : ℕ)^4659*25000000000000^3635 ≤ 10867279360887^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305103467 2500000000 10867279360887 25000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1770693733/10000000000 : ℝ), (2712203053/5000000000 : ℝ), (1305103467/2500000000 : ℝ)] ![(5436397752693/50000000000000 : ℝ), (9131617407737/20000000000000 : ℝ), (10867279360887/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1770693733/10000000000 : ℝ)|^4659 ≤ (5436397752693/50000000000000 : ℝ)^3635
        have hw : |(-1770693733/10000000000 : ℝ)|=(1770693733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712203053/5000000000 : ℝ)|^4659 ≤ (9131617407737/20000000000000 : ℝ)^3635
        have hw : |(2712203053/5000000000 : ℝ)|=(2712203053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305103467/2500000000 : ℝ)|^4659 ≤ (10867279360887/25000000000000 : ℝ)^3635
        have hw : |(1305103467/2500000000 : ℝ)|=(1305103467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s5_1 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347512359/10000000000 : ℝ)*x 0 + (-234379107/1250000000 : ℝ)*x 1 + (522041389/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347512359/10000000000 : ℝ)^4659 ≤ (22415097351317/50000000000000 : ℝ)^3635 := by
    have hnat : (5347512359 : ℕ)^4659*50000000000000^3635 ≤ 22415097351317^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347512359 10000000000 22415097351317 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234379107/1250000000 : ℝ)^4659 ≤ (11700687606749/100000000000000 : ℝ)^3635 := by
    have hnat : (234379107 : ℕ)^4659*100000000000000^3635 ≤ 11700687606749^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234379107 1250000000 11700687606749 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522041389/1000000000 : ℝ)^4659 ≤ (21734558839171/50000000000000 : ℝ)^3635 := by
    have hnat : (522041389 : ℕ)^4659*50000000000000^3635 ≤ 21734558839171^3635*1000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522041389 1000000000 21734558839171 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347512359/10000000000 : ℝ), (-234379107/1250000000 : ℝ), (522041389/1000000000 : ℝ)] ![(22415097351317/50000000000000 : ℝ), (11700687606749/100000000000000 : ℝ), (21734558839171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347512359/10000000000 : ℝ)|^4659 ≤ (22415097351317/50000000000000 : ℝ)^3635
        have hw : |(5347512359/10000000000 : ℝ)|=(5347512359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234379107/1250000000 : ℝ)|^4659 ≤ (11700687606749/100000000000000 : ℝ)^3635
        have hw : |(-234379107/1250000000 : ℝ)|=(234379107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522041389/1000000000 : ℝ)|^4659 ≤ (21734558839171/50000000000000 : ℝ)^3635
        have hw : |(522041389/1000000000 : ℝ)|=(522041389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s5_2 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668439043/1250000000 : ℝ)*x 0 + (1305103477/2500000000 : ℝ)*x 1 + (-1875032851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668439043/1250000000 : ℝ)^4659 ≤ (44830194541459/100000000000000 : ℝ)^3635 := by
    have hnat : (668439043 : ℕ)^4659*100000000000000^3635 ≤ 44830194541459^3635*1250000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668439043 1250000000 44830194541459 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305103477/2500000000 : ℝ)^4659 ≤ (43469117870447/100000000000000 : ℝ)^3635 := by
    have hnat : (1305103477 : ℕ)^4659*100000000000000^3635 ≤ 43469117870447^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305103477 2500000000 43469117870447 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1875032851/10000000000 : ℝ)^4659 ≤ (5850343783379/50000000000000 : ℝ)^3635 := by
    have hnat : (1875032851 : ℕ)^4659*50000000000000^3635 ≤ 5850343783379^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875032851 10000000000 5850343783379 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668439043/1250000000 : ℝ), (1305103477/2500000000 : ℝ), (-1875032851/10000000000 : ℝ)] ![(44830194541459/100000000000000 : ℝ), (43469117870447/100000000000000 : ℝ), (5850343783379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668439043/1250000000 : ℝ)|^4659 ≤ (44830194541459/100000000000000 : ℝ)^3635
        have hw : |(668439043/1250000000 : ℝ)|=(668439043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305103477/2500000000 : ℝ)|^4659 ≤ (43469117870447/100000000000000 : ℝ)^3635
        have hw : |(1305103477/2500000000 : ℝ)|=(1305103477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1875032851/10000000000 : ℝ)|^4659 ≤ (5850343783379/50000000000000 : ℝ)^3635
        have hw : |(-1875032851/10000000000 : ℝ)|=(1875032851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s5_3 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238686213/10000000000 : ℝ)*x 0 + (4001685321/10000000000 : ℝ)*x 1 + (897366389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238686213/10000000000 : ℝ)^4659 ≤ (3328282741037/10000000000000 : ℝ)^3635 := by
    have hnat : (4238686213 : ℕ)^4659*10000000000000^3635 ≤ 3328282741037^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238686213 10000000000 3328282741037 10000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4001685321/10000000000 : ℝ)^4659 ≤ (241536381579/781250000000 : ℝ)^3635 := by
    have hnat : (4001685321 : ℕ)^4659*781250000000^3635 ≤ 241536381579^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001685321 10000000000 241536381579 781250000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897366389/2000000000 : ℝ)^4659 ≤ (35800515724873/100000000000000 : ℝ)^3635 := by
    have hnat : (897366389 : ℕ)^4659*100000000000000^3635 ≤ 35800515724873^3635*2000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897366389 2000000000 35800515724873 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238686213/10000000000 : ℝ), (4001685321/10000000000 : ℝ), (897366389/2000000000 : ℝ)] ![(3328282741037/10000000000000 : ℝ), (241536381579/781250000000 : ℝ), (35800515724873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238686213/10000000000 : ℝ)|^4659 ≤ (3328282741037/10000000000000 : ℝ)^3635
        have hw : |(4238686213/10000000000 : ℝ)|=(4238686213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4001685321/10000000000 : ℝ)|^4659 ≤ (241536381579/781250000000 : ℝ)^3635
        have hw : |(4001685321/10000000000 : ℝ)|=(4001685321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897366389/2000000000 : ℝ)|^4659 ≤ (35800515724873/100000000000000 : ℝ)^3635
        have hw : |(897366389/2000000000 : ℝ)|=(897366389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s5_4 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-110670007/625000000 : ℝ)*x 0 + (1305369747/2500000000 : ℝ)*x 1 + (5423333121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110670007/625000000 : ℝ)^4659 ≤ (10873003113969/100000000000000 : ℝ)^3635 := by
    have hnat : (110670007 : ℕ)^4659*100000000000000^3635 ≤ 10873003113969^3635*625000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110670007 625000000 10873003113969 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305369747/2500000000 : ℝ)^4659 ≤ (21740242605791/50000000000000 : ℝ)^3635 := by
    have hnat : (1305369747 : ℕ)^4659*50000000000000^3635 ≤ 21740242605791^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305369747 2500000000 21740242605791 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423333121/10000000000 : ℝ)^4659 ≤ (45646511655927/100000000000000 : ℝ)^3635 := by
    have hnat : (5423333121 : ℕ)^4659*100000000000000^3635 ≤ 45646511655927^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423333121 10000000000 45646511655927 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110670007/625000000 : ℝ), (1305369747/2500000000 : ℝ), (5423333121/10000000000 : ℝ)] ![(10873003113969/100000000000000 : ℝ), (21740242605791/50000000000000 : ℝ), (45646511655927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110670007/625000000 : ℝ)|^4659 ≤ (10873003113969/100000000000000 : ℝ)^3635
        have hw : |(-110670007/625000000 : ℝ)|=(110670007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305369747/2500000000 : ℝ)|^4659 ≤ (21740242605791/50000000000000 : ℝ)^3635
        have hw : |(1305369747/2500000000 : ℝ)|=(1305369747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423333121/10000000000 : ℝ)|^4659 ≤ (45646511655927/100000000000000 : ℝ)^3635
        have hw : |(5423333121/10000000000 : ℝ)|=(5423333121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s5_5 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529347317/1000000000 : ℝ)*x 0 + (-836056823/5000000000 : ℝ)*x 1 + (1355833283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529347317/1000000000 : ℝ)^4659 ≤ (8850074235291/20000000000000 : ℝ)^3635 := by
    have hnat : (529347317 : ℕ)^4659*20000000000000^3635 ≤ 8850074235291^3635*1000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529347317 1000000000 8850074235291 20000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (836056823/5000000000 : ℝ)^4659 ≤ (10103117037609/100000000000000 : ℝ)^3635 := by
    have hnat : (836056823 : ℕ)^4659*100000000000000^3635 ≤ 10103117037609^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836056823 5000000000 10103117037609 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355833283/2500000000 : ℝ)^4659 ≤ (45646511774591/100000000000000 : ℝ)^3635 := by
    have hnat : (1355833283 : ℕ)^4659*100000000000000^3635 ≤ 45646511774591^3635*2500000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355833283 2500000000 45646511774591 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529347317/1000000000 : ℝ), (-836056823/5000000000 : ℝ), (1355833283/2500000000 : ℝ)] ![(8850074235291/20000000000000 : ℝ), (10103117037609/100000000000000 : ℝ), (45646511774591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529347317/1000000000 : ℝ)|^4659 ≤ (8850074235291/20000000000000 : ℝ)^3635
        have hw : |(529347317/1000000000 : ℝ)|=(529347317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-836056823/5000000000 : ℝ)|^4659 ≤ (10103117037609/100000000000000 : ℝ)^3635
        have hw : |(-836056823/5000000000 : ℝ)|=(836056823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355833283/2500000000 : ℝ)|^4659 ≤ (45646511774591/100000000000000 : ℝ)^3635
        have hw : |(1355833283/2500000000 : ℝ)|=(1355833283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s5_6 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646736591/5000000000 : ℝ)*x 0 + (5423333123/10000000000 : ℝ)*x 1 + (-1672113641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646736591/5000000000 : ℝ)^4659 ≤ (44250371305027/100000000000000 : ℝ)^3635 := by
    have hnat : (2646736591 : ℕ)^4659*100000000000000^3635 ≤ 44250371305027^3635*5000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646736591 5000000000 44250371305027 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423333123/10000000000 : ℝ)^4659 ≤ (22823255838751/50000000000000 : ℝ)^3635 := by
    have hnat : (5423333123 : ℕ)^4659*50000000000000^3635 ≤ 22823255838751^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423333123 10000000000 22823255838751 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1672113641/10000000000 : ℝ)^4659 ≤ (1262889624861/12500000000000 : ℝ)^3635 := by
    have hnat : (1672113641 : ℕ)^4659*12500000000000^3635 ≤ 1262889624861^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1672113641 10000000000 1262889624861 12500000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646736591/5000000000 : ℝ), (5423333123/10000000000 : ℝ), (-1672113641/10000000000 : ℝ)] ![(44250371305027/100000000000000 : ℝ), (22823255838751/50000000000000 : ℝ), (1262889624861/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646736591/5000000000 : ℝ)|^4659 ≤ (44250371305027/100000000000000 : ℝ)^3635
        have hw : |(2646736591/5000000000 : ℝ)|=(2646736591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423333123/10000000000 : ℝ)|^4659 ≤ (22823255838751/50000000000000 : ℝ)^3635
        have hw : |(5423333123/10000000000 : ℝ)|=(5423333123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1672113641/10000000000 : ℝ)|^4659 ≤ (1262889624861/12500000000000 : ℝ)^3635
        have hw : |(-1672113641/10000000000 : ℝ)|=(1672113641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1581_s5_7 (p : ℝ) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238749/10000000 : ℝ)*x 0 + (4484298961/10000000000 : ℝ)*x 1 + (4004237039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238749/10000000 : ℝ)^4659 ≤ (16641729654839/50000000000000 : ℝ)^3635 := by
    have hnat : (4238749 : ℕ)^4659*50000000000000^3635 ≤ 16641729654839^3635*10000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238749 10000000 16641729654839 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484298961/10000000000 : ℝ)^4659 ≤ (17887306791383/50000000000000 : ℝ)^3635 := by
    have hnat : (4484298961 : ℕ)^4659*50000000000000^3635 ≤ 17887306791383^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484298961 10000000000 17887306791383 50000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4004237039/10000000000 : ℝ)^4659 ≤ (30941927093531/100000000000000 : ℝ)^3635 := by
    have hnat : (4004237039 : ℕ)^4659*100000000000000^3635 ≤ 30941927093531^3635*10000000000^4659 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4004237039 10000000000 30941927093531 100000000000000 4659 3635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4659/1024 : ℝ)) 4659 3635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238749/10000000 : ℝ), (4484298961/10000000000 : ℝ), (4004237039/10000000000 : ℝ)] ![(16641729654839/50000000000000 : ℝ), (17887306791383/50000000000000 : ℝ), (30941927093531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238749/10000000 : ℝ)|^4659 ≤ (16641729654839/50000000000000 : ℝ)^3635
        have hw : |(4238749/10000000 : ℝ)|=(4238749/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484298961/10000000000 : ℝ)|^4659 ≤ (17887306791383/50000000000000 : ℝ)^3635
        have hw : |(4484298961/10000000000 : ℝ)|=(4484298961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4004237039/10000000000 : ℝ)|^4659 ≤ (30941927093531/100000000000000 : ℝ)^3635
        have hw : |(4004237039/10000000000 : ℝ)|=(4004237039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1581_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2789/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5577/50000 : ℝ) ^ (4657/1024 : ℝ) ≤ (145447402633903/3125000000000000000 : ℝ) := by
    have hpowers : (5577/50000 : ℝ)^4657 ≤ (145447402633903/3125000000000000000 : ℝ)^1024 := by
      have hnat : (5577 : ℕ)^4657*3125000000000000000^1024 ≤ 145447402633903^1024*50000^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5577 50000 145447402633903 3125000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5577/50000 : ℝ)) (X := (145447402633903/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15487/100000 : ℝ) ^ (4657/1024 : ℝ) ≤ (5176444008712853/25000000000000000000 : ℝ) := by
    have hpowers : (15487/100000 : ℝ)^4657 ≤ (5176444008712853/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15487 : ℕ)^4657*25000000000000000000^1024 ≤ 5176444008712853^1024*100000^4657 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15487 100000 5176444008712853 25000000000000000000 4657 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15487/100000 : ℝ)) (X := (5176444008712853/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562645447402633903/1562500000000000000 : ℝ) ≤ (1000020467457373/1000000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (1562645447402633903/1562500000000000000 : ℝ)^1024 ≤ (1000020467457373/1000000000000000 : ℝ)^4657 := by
      have hnat : (1562645447402633903 : ℕ)^1024*1000000000000000^4657 ≤ 1000020467457373^4657*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562645447402633903 1562500000000000000 1000020467457373 1000000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000020467457373/1000000000000000 : ℝ)) (X := (1562645447402633903/1562500000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006340023229784077/25000000000000000000 : ℝ) ≤ (200011151456617/200000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (25006340023229784077/25000000000000000000 : ℝ)^1024 ≤ (200011151456617/200000000000000 : ℝ)^4657 := by
      have hnat : (25006340023229784077 : ℕ)^1024*200000000000000^4657 ≤ 200011151456617^4657*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006340023229784077 25000000000000000000 200011151456617 200000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200011151456617/200000000000000 : ℝ)) (X := (25006340023229784077/25000000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505176444008712853/12500000000000000000 : ℝ) ≤ (1000091047108797/1000000000000000 : ℝ) ^ (4657/1024 : ℝ) := by
    have hpowers : (12505176444008712853/12500000000000000000 : ℝ)^1024 ≤ (1000091047108797/1000000000000000 : ℝ)^4657 := by
      have hnat : (12505176444008712853 : ℕ)^1024*1000000000000000^4657 ≤ 1000091047108797^4657*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505176444008712853 12500000000000000000 1000091047108797 1000000000000000 1024 4657 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000091047108797/1000000000000000 : ℝ)) (X := (12505176444008712853/12500000000000000000 : ℝ)) (by norm_num) 4657 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(145447402633903/3125000000000000000 : ℝ) ≤ ((4332301440060813913/4333000000000000000 : ℝ)+2*(2205614107/2708125000000 : ℝ)*(5577/50000 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (4332301440060813913/4333000000000000000 : ℝ)+2*(2205614107/2708125000000 : ℝ)*(5577/50000 : ℝ)=(1000020467457373/1000000000000000 : ℝ) by norm_num, show 1+2*(145447402633903/3125000000000000000 : ℝ)=(1562645447402633903/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5176444008712853/25000000000000000000 : ℝ)+(145447402633903/3125000000000000000 : ℝ) ≤ ((4332301440060813913/4333000000000000000 : ℝ)+(2205614107/2708125000000 : ℝ)*((15487/100000 : ℝ)+(5577/50000 : ℝ)))^(4657/1024 : ℝ) := by
    rw [show (4332301440060813913/4333000000000000000 : ℝ)+(2205614107/2708125000000 : ℝ)*((15487/100000 : ℝ)+(5577/50000 : ℝ))=(200011151456617/200000000000000 : ℝ) by norm_num, show 1+(5176444008712853/25000000000000000000 : ℝ)+(145447402633903/3125000000000000000 : ℝ)=(25006340023229784077/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5176444008712853/25000000000000000000 : ℝ) ≤ ((4332301440060813913/4333000000000000000 : ℝ)+2*(2205614107/2708125000000 : ℝ)*(15487/100000 : ℝ))^(4657/1024 : ℝ) := by
    rw [show (4332301440060813913/4333000000000000000 : ℝ)+2*(2205614107/2708125000000 : ℝ)*(15487/100000 : ℝ)=(1000091047108797/1000000000000000 : ℝ) by norm_num, show 1+2*(5176444008712853/25000000000000000000 : ℝ)=(12505176444008712853/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4332301440060813913/4333000000000000000 : ℝ)*(X 1 0+X 2 0)+(2205614107/2708125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (4332301440060813913/4333000000000000000 : ℝ)) (alpha := (2205614107/2708125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4332301440060813913/4333000000000000000 : ℝ)*(X 0 1+X 2 1)+(2205614107/2708125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (4332301440060813913/4333000000000000000 : ℝ)) (alpha := (2205614107/2708125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4332301440060813913/4333000000000000000 : ℝ)*(X 0 2+X 1 2)+(2205614107/2708125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4657/1024 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (4332301440060813913/4333000000000000000 : ℝ)) (alpha := (2205614107/2708125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1770693733/10000000000 : ℝ)*X 0 0+(2712203053/5000000000 : ℝ)*X 0 1+(1305103467/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347512359/10000000000 : ℝ)*X 1 0+(-234379107/1250000000 : ℝ)*X 1 1+(522041389/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668439043/1250000000 : ℝ)*X 2 0+(1305103477/2500000000 : ℝ)*X 2 1+(-1875032851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4238686213/10000000000 : ℝ)*X 0 0+(4001685321/10000000000 : ℝ)*X 0 1+(897366389/2000000000 : ℝ)*X 0 2+(4238686213/10000000000 : ℝ)*X 1 0+(4001685321/10000000000 : ℝ)*X 1 1+(897366389/2000000000 : ℝ)*X 1 2+(4238686213/10000000000 : ℝ)*X 2 0+(4001685321/10000000000 : ℝ)*X 2 1+(897366389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-110670007/625000000 : ℝ)*X 0 0+(1305369747/2500000000 : ℝ)*X 0 1+(5423333121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529347317/1000000000 : ℝ)*X 1 0+(-836056823/5000000000 : ℝ)*X 1 1+(1355833283/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646736591/5000000000 : ℝ)*X 2 0+(5423333123/10000000000 : ℝ)*X 2 1+(-1672113641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4238749/10000000 : ℝ)*X 0 0+(4484298961/10000000000 : ℝ)*X 0 1+(4004237039/10000000000 : ℝ)*X 0 2+(4238749/10000000 : ℝ)*X 1 0+(4484298961/10000000000 : ℝ)*X 1 1+(4004237039/10000000000 : ℝ)*X 1 2+(4238749/10000000 : ℝ)*X 2 0+(4484298961/10000000000 : ℝ)*X 2 1+(4004237039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1581_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75502781249763557665443057/7737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (422295533/25000000000000 : ℝ)*(base19) + (396259753/25000000000000 : ℝ)*(base23) + (48337357/100000000000000 : ℝ)*(lower2) + (236787373/100000000000000 : ℝ)*(upper3) + (174505049/100000000000000 : ℝ)*(upper5) + (3481730936217921/100000000000000 : ℝ)*(major0) + (3481730936217921/100000000000000 : ℝ)*(major1) + (1740865468108961/50000000000000 : ℝ)*(major2) + (490217670121751/10000000000000 : ℝ)*(sp0) + (15319386442777/312500000000 : ℝ)*(sp1) + (61277547072897/1250000000000 : ℝ)*(sp2) + (515310957282593/25000000000000 : ℝ)*(sp3) + (28649653261/100000000000000 : ℝ)*(sp4) + (6183583459/50000000000000 : ℝ)*(sp7) + (206125619629729/10000000000000 : ℝ)*(f.failure) + (1225551337717693/25000000000000 : ℝ)*(f.sum) + (5311836713863/2166500000000000000000000000 : ℝ)*base66 + (3549581158972265127/433300000000000000000000000000000 : ℝ)*base68 + (91986550523575607/216650000000000000000000000000000 : ℝ)*base70 + (7213049230523665127/433300000000000000000000000000000 : ℝ)*base72 + (9018918823097/2166500000000000000000000000 : ℝ)*base74 + (2231583676917925607/216650000000000000000000000000000 : ℝ)*base76 + (4970933229638865127/433300000000000000000000000000000 : ℝ)*base78 + (8066719180005065127/433300000000000000000000000000000 : ℝ)*base80 + (8136547232651/2166500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1990469/1000000000000000000000 : ℝ)*base89 + (1990469/1000000000000000000000 : ℝ)*base91 + (8009531/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117007763841757816171364013/13540625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1340432529/100000000000000 : ℝ)*(base19) + (367872027/25000000000000 : ℝ)*(base23) + (217306453/50000000000000 : ℝ)*(lower1) + (23038483/12500000000000 : ℝ)*(upper3) + (52238211/100000000000000 : ℝ)*(lower4) + (34504849/20000000000000 : ℝ)*(upper5) + (439819087038817/12500000000000 : ℝ)*(major0) + (439819087038817/12500000000000 : ℝ)*(major1) + (439819087038817/12500000000000 : ℝ)*(major2) + (207087769/10000000000000 : ℝ)*(sp2) + (2477024835167259/50000000000000 : ℝ)*(sp4) + (1238512082475497/25000000000000 : ℝ)*(sp5) + (4954046127968719/100000000000000 : ℝ)*(sp6) + (83322217369811/4000000000000 : ℝ)*(sp7) + (83322217369811/4000000000000 : ℝ)*(f.failure) + (2477024835167259/50000000000000 : ℝ)*(f.sum) + (275731268051/541625000000000000000000000 : ℝ)*base66 + (2399899314018026579/54162500000000000000000000000000 : ℝ)*base68 + (228505425799926579/54162500000000000000000000000000 : ℝ)*base70 + (695300900030939079/54162500000000000000000000000000 : ℝ)*base72 + (11538187736727/4333000000000000000000000000 : ℝ)*base74 + (572336113790648421/54162500000000000000000000000000 : ℝ)*base75 + (269742739267364079/54162500000000000000000000000000 : ℝ)*base78 + (365305809288139079/54162500000000000000000000000000 : ℝ)*base80 + (34522962669/67703125000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1001471/400000000000000000000 : ℝ)*base89 + (1001471/400000000000000000000 : ℝ)*base91 + (1001471/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1581_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1581_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1581_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1581_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1581_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1581_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4657/1024 : ℝ) ≤ p) (hpb : p ≤ (4659/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168913061/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1581_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
