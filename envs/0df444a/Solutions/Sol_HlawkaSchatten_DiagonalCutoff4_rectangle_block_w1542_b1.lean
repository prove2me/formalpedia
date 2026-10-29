-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1542_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:08:04.458961+00:00
-- url     : https://prove2.me/submissions/c5260051-a33f-4f61-853b-85954de80ac8

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
theorem support_rectangle_w1542_s3_0 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-182424131/1000000000 : ℝ)*x 0 + (2715839447/5000000000 : ℝ)*x 1 + (5216923681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182424131/1000000000 : ℝ)^4581 ≤ (2794476176091/25000000000000 : ℝ)^3557 := by
    have hnat : (182424131 : ℕ)^4581*25000000000000^3557 ≤ 2794476176091^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182424131 1000000000 2794476176091 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715839447/5000000000 : ℝ)^4581 ≤ (22782223571051/50000000000000 : ℝ)^3557 := by
    have hnat : (2715839447 : ℕ)^4581*50000000000000^3557 ≤ 22782223571051^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715839447 5000000000 22782223571051 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216923681/10000000000 : ℝ)^4581 ≤ (43257648138853/100000000000000 : ℝ)^3557 := by
    have hnat : (5216923681 : ℕ)^4581*100000000000000^3557 ≤ 43257648138853^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216923681 10000000000 43257648138853 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182424131/1000000000 : ℝ), (2715839447/5000000000 : ℝ), (5216923681/10000000000 : ℝ)] ![(2794476176091/25000000000000 : ℝ), (22782223571051/50000000000000 : ℝ), (43257648138853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182424131/1000000000 : ℝ)|^4581 ≤ (2794476176091/25000000000000 : ℝ)^3557
        have hw : |(-182424131/1000000000 : ℝ)|=(182424131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715839447/5000000000 : ℝ)|^4581 ≤ (22782223571051/50000000000000 : ℝ)^3557
        have hw : |(2715839447/5000000000 : ℝ)|=(2715839447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216923681/10000000000 : ℝ)|^4581 ≤ (43257648138853/100000000000000 : ℝ)^3557
        have hw : |(5216923681/10000000000 : ℝ)|=(5216923681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s3_1 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675242563/5000000000 : ℝ)*x 0 + (-1934216951/10000000000 : ℝ)*x 1 + (1304230969/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675242563/5000000000 : ℝ)^4581 ≤ (5586144550513/12500000000000 : ℝ)^3557 := by
    have hnat : (2675242563 : ℕ)^4581*12500000000000^3557 ≤ 5586144550513^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675242563 5000000000 5586144550513 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1934216951/10000000000 : ℝ)^4581 ≤ (12053193349839/100000000000000 : ℝ)^3557 := by
    have hnat : (1934216951 : ℕ)^4581*100000000000000^3557 ≤ 12053193349839^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934216951 10000000000 12053193349839 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304230969/2500000000 : ℝ)^4581 ≤ (4325765022123/10000000000000 : ℝ)^3557 := by
    have hnat : (1304230969 : ℕ)^4581*10000000000000^3557 ≤ 4325765022123^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304230969 2500000000 4325765022123 10000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675242563/5000000000 : ℝ), (-1934216951/10000000000 : ℝ), (1304230969/2500000000 : ℝ)] ![(5586144550513/12500000000000 : ℝ), (12053193349839/100000000000000 : ℝ), (4325765022123/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675242563/5000000000 : ℝ)|^4581 ≤ (5586144550513/12500000000000 : ℝ)^3557
        have hw : |(2675242563/5000000000 : ℝ)|=(2675242563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1934216951/10000000000 : ℝ)|^4581 ≤ (12053193349839/100000000000000 : ℝ)^3557
        have hw : |(-1934216951/10000000000 : ℝ)|=(1934216951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304230969/2500000000 : ℝ)|^4581 ≤ (4325765022123/10000000000000 : ℝ)^3557
        have hw : |(1304230969/2500000000 : ℝ)|=(1304230969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s3_2 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53504849/100000000 : ℝ)*x 0 + (2608462001/5000000000 : ℝ)*x 1 + (-15111071/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53504849/100000000 : ℝ)^4581 ≤ (22344576986527/50000000000000 : ℝ)^3557 := by
    have hnat : (53504849 : ℕ)^4581*50000000000000^3557 ≤ 22344576986527^3557*100000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53504849 100000000 22344576986527 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608462001/5000000000 : ℝ)^4581 ≤ (43257651566767/100000000000000 : ℝ)^3557 := by
    have hnat : (2608462001 : ℕ)^4581*100000000000000^3557 ≤ 43257651566767^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608462001 5000000000 43257651566767 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15111071/78125000 : ℝ)^4581 ≤ (1506649306167/12500000000000 : ℝ)^3557 := by
    have hnat : (15111071 : ℕ)^4581*12500000000000^3557 ≤ 1506649306167^3557*78125000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15111071 78125000 1506649306167 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53504849/100000000 : ℝ), (2608462001/5000000000 : ℝ), (-15111071/78125000 : ℝ)] ![(22344576986527/50000000000000 : ℝ), (43257651566767/100000000000000 : ℝ), (1506649306167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53504849/100000000 : ℝ)|^4581 ≤ (22344576986527/50000000000000 : ℝ)^3557
        have hw : |(53504849/100000000 : ℝ)|=(53504849/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608462001/5000000000 : ℝ)|^4581 ≤ (43257651566767/100000000000000 : ℝ)^3557
        have hw : |(2608462001/5000000000 : ℝ)|=(2608462001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15111071/78125000 : ℝ)|^4581 ≤ (1506649306167/12500000000000 : ℝ)^3557
        have hw : |(-15111071/78125000 : ℝ)|=(15111071/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s3_3 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132993237/312500000 : ℝ)*x 0 + (2006577629/5000000000 : ℝ)*x 1 + (4510443653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132993237/312500000 : ℝ)^4581 ≤ (4159863172109/12500000000000 : ℝ)^3557 := by
    have hnat : (132993237 : ℕ)^4581*12500000000000^3557 ≤ 4159863172109^3557*312500000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132993237 312500000 4159863172109 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006577629/5000000000 : ℝ)^4581 ≤ (7713940783849/25000000000000 : ℝ)^3557 := by
    have hnat : (2006577629 : ℕ)^4581*25000000000000^3557 ≤ 7713940783849^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006577629 5000000000 7713940783849 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510443653/10000000000 : ℝ)^4581 ≤ (8966332868871/25000000000000 : ℝ)^3557 := by
    have hnat : (4510443653 : ℕ)^4581*25000000000000^3557 ≤ 8966332868871^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510443653 10000000000 8966332868871 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132993237/312500000 : ℝ), (2006577629/5000000000 : ℝ), (4510443653/10000000000 : ℝ)] ![(4159863172109/12500000000000 : ℝ), (7713940783849/25000000000000 : ℝ), (8966332868871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132993237/312500000 : ℝ)|^4581 ≤ (4159863172109/12500000000000 : ℝ)^3557
        have hw : |(132993237/312500000 : ℝ)|=(132993237/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2006577629/5000000000 : ℝ)|^4581 ≤ (7713940783849/25000000000000 : ℝ)^3557
        have hw : |(2006577629/5000000000 : ℝ)|=(2006577629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510443653/10000000000 : ℝ)|^4581 ≤ (8966332868871/25000000000000 : ℝ)^3557
        have hw : |(4510443653/10000000000 : ℝ)|=(4510443653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s3_4 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-912135623/5000000000 : ℝ)*x 0 + (1043611753/2000000000 : ℝ)*x 1 + (271526749/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (912135623/5000000000 : ℝ)^4581 ≤ (11178140942137/100000000000000 : ℝ)^3557 := by
    have hnat : (912135623 : ℕ)^4581*100000000000000^3557 ≤ 11178140942137^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912135623 5000000000 11178140942137 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043611753/2000000000 : ℝ)^4581 ≤ (8653953984059/20000000000000 : ℝ)^3557 := by
    have hnat : (1043611753 : ℕ)^4581*20000000000000^3557 ≤ 8653953984059^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043611753 2000000000 8653953984059 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271526749/500000000 : ℝ)^4581 ≤ (911041782579/2000000000000 : ℝ)^3557 := by
    have hnat : (271526749 : ℕ)^4581*2000000000000^3557 ≤ 911041782579^3557*500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271526749 500000000 911041782579 2000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-912135623/5000000000 : ℝ), (1043611753/2000000000 : ℝ), (271526749/500000000 : ℝ)] ![(11178140942137/100000000000000 : ℝ), (8653953984059/20000000000000 : ℝ), (911041782579/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-912135623/5000000000 : ℝ)|^4581 ≤ (11178140942137/100000000000000 : ℝ)^3557
        have hw : |(-912135623/5000000000 : ℝ)|=(912135623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043611753/2000000000 : ℝ)|^4581 ≤ (8653953984059/20000000000000 : ℝ)^3557
        have hw : |(1043611753/2000000000 : ℝ)|=(1043611753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271526749/500000000 : ℝ)|^4581 ≤ (911041782579/2000000000000 : ℝ)^3557
        have hw : |(271526749/500000000 : ℝ)|=(271526749/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s3_5 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293867219/10000000000 : ℝ)*x 0 + (-21507573/125000000 : ℝ)*x 1 + (1357633751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293867219/10000000000 : ℝ)^4581 ≤ (22040527815917/50000000000000 : ℝ)^3557 := by
    have hnat : (5293867219 : ℕ)^4581*50000000000000^3557 ≤ 22040527815917^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293867219 10000000000 22040527815917 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21507573/125000000 : ℝ)^4581 ≤ (10366854964623/100000000000000 : ℝ)^3557 := by
    have hnat : (21507573 : ℕ)^4581*100000000000000^3557 ≤ 10366854964623^3557*125000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21507573 125000000 10366854964623 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357633751/2500000000 : ℝ)^4581 ≤ (45552089388221/100000000000000 : ℝ)^3557 := by
    have hnat : (1357633751 : ℕ)^4581*100000000000000^3557 ≤ 45552089388221^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357633751 2500000000 45552089388221 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293867219/10000000000 : ℝ), (-21507573/125000000 : ℝ), (1357633751/2500000000 : ℝ)] ![(22040527815917/50000000000000 : ℝ), (10366854964623/100000000000000 : ℝ), (45552089388221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293867219/10000000000 : ℝ)|^4581 ≤ (22040527815917/50000000000000 : ℝ)^3557
        have hw : |(5293867219/10000000000 : ℝ)|=(5293867219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21507573/125000000 : ℝ)|^4581 ≤ (10366854964623/100000000000000 : ℝ)^3557
        have hw : |(-21507573/125000000 : ℝ)|=(21507573/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357633751/2500000000 : ℝ)|^4581 ≤ (45552089388221/100000000000000 : ℝ)^3557
        have hw : |(1357633751/2500000000 : ℝ)|=(1357633751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s3_6 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293867569/10000000000 : ℝ)*x 0 + (5430534839/10000000000 : ℝ)*x 1 + (-1720605587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293867569/10000000000 : ℝ)^4581 ≤ (44081059385221/100000000000000 : ℝ)^3557 := by
    have hnat : (5293867569 : ℕ)^4581*100000000000000^3557 ≤ 44081059385221^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293867569 10000000000 44081059385221 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430534839/10000000000 : ℝ)^4581 ≤ (9110417521147/20000000000000 : ℝ)^3557 := by
    have hnat : (5430534839 : ℕ)^4581*20000000000000^3557 ≤ 9110417521147^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430534839 10000000000 9110417521147 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1720605587/10000000000 : ℝ)^4581 ≤ (1295856625179/12500000000000 : ℝ)^3557 := by
    have hnat : (1720605587 : ℕ)^4581*12500000000000^3557 ≤ 1295856625179^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720605587 10000000000 1295856625179 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293867569/10000000000 : ℝ), (5430534839/10000000000 : ℝ), (-1720605587/10000000000 : ℝ)] ![(44081059385221/100000000000000 : ℝ), (9110417521147/20000000000000 : ℝ), (1295856625179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293867569/10000000000 : ℝ)|^4581 ≤ (44081059385221/100000000000000 : ℝ)^3557
        have hw : |(5293867569/10000000000 : ℝ)|=(5293867569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430534839/10000000000 : ℝ)|^4581 ≤ (9110417521147/20000000000000 : ℝ)^3557
        have hw : |(5430534839/10000000000 : ℝ)|=(5430534839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1720605587/10000000000 : ℝ)|^4581 ≤ (1295856625179/12500000000000 : ℝ)^3557
        have hw : |(-1720605587/10000000000 : ℝ)|=(1720605587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s3_7 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4255851771/10000000000 : ℝ)*x 0 + (4507815097/10000000000 : ℝ)*x 1 + (4015803887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255851771/10000000000 : ℝ)^4581 ≤ (2079974504949/6250000000000 : ℝ)^3557 := by
    have hnat : (4255851771 : ℕ)^4581*6250000000000^3557 ≤ 2079974504949^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255851771 10000000000 2079974504949 6250000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507815097/10000000000 : ℝ)^4581 ≤ (35838415333509/100000000000000 : ℝ)^3557 := by
    have hnat : (4507815097 : ℕ)^4581*100000000000000^3557 ≤ 35838415333509^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507815097 10000000000 35838415333509 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4015803887/10000000000 : ℝ)^4581 ≤ (15440996291249/50000000000000 : ℝ)^3557 := by
    have hnat : (4015803887 : ℕ)^4581*50000000000000^3557 ≤ 15440996291249^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015803887 10000000000 15440996291249 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255851771/10000000000 : ℝ), (4507815097/10000000000 : ℝ), (4015803887/10000000000 : ℝ)] ![(2079974504949/6250000000000 : ℝ), (35838415333509/100000000000000 : ℝ), (15440996291249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255851771/10000000000 : ℝ)|^4581 ≤ (2079974504949/6250000000000 : ℝ)^3557
        have hw : |(4255851771/10000000000 : ℝ)|=(4255851771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507815097/10000000000 : ℝ)|^4581 ≤ (35838415333509/100000000000000 : ℝ)^3557
        have hw : |(4507815097/10000000000 : ℝ)|=(4507815097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4015803887/10000000000 : ℝ)|^4581 ≤ (15440996291249/50000000000000 : ℝ)^3557
        have hw : |(4015803887/10000000000 : ℝ)|=(4015803887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1542_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15893/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10651/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5491/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15533/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15893/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10651/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15893/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10651/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15893/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10651/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15893/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10651/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15893/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10651/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15893/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10651/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10651/100000 : ℝ) ^ (4579/1024 : ℝ) ≤ (4475085521252263/100000000000000000000 : ℝ) := by
    have hpowers : (10651/100000 : ℝ)^4579 ≤ (4475085521252263/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10651 : ℕ)^4579*100000000000000000000^1024 ≤ 4475085521252263^1024*100000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10651 100000 4475085521252263 100000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10651/100000 : ℝ)) (X := (4475085521252263/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15893/100000 : ℝ) ^ (4579/1024 : ℝ) ≤ (13397339984369213/50000000000000000000 : ℝ) := by
    have hpowers : (15893/100000 : ℝ)^4579 ≤ (13397339984369213/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15893 : ℕ)^4579*50000000000000000000^1024 ≤ 13397339984369213^1024*100000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15893 100000 13397339984369213 50000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15893/100000 : ℝ)) (X := (13397339984369213/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004475085521252263/50000000000000000000 : ℝ) ≤ (5000100072687743/5000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (50004475085521252263/50000000000000000000 : ℝ)^1024 ≤ (5000100072687743/5000000000000000 : ℝ)^4579 := by
      have hnat : (50004475085521252263 : ℕ)^1024*5000000000000000^4579 ≤ 5000100072687743^4579*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004475085521252263 50000000000000000000 5000100072687743 5000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000100072687743/5000000000000000 : ℝ)) (X := (50004475085521252263/50000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031269765489990689/100000000000000000000 : ℝ) ≤ (5000349599845133/5000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (100031269765489990689/100000000000000000000 : ℝ)^1024 ≤ (5000349599845133/5000000000000000 : ℝ)^4579 := by
      have hnat : (100031269765489990689 : ℕ)^1024*5000000000000000^4579 ≤ 5000349599845133^4579*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031269765489990689 100000000000000000000 5000349599845133 5000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000349599845133/5000000000000000 : ℝ)) (X := (100031269765489990689/100000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013397339984369213/25000000000000000000 : ℝ) ≤ (5000599127002523/5000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (25013397339984369213/25000000000000000000 : ℝ)^1024 ≤ (5000599127002523/5000000000000000 : ℝ)^4579 := by
      have hnat : (25013397339984369213 : ℕ)^1024*5000000000000000^4579 ≤ 5000599127002523^4579*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013397339984369213 25000000000000000000 5000599127002523 5000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000599127002523/5000000000000000 : ℝ)) (X := (25013397339984369213/25000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4475085521252263/100000000000000000000 : ℝ) ≤ ((13102604576761213513/13105000000000000000 : ℝ)+2*(24952715739/26210000000000 : ℝ)*(10651/100000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (13102604576761213513/13105000000000000000 : ℝ)+2*(24952715739/26210000000000 : ℝ)*(10651/100000 : ℝ)=(5000100072687743/5000000000000000 : ℝ) by norm_num, show 1+2*(4475085521252263/100000000000000000000 : ℝ)=(50004475085521252263/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13397339984369213/50000000000000000000 : ℝ)+(4475085521252263/100000000000000000000 : ℝ) ≤ ((13102604576761213513/13105000000000000000 : ℝ)+(24952715739/26210000000000 : ℝ)*((15893/100000 : ℝ)+(10651/100000 : ℝ)))^(4579/1024 : ℝ) := by
    rw [show (13102604576761213513/13105000000000000000 : ℝ)+(24952715739/26210000000000 : ℝ)*((15893/100000 : ℝ)+(10651/100000 : ℝ))=(5000349599845133/5000000000000000 : ℝ) by norm_num, show 1+(13397339984369213/50000000000000000000 : ℝ)+(4475085521252263/100000000000000000000 : ℝ)=(100031269765489990689/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13397339984369213/50000000000000000000 : ℝ) ≤ ((13102604576761213513/13105000000000000000 : ℝ)+2*(24952715739/26210000000000 : ℝ)*(15893/100000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (13102604576761213513/13105000000000000000 : ℝ)+2*(24952715739/26210000000000 : ℝ)*(15893/100000 : ℝ)=(5000599127002523/5000000000000000 : ℝ) by norm_num, show 1+2*(13397339984369213/50000000000000000000 : ℝ)=(25013397339984369213/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13102604576761213513/13105000000000000000 : ℝ)*(X 1 0+X 2 0)+(24952715739/26210000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (10651/100000 : ℝ)) (hi := (15893/100000 : ℝ)) (c := (13102604576761213513/13105000000000000000 : ℝ)) (alpha := (24952715739/26210000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13102604576761213513/13105000000000000000 : ℝ)*(X 0 1+X 2 1)+(24952715739/26210000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (10651/100000 : ℝ)) (hi := (15893/100000 : ℝ)) (c := (13102604576761213513/13105000000000000000 : ℝ)) (alpha := (24952715739/26210000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13102604576761213513/13105000000000000000 : ℝ)*(X 0 2+X 1 2)+(24952715739/26210000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (10651/100000 : ℝ)) (hi := (15893/100000 : ℝ)) (c := (13102604576761213513/13105000000000000000 : ℝ)) (alpha := (24952715739/26210000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-182424131/1000000000 : ℝ)*X 0 0+(2715839447/5000000000 : ℝ)*X 0 1+(5216923681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675242563/5000000000 : ℝ)*X 1 0+(-1934216951/10000000000 : ℝ)*X 1 1+(1304230969/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53504849/100000000 : ℝ)*X 2 0+(2608462001/5000000000 : ℝ)*X 2 1+(-15111071/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((132993237/312500000 : ℝ)*X 0 0+(2006577629/5000000000 : ℝ)*X 0 1+(4510443653/10000000000 : ℝ)*X 0 2+(132993237/312500000 : ℝ)*X 1 0+(2006577629/5000000000 : ℝ)*X 1 1+(4510443653/10000000000 : ℝ)*X 1 2+(132993237/312500000 : ℝ)*X 2 0+(2006577629/5000000000 : ℝ)*X 2 1+(4510443653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-912135623/5000000000 : ℝ)*X 0 0+(1043611753/2000000000 : ℝ)*X 0 1+(271526749/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293867219/10000000000 : ℝ)*X 1 0+(-21507573/125000000 : ℝ)*X 1 1+(1357633751/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293867569/10000000000 : ℝ)*X 2 0+(5430534839/10000000000 : ℝ)*X 2 1+(-1720605587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4255851771/10000000000 : ℝ)*X 0 0+(4507815097/10000000000 : ℝ)*X 0 1+(4015803887/10000000000 : ℝ)*X 0 2+(4255851771/10000000000 : ℝ)*X 1 0+(4507815097/10000000000 : ℝ)*X 1 1+(4015803887/10000000000 : ℝ)*X 1 2+(4255851771/10000000000 : ℝ)*X 2 0+(4507815097/10000000000 : ℝ)*X 2 1+(4015803887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1206875584969559626487689821/163812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (222141377/20000000000000 : ℝ)*(base19) + (98134199/12500000000000 : ℝ)*(base23) + (34496363/50000000000000 : ℝ)*(lower2) + (319706399/100000000000000 : ℝ)*(upper3) + (2491317/4000000000000 : ℝ)*(upper5) + (833427999553261/25000000000000 : ℝ)*(major0) + (833427999553261/25000000000000 : ℝ)*(major1) + (833427999553261/25000000000000 : ℝ)*(major2) + (29103036572953/625000000000 : ℝ)*(sp0) + (2328249447704623/50000000000000 : ℝ)*(sp1) + (4656499221042539/100000000000000 : ℝ)*(sp2) + (1005456642435973/50000000000000 : ℝ)*(sp3) + (3538610913/25000000000000 : ℝ)*(sp4) + (10459857319/100000000000000 : ℝ)*(sp7) + (402184748945853/20000000000000 : ℝ)*(f.failure) + (4656500006116131/100000000000000 : ℝ)*(f.sum) + (74469262791/2621000000000000000000000000 : ℝ)*base65 + (865812282334540893/327625000000000000000000000000000 : ℝ)*base67 + (2208299520667959107/327625000000000000000000000000000 : ℝ)*base70 + (3014446653302290893/327625000000000000000000000000000 : ℝ)*base71 + (9038313260667/2621000000000000000000000000 : ℝ)*base73 + (1330710535040893/327625000000000000000000000000000 : ℝ)*base75 + (796004043479290893/327625000000000000000000000000000 : ℝ)*base77 + (2062589795232709107/327625000000000000000000000000000 : ℝ)*base80 + (9117149193/2621000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (669911/200000000000000000000 : ℝ)*base90 + (669911/200000000000000000000 : ℝ)*base92 + (669911/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222611469183198160834901139/40953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (543517073/50000000000000 : ℝ)*(base19) + (1874944683/100000000000000 : ℝ)*(base23) + (17277769/10000000000000 : ℝ)*(upper2) + (270707183/100000000000000 : ℝ)*(upper3) + (3246697/2000000000000 : ℝ)*(upper5) + (210590011093467/6250000000000 : ℝ)*(major0) + (210590011093467/6250000000000 : ℝ)*(major1) + (210590011093467/6250000000000 : ℝ)*(major2) + (11109188891/100000000000000 : ℝ)*(sp1) + (1006797607/4000000000000 : ℝ)*(sp2) + (941280976818209/20000000000000 : ℝ)*(sp4) + (588299085983501/12500000000000 : ℝ)*(sp5) + (4706377839206187/100000000000000 : ℝ)*(sp6) + (2032475289707803/100000000000000 : ℝ)*(sp7) + (2032475289707803/100000000000000 : ℝ)*(f.failure) + (941280976818209/20000000000000 : ℝ)*(f.sum) + (10203529062087/2621000000000000000000000000 : ℝ)*base66 + (420977105870705429/81906250000000000000000000000000 : ℝ)*base68 + (733074568400236679/81906250000000000000000000000000 : ℝ)*base70 + (453458897999299179/81906250000000000000000000000000 : ℝ)*base72 + (6293600694593/1310500000000000000000000000 : ℝ)*base73 + (458718071937986679/81906250000000000000000000000000 : ℝ)*base76 + (497224838017580429/81906250000000000000000000000000 : ℝ)*base78 + (1244066921276267929/81906250000000000000000000000000 : ℝ)*base80 + (1064300896629/655250000000000000000000000 : ℝ)*base82 + (4335439/1000000000000000000000 : ℝ)*base89 + (4335439/1000000000000000000000 : ℝ)*base91 + (4335439/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1542_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15893/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10651/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15533/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1542_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1542_s4_0 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-456138309/2500000000 : ℝ)*x 0 + (1357402823/2500000000 : ℝ)*x 1 + (5218784713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (456138309/2500000000 : ℝ)^4581 ≤ (1397545787567/12500000000000 : ℝ)^3557 := by
    have hnat : (456138309 : ℕ)^4581*12500000000000^3557 ≤ 1397545787567^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456138309 2500000000 1397545787567 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357402823/2500000000 : ℝ)^4581 ≤ (9108422164771/20000000000000 : ℝ)^3557 := by
    have hnat : (1357402823 : ℕ)^4581*20000000000000^3557 ≤ 9108422164771^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357402823 2500000000 9108422164771 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218784713/10000000000 : ℝ)^4581 ≤ (21638761428661/50000000000000 : ℝ)^3557 := by
    have hnat : (5218784713 : ℕ)^4581*50000000000000^3557 ≤ 21638761428661^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218784713 10000000000 21638761428661 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-456138309/2500000000 : ℝ), (1357402823/2500000000 : ℝ), (5218784713/10000000000 : ℝ)] ![(1397545787567/12500000000000 : ℝ), (9108422164771/20000000000000 : ℝ), (21638761428661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-456138309/2500000000 : ℝ)|^4581 ≤ (1397545787567/12500000000000 : ℝ)^3557
        have hw : |(-456138309/2500000000 : ℝ)|=(456138309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357402823/2500000000 : ℝ)|^4581 ≤ (9108422164771/20000000000000 : ℝ)^3557
        have hw : |(1357402823/2500000000 : ℝ)|=(1357402823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218784713/10000000000 : ℝ)|^4581 ≤ (21638761428661/50000000000000 : ℝ)^3557
        have hw : |(5218784713/10000000000 : ℝ)|=(5218784713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s4_1 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674970131/5000000000 : ℝ)*x 0 + (-1932470617/10000000000 : ℝ)*x 1 + (1304696219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674970131/5000000000 : ℝ)^4581 ≤ (44683295465523/100000000000000 : ℝ)^3557 := by
    have hnat : (2674970131 : ℕ)^4581*100000000000000^3557 ≤ 44683295465523^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674970131 5000000000 44683295465523 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1932470617/10000000000 : ℝ)^4581 ≤ (12039179927279/100000000000000 : ℝ)^3557 := by
    have hnat : (1932470617 : ℕ)^4581*100000000000000^3557 ≤ 12039179927279^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932470617 10000000000 12039179927279 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304696219/2500000000 : ℝ)^4581 ≤ (8655504919631/20000000000000 : ℝ)^3557 := by
    have hnat : (1304696219 : ℕ)^4581*20000000000000^3557 ≤ 8655504919631^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304696219 2500000000 8655504919631 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674970131/5000000000 : ℝ), (-1932470617/10000000000 : ℝ), (1304696219/2500000000 : ℝ)] ![(44683295465523/100000000000000 : ℝ), (12039179927279/100000000000000 : ℝ), (8655504919631/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674970131/5000000000 : ℝ)|^4581 ≤ (44683295465523/100000000000000 : ℝ)^3557
        have hw : |(2674970131/5000000000 : ℝ)|=(2674970131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1932470617/10000000000 : ℝ)|^4581 ≤ (12039179927279/100000000000000 : ℝ)^3557
        have hw : |(-1932470617/10000000000 : ℝ)|=(1932470617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304696219/2500000000 : ℝ)|^4581 ≤ (8655504919631/20000000000000 : ℝ)^3557
        have hw : |(1304696219/2500000000 : ℝ)|=(1304696219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s4_2 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349940367/10000000000 : ℝ)*x 0 + (5218784849/10000000000 : ℝ)*x 1 + (-120779407/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349940367/10000000000 : ℝ)^4581 ≤ (558541207437/1250000000000 : ℝ)^3557 := by
    have hnat : (5349940367 : ℕ)^4581*1250000000000^3557 ≤ 558541207437^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349940367 10000000000 558541207437 1250000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218784849/10000000000 : ℝ)^4581 ≤ (10819381077449/25000000000000 : ℝ)^3557 := by
    have hnat : (5218784849 : ℕ)^4581*25000000000000^3557 ≤ 10819381077449^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218784849 10000000000 10819381077449 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120779407/625000000 : ℝ)^4581 ≤ (6019589542409/50000000000000 : ℝ)^3557 := by
    have hnat : (120779407 : ℕ)^4581*50000000000000^3557 ≤ 6019589542409^3557*625000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120779407 625000000 6019589542409 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349940367/10000000000 : ℝ), (5218784849/10000000000 : ℝ), (-120779407/625000000 : ℝ)] ![(558541207437/1250000000000 : ℝ), (10819381077449/25000000000000 : ℝ), (6019589542409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349940367/10000000000 : ℝ)|^4581 ≤ (558541207437/1250000000000 : ℝ)^3557
        have hw : |(5349940367/10000000000 : ℝ)|=(5349940367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218784849/10000000000 : ℝ)|^4581 ≤ (10819381077449/25000000000000 : ℝ)^3557
        have hw : |(5218784849/10000000000 : ℝ)|=(5218784849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120779407/625000000 : ℝ)|^4581 ≤ (6019589542409/50000000000000 : ℝ)^3557
        have hw : |(-120779407/625000000 : ℝ)|=(120779407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s4_3 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127989549/5000000000 : ℝ)*x 0 + (502210301/1250000000 : ℝ)*x 1 + (4505872569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127989549/5000000000 : ℝ)^4581 ≤ (33280874381139/100000000000000 : ℝ)^3557 := by
    have hnat : (2127989549 : ℕ)^4581*100000000000000^3557 ≤ 33280874381139^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127989549 5000000000 33280874381139 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502210301/1250000000 : ℝ)^4581 ≤ (7725149661917/25000000000000 : ℝ)^3557 := by
    have hnat : (502210301 : ℕ)^4581*25000000000000^3557 ≤ 7725149661917^3557*1250000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502210301 1250000000 7725149661917 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505872569/10000000000 : ℝ)^4581 ≤ (35818526950423/100000000000000 : ℝ)^3557 := by
    have hnat : (4505872569 : ℕ)^4581*100000000000000^3557 ≤ 35818526950423^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505872569 10000000000 35818526950423 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127989549/5000000000 : ℝ), (502210301/1250000000 : ℝ), (4505872569/10000000000 : ℝ)] ![(33280874381139/100000000000000 : ℝ), (7725149661917/25000000000000 : ℝ), (35818526950423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127989549/5000000000 : ℝ)|^4581 ≤ (33280874381139/100000000000000 : ℝ)^3557
        have hw : |(2127989549/5000000000 : ℝ)|=(2127989549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502210301/1250000000 : ℝ)|^4581 ≤ (7725149661917/25000000000000 : ℝ)^3557
        have hw : |(502210301/1250000000 : ℝ)|=(502210301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505872569/10000000000 : ℝ)|^4581 ≤ (35818526950423/100000000000000 : ℝ)^3557
        have hw : |(4505872569/10000000000 : ℝ)|=(4505872569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s4_4 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-364916239/2000000000 : ℝ)*x 0 + (5219879031/10000000000 : ℝ)*x 1 + (5428508889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (364916239/2000000000 : ℝ)^4581 ≤ (5590293473891/50000000000000 : ℝ)^3557 := by
    have hnat : (364916239 : ℕ)^4581*50000000000000^3557 ≤ 5590293473891^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364916239 2000000000 5590293473891 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219879031/10000000000 : ℝ)^4581 ≤ (43289210477503/100000000000000 : ℝ)^3557 := by
    have hnat : (5219879031 : ℕ)^4581*100000000000000^3557 ≤ 43289210477503^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219879031 10000000000 43289210477503 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428508889/10000000000 : ℝ)^4581 ≤ (11382550639401/25000000000000 : ℝ)^3557 := by
    have hnat : (5428508889 : ℕ)^4581*25000000000000^3557 ≤ 11382550639401^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428508889 10000000000 11382550639401 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-364916239/2000000000 : ℝ), (5219879031/10000000000 : ℝ), (5428508889/10000000000 : ℝ)] ![(5590293473891/50000000000000 : ℝ), (43289210477503/100000000000000 : ℝ), (11382550639401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-364916239/2000000000 : ℝ)|^4581 ≤ (5590293473891/50000000000000 : ℝ)^3557
        have hw : |(-364916239/2000000000 : ℝ)|=(364916239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219879031/10000000000 : ℝ)|^4581 ≤ (43289210477503/100000000000000 : ℝ)^3557
        have hw : |(5219879031/10000000000 : ℝ)|=(5219879031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428508889/10000000000 : ℝ)|^4581 ≤ (11382550639401/25000000000000 : ℝ)^3557
        have hw : |(5428508889/10000000000 : ℝ)|=(5428508889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s4_5 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294358981/10000000000 : ℝ)*x 0 + (-1722746457/10000000000 : ℝ)*x 1 + (5428508863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294358981/10000000000 : ℝ)^4581 ≤ (4408632934059/10000000000000 : ℝ)^3557 := by
    have hnat : (5294358981 : ℕ)^4581*10000000000000^3557 ≤ 4408632934059^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294358981 10000000000 4408632934059 10000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1722746457/10000000000 : ℝ)^4581 ≤ (10383468374109/100000000000000 : ℝ)^3557 := by
    have hnat : (1722746457 : ℕ)^4581*100000000000000^3557 ≤ 10383468374109^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722746457 10000000000 10383468374109 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428508863/10000000000 : ℝ)^4581 ≤ (45530202276757/100000000000000 : ℝ)^3557 := by
    have hnat : (5428508863 : ℕ)^4581*100000000000000^3557 ≤ 45530202276757^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428508863 10000000000 45530202276757 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294358981/10000000000 : ℝ), (-1722746457/10000000000 : ℝ), (5428508863/10000000000 : ℝ)] ![(4408632934059/10000000000000 : ℝ), (10383468374109/100000000000000 : ℝ), (45530202276757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294358981/10000000000 : ℝ)|^4581 ≤ (4408632934059/10000000000000 : ℝ)^3557
        have hw : |(5294358981/10000000000 : ℝ)|=(5294358981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1722746457/10000000000 : ℝ)|^4581 ≤ (10383468374109/100000000000000 : ℝ)^3557
        have hw : |(-1722746457/10000000000 : ℝ)|=(1722746457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428508863/10000000000 : ℝ)|^4581 ≤ (45530202276757/100000000000000 : ℝ)^3557
        have hw : |(5428508863/10000000000 : ℝ)|=(5428508863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s4_6 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529435891/1000000000 : ℝ)*x 0 + (5428508849/10000000000 : ℝ)*x 1 + (-1722746573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529435891/1000000000 : ℝ)^4581 ≤ (1377697768099/3125000000000 : ℝ)^3557 := by
    have hnat : (529435891 : ℕ)^4581*3125000000000^3557 ≤ 1377697768099^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529435891 1000000000 1377697768099 3125000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428508849/10000000000 : ℝ)^4581 ≤ (11382550531383/25000000000000 : ℝ)^3557 := by
    have hnat : (5428508849 : ℕ)^4581*25000000000000^3557 ≤ 11382550531383^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428508849 10000000000 11382550531383 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1722746573/10000000000 : ℝ)^4581 ≤ (10383469274551/100000000000000 : ℝ)^3557 := by
    have hnat : (1722746573 : ℕ)^4581*100000000000000^3557 ≤ 10383469274551^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722746573 10000000000 10383469274551 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529435891/1000000000 : ℝ), (5428508849/10000000000 : ℝ), (-1722746573/10000000000 : ℝ)] ![(1377697768099/3125000000000 : ℝ), (11382550531383/25000000000000 : ℝ), (10383469274551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529435891/1000000000 : ℝ)|^4581 ≤ (1377697768099/3125000000000 : ℝ)^3557
        have hw : |(529435891/1000000000 : ℝ)|=(529435891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428508849/10000000000 : ℝ)|^4581 ≤ (11382550531383/25000000000000 : ℝ)^3557
        have hw : |(5428508849/10000000000 : ℝ)|=(5428508849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1722746573/10000000000 : ℝ)|^4581 ≤ (10383469274551/100000000000000 : ℝ)^3557
        have hw : |(-1722746573/10000000000 : ℝ)|=(1722746573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s4_7 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064010987/2500000000 : ℝ)*x 0 + (4503338673/10000000000 : ℝ)*x 1 + (4020234973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064010987/2500000000 : ℝ)^4581 ≤ (16640763742763/50000000000000 : ℝ)^3557 := by
    have hnat : (1064010987 : ℕ)^4581*50000000000000^3557 ≤ 16640763742763^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064010987 2500000000 16640763742763 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503338673/10000000000 : ℝ)^4581 ≤ (17896293806813/50000000000000 : ℝ)^3557 := by
    have hnat : (4503338673 : ℕ)^4581*50000000000000^3557 ≤ 17896293806813^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503338673 10000000000 17896293806813 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020234973/10000000000 : ℝ)^4581 ≤ (30925884886477/100000000000000 : ℝ)^3557 := by
    have hnat : (4020234973 : ℕ)^4581*100000000000000^3557 ≤ 30925884886477^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020234973 10000000000 30925884886477 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064010987/2500000000 : ℝ), (4503338673/10000000000 : ℝ), (4020234973/10000000000 : ℝ)] ![(16640763742763/50000000000000 : ℝ), (17896293806813/50000000000000 : ℝ), (30925884886477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064010987/2500000000 : ℝ)|^4581 ≤ (16640763742763/50000000000000 : ℝ)^3557
        have hw : |(1064010987/2500000000 : ℝ)|=(1064010987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503338673/10000000000 : ℝ)|^4581 ≤ (17896293806813/50000000000000 : ℝ)^3557
        have hw : |(4503338673/10000000000 : ℝ)|=(4503338673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020234973/10000000000 : ℝ)|^4581 ≤ (30925884886477/100000000000000 : ℝ)^3557
        have hw : |(4020234973/10000000000 : ℝ)|=(4020234973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1542_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5511/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5491/50000 : ℝ) ^ (4579/1024 : ℝ) ≤ (5131385924829159/100000000000000000000 : ℝ) := by
    have hpowers : (5491/50000 : ℝ)^4579 ≤ (5131385924829159/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5491 : ℕ)^4579*100000000000000000000^1024 ≤ 5131385924829159^1024*50000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5491 50000 5131385924829159 100000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5491/50000 : ℝ)) (X := (5131385924829159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15533/100000 : ℝ) ^ (4579/1024 : ℝ) ≤ (24185381456147953/100000000000000000000 : ℝ) := by
    have hpowers : (15533/100000 : ℝ)^4579 ≤ (24185381456147953/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15533 : ℕ)^4579*100000000000000000000^1024 ≤ 24185381456147953^1024*100000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15533 100000 24185381456147953 100000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15533/100000 : ℝ)) (X := (24185381456147953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005131385924829159/50000000000000000000 : ℝ) ≤ (5000114748413769/5000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (50005131385924829159/50000000000000000000 : ℝ)^1024 ≤ (5000114748413769/5000000000000000 : ℝ)^4579 := by
      have hnat : (50005131385924829159 : ℕ)^1024*5000000000000000^4579 ≤ 5000114748413769^4579*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005131385924829159 50000000000000000000 5000114748413769 5000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000114748413769/5000000000000000 : ℝ)) (X := (50005131385924829159/50000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503664595922622139/12500000000000000000 : ℝ) ≤ (5000327767569037/5000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (12503664595922622139/12500000000000000000 : ℝ)^1024 ≤ (5000327767569037/5000000000000000 : ℝ)^4579 := by
      have hnat : (12503664595922622139 : ℕ)^1024*5000000000000000^4579 ≤ 5000327767569037^4579*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503664595922622139 12500000000000000000 5000327767569037 5000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000327767569037/5000000000000000 : ℝ)) (X := (12503664595922622139/12500000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024185381456147953/50000000000000000000 : ℝ) ≤ (1000108157344861/1000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (50024185381456147953/50000000000000000000 : ℝ)^1024 ≤ (1000108157344861/1000000000000000 : ℝ)^4579 := by
      have hnat : (50024185381456147953 : ℕ)^1024*1000000000000000^4579 ≤ 1000108157344861^4579*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024185381456147953 50000000000000000000 1000108157344861 1000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000108157344861/1000000000000000 : ℝ)) (X := (50024185381456147953/50000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5131385924829159/100000000000000000000 : ℝ) ≤ ((22750843467304756367/22755000000000000000 : ℝ)+2*(53254788817/56887500000000 : ℝ)*(5491/50000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (22750843467304756367/22755000000000000000 : ℝ)+2*(53254788817/56887500000000 : ℝ)*(5491/50000 : ℝ)=(5000114748413769/5000000000000000 : ℝ) by norm_num, show 1+2*(5131385924829159/100000000000000000000 : ℝ)=(50005131385924829159/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24185381456147953/100000000000000000000 : ℝ)+(5131385924829159/100000000000000000000 : ℝ) ≤ ((22750843467304756367/22755000000000000000 : ℝ)+(53254788817/56887500000000 : ℝ)*((15533/100000 : ℝ)+(5491/50000 : ℝ)))^(4579/1024 : ℝ) := by
    rw [show (22750843467304756367/22755000000000000000 : ℝ)+(53254788817/56887500000000 : ℝ)*((15533/100000 : ℝ)+(5491/50000 : ℝ))=(5000327767569037/5000000000000000 : ℝ) by norm_num, show 1+(24185381456147953/100000000000000000000 : ℝ)+(5131385924829159/100000000000000000000 : ℝ)=(12503664595922622139/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24185381456147953/100000000000000000000 : ℝ) ≤ ((22750843467304756367/22755000000000000000 : ℝ)+2*(53254788817/56887500000000 : ℝ)*(15533/100000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (22750843467304756367/22755000000000000000 : ℝ)+2*(53254788817/56887500000000 : ℝ)*(15533/100000 : ℝ)=(1000108157344861/1000000000000000 : ℝ) by norm_num, show 1+2*(24185381456147953/100000000000000000000 : ℝ)=(50024185381456147953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22750843467304756367/22755000000000000000 : ℝ)*(X 1 0+X 2 0)+(53254788817/56887500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (15533/100000 : ℝ)) (c := (22750843467304756367/22755000000000000000 : ℝ)) (alpha := (53254788817/56887500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22750843467304756367/22755000000000000000 : ℝ)*(X 0 1+X 2 1)+(53254788817/56887500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (15533/100000 : ℝ)) (c := (22750843467304756367/22755000000000000000 : ℝ)) (alpha := (53254788817/56887500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22750843467304756367/22755000000000000000 : ℝ)*(X 0 2+X 1 2)+(53254788817/56887500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (15533/100000 : ℝ)) (c := (22750843467304756367/22755000000000000000 : ℝ)) (alpha := (53254788817/56887500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-456138309/2500000000 : ℝ)*X 0 0+(1357402823/2500000000 : ℝ)*X 0 1+(5218784713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674970131/5000000000 : ℝ)*X 1 0+(-1932470617/10000000000 : ℝ)*X 1 1+(1304696219/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349940367/10000000000 : ℝ)*X 2 0+(5218784849/10000000000 : ℝ)*X 2 1+(-120779407/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2127989549/5000000000 : ℝ)*X 0 0+(502210301/1250000000 : ℝ)*X 0 1+(4505872569/10000000000 : ℝ)*X 0 2+(2127989549/5000000000 : ℝ)*X 1 0+(502210301/1250000000 : ℝ)*X 1 1+(4505872569/10000000000 : ℝ)*X 1 2+(2127989549/5000000000 : ℝ)*X 2 0+(502210301/1250000000 : ℝ)*X 2 1+(4505872569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-364916239/2000000000 : ℝ)*X 0 0+(5219879031/10000000000 : ℝ)*X 0 1+(5428508889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294358981/10000000000 : ℝ)*X 1 0+(-1722746457/10000000000 : ℝ)*X 1 1+(5428508863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529435891/1000000000 : ℝ)*X 2 0+(5428508849/10000000000 : ℝ)*X 2 1+(-1722746573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1064010987/2500000000 : ℝ)*X 0 0+(4503338673/10000000000 : ℝ)*X 0 1+(4020234973/10000000000 : ℝ)*X 0 2+(1064010987/2500000000 : ℝ)*X 1 0+(4503338673/10000000000 : ℝ)*X 1 1+(4020234973/10000000000 : ℝ)*X 1 2+(1064010987/2500000000 : ℝ)*X 2 0+(4503338673/10000000000 : ℝ)*X 2 1+(4020234973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5714648511336357998283/948125000000000000000000000 : ℝ) := by norm_num
    linear_combination (377833607/50000000000000 : ℝ)*(base19) + (731976267/100000000000000 : ℝ)*(base23) + (7809849/12500000000000 : ℝ)*(lower2) + (45192457/50000000000000 : ℝ)*(upper3) + (15434867/12500000000000 : ℝ)*(upper5) + (424478690887017/12500000000000 : ℝ)*(major0) + (424478690887017/12500000000000 : ℝ)*(major1) + (424478690887017/12500000000000 : ℝ)*(major2) + (189729947069041/4000000000000 : ℝ)*(sp0) + (4743264525299119/100000000000000 : ℝ)*(sp1) + (4743264548990067/100000000000000 : ℝ)*(sp2) + (2048387694402703/100000000000000 : ℝ)*(sp3) + (16604240309/100000000000000 : ℝ)*(sp4) + (587791271/10000000000000 : ℝ)*(sp7) + (1024196786157707/50000000000000 : ℝ)*(f.failure) + (2371632640483167/50000000000000 : ℝ)*(f.sum) + (5107536477517/7585000000000000000000000000 : ℝ)*base65 + (661969887642900087/94812500000000000000000000000000 : ℝ)*base68 + (211127521649775087/94812500000000000000000000000000 : ℝ)*base70 + (971915662168162413/94812500000000000000000000000000 : ℝ)*base71 + (16127212682503/7585000000000000000000000000 : ℝ)*base74 + (646407764212349913/94812500000000000000000000000000 : ℝ)*base75 + (373862957112275087/94812500000000000000000000000000 : ℝ)*base78 + (63652929477849913/94812500000000000000000000000000 : ℝ)*base79 + (39672140926827/7585000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6696191/500000000000000000000 : ℝ)*base89 + (6696191/500000000000000000000 : ℝ)*base91 + (6696191/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (852957564535166568026927591/94812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80100621/6250000000000 : ℝ)*(base19) + (351826487/25000000000000 : ℝ)*(base23) + (6322683/4000000000000 : ℝ)*(upper3) + (51592827/50000000000000 : ℝ)*(lower4) + (93917017/50000000000000 : ℝ)*(upper5) + (857890555799491/25000000000000 : ℝ)*(major0) + (857890555799491/25000000000000 : ℝ)*(major1) + (857890555799491/25000000000000 : ℝ)*(major2) + (19804959753/100000000000000 : ℝ)*(sp1) + (1933601217/10000000000000 : ℝ)*(sp2) + (4793176304642453/100000000000000 : ℝ)*(sp4) + (1198288804518191/25000000000000 : ℝ)*(sp5) + (958631112264867/20000000000000 : ℝ)*(sp6) + (1034973920939127/50000000000000 : ℝ)*(sp7) + (1034973920939127/50000000000000 : ℝ)*(f.failure) + (4793176304642453/100000000000000 : ℝ)*(f.sum) + (141919843124669/22755000000000000000000000000 : ℝ)*base65 + (1371015127983488601/189625000000000000000000000000000 : ℝ)*base68 + (1003393288340738601/189625000000000000000000000000000 : ℝ)*base70 + (305921004272113601/189625000000000000000000000000000 : ℝ)*base72 + (20997008153011/22755000000000000000000000000 : ℝ)*base74 + (2486400777669613601/189625000000000000000000000000000 : ℝ)*base76 + (1829400958895863601/189625000000000000000000000000000 : ℝ)*base78 + (1222168927725238601/189625000000000000000000000000000 : ℝ)*base80 + (138937648143719/22755000000000000000000000000 : ℝ)*base81 + (385349/500000000000000000000 : ℝ)*base90 + (385349/500000000000000000000 : ℝ)*base92 + (385349/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1542_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1542_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1542_s5_0 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1824587347/10000000000 : ℝ)*x 0 + (339336349/625000000 : ℝ)*x 1 + (5218991847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1824587347/10000000000 : ℝ)^4581 ≤ (11180635498357/100000000000000 : ℝ)^3557 := by
    have hnat : (1824587347 : ℕ)^4581*100000000000000^3557 ≤ 11180635498357^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824587347 10000000000 11180635498357 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339336349/625000000 : ℝ)^4581 ≤ (9107925887581/20000000000000 : ℝ)^3557 := by
    have hnat : (339336349 : ℕ)^4581*20000000000000^3557 ≤ 9107925887581^3557*625000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339336349 625000000 9107925887581 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218991847/10000000000 : ℝ)^4581 ≤ (10819933762961/25000000000000 : ℝ)^3557 := by
    have hnat : (5218991847 : ℕ)^4581*25000000000000^3557 ≤ 10819933762961^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218991847 10000000000 10819933762961 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1824587347/10000000000 : ℝ), (339336349/625000000 : ℝ), (5218991847/10000000000 : ℝ)] ![(11180635498357/100000000000000 : ℝ), (9107925887581/20000000000000 : ℝ), (10819933762961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1824587347/10000000000 : ℝ)|^4581 ≤ (11180635498357/100000000000000 : ℝ)^3557
        have hw : |(-1824587347/10000000000 : ℝ)|=(1824587347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339336349/625000000 : ℝ)|^4581 ≤ (9107925887581/20000000000000 : ℝ)^3557
        have hw : |(339336349/625000000 : ℝ)|=(339336349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218991847/10000000000 : ℝ)|^4581 ≤ (10819933762961/25000000000000 : ℝ)^3557
        have hw : |(5218991847/10000000000 : ℝ)|=(5218991847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s5_1 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534987999/1000000000 : ℝ)*x 0 + (-193227589/1000000000 : ℝ)*x 1 + (1304747967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534987999/1000000000 : ℝ)^4581 ≤ (44682647148257/100000000000000 : ℝ)^3557 := by
    have hnat : (534987999 : ℕ)^4581*100000000000000^3557 ≤ 44682647148257^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534987999 1000000000 44682647148257 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193227589/1000000000 : ℝ)^4581 ≤ (94043887267/781250000000 : ℝ)^3557 := by
    have hnat : (193227589 : ℕ)^4581*781250000000^3557 ≤ 94043887267^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193227589 1000000000 94043887267 781250000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304747967/2500000000 : ℝ)^4581 ≤ (21639867638063/50000000000000 : ℝ)^3557 := by
    have hnat : (1304747967 : ℕ)^4581*50000000000000^3557 ≤ 21639867638063^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304747967 2500000000 21639867638063 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534987999/1000000000 : ℝ), (-193227589/1000000000 : ℝ), (1304747967/2500000000 : ℝ)] ![(44682647148257/100000000000000 : ℝ), (94043887267/781250000000 : ℝ), (21639867638063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534987999/1000000000 : ℝ)|^4581 ≤ (44682647148257/100000000000000 : ℝ)^3557
        have hw : |(534987999/1000000000 : ℝ)|=(534987999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-193227589/1000000000 : ℝ)|^4581 ≤ (94043887267/781250000000 : ℝ)^3557
        have hw : |(-193227589/1000000000 : ℝ)|=(193227589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304747967/2500000000 : ℝ)|^4581 ≤ (21639867638063/50000000000000 : ℝ)^3557
        have hw : |(1304747967/2500000000 : ℝ)|=(1304747967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s5_2 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337470001/2500000000 : ℝ)*x 0 + (1043798371/2000000000 : ℝ)*x 1 + (-1932275887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337470001/2500000000 : ℝ)^4581 ≤ (1396332728089/3125000000000 : ℝ)^3557 := by
    have hnat : (1337470001 : ℕ)^4581*3125000000000^3557 ≤ 1396332728089^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337470001 2500000000 1396332728089 3125000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043798371/2000000000 : ℝ)^4581 ≤ (8655947027457/20000000000000 : ℝ)^3557 := by
    have hnat : (1043798371 : ℕ)^4581*20000000000000^3557 ≤ 8655947027457^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043798371 2000000000 8655947027457 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1932275887/10000000000 : ℝ)^4581 ≤ (12037617546107/100000000000000 : ℝ)^3557 := by
    have hnat : (1932275887 : ℕ)^4581*100000000000000^3557 ≤ 12037617546107^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932275887 10000000000 12037617546107 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337470001/2500000000 : ℝ), (1043798371/2000000000 : ℝ), (-1932275887/10000000000 : ℝ)] ![(1396332728089/3125000000000 : ℝ), (8655947027457/20000000000000 : ℝ), (12037617546107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337470001/2500000000 : ℝ)|^4581 ≤ (1396332728089/3125000000000 : ℝ)^3557
        have hw : |(1337470001/2500000000 : ℝ)|=(1337470001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043798371/2000000000 : ℝ)|^4581 ≤ (8655947027457/20000000000000 : ℝ)^3557
        have hw : |(1043798371/2000000000 : ℝ)|=(1043798371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1932275887/10000000000 : ℝ)|^4581 ≤ (12037617546107/100000000000000 : ℝ)^3557
        have hw : |(-1932275887/10000000000 : ℝ)|=(1932275887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s5_3 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4256000649/10000000000 : ℝ)*x 0 + (1004546397/2500000000 : ℝ)*x 1 + (4505364513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256000649/10000000000 : ℝ)^4581 ≤ (16640545710477/50000000000000 : ℝ)^3557 := by
    have hnat : (4256000649 : ℕ)^4581*50000000000000^3557 ≤ 16640545710477^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256000649 10000000000 16640545710477 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004546397/2500000000 : ℝ)^4581 ≤ (30905582887323/100000000000000 : ℝ)^3557 := by
    have hnat : (1004546397 : ℕ)^4581*100000000000000^3557 ≤ 30905582887323^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004546397 2500000000 30905582887323 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505364513/10000000000 : ℝ)^4581 ≤ (8953331418969/25000000000000 : ℝ)^3557 := by
    have hnat : (4505364513 : ℕ)^4581*25000000000000^3557 ≤ 8953331418969^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505364513 10000000000 8953331418969 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256000649/10000000000 : ℝ), (1004546397/2500000000 : ℝ), (4505364513/10000000000 : ℝ)] ![(16640545710477/50000000000000 : ℝ), (30905582887323/100000000000000 : ℝ), (8953331418969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256000649/10000000000 : ℝ)|^4581 ≤ (16640545710477/50000000000000 : ℝ)^3557
        have hw : |(4256000649/10000000000 : ℝ)|=(4256000649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004546397/2500000000 : ℝ)|^4581 ≤ (30905582887323/100000000000000 : ℝ)^3557
        have hw : |(1004546397/2500000000 : ℝ)|=(1004546397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505364513/10000000000 : ℝ)|^4581 ≤ (8953331418969/25000000000000 : ℝ)^3557
        have hw : |(4505364513/10000000000 : ℝ)|=(4505364513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s5_4 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-5701923/31250000 : ℝ)*x 0 + (1044016309/2000000000 : ℝ)*x 1 + (5428283683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5701923/31250000 : ℝ)^4581 ≤ (1397607071619/12500000000000 : ℝ)^3557 := by
    have hnat : (5701923 : ℕ)^4581*12500000000000^3557 ≤ 1397607071619^3557*31250000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5701923 31250000 1397607071619 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044016309/2000000000 : ℝ)^4581 ≤ (2705710841289/6250000000000 : ℝ)^3557 := by
    have hnat : (1044016309 : ℕ)^4581*6250000000000^3557 ≤ 2705710841289^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044016309 2000000000 2705710841289 6250000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428283683/10000000000 : ℝ)^4581 ≤ (45527769945747/100000000000000 : ℝ)^3557 := by
    have hnat : (5428283683 : ℕ)^4581*100000000000000^3557 ≤ 45527769945747^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428283683 10000000000 45527769945747 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5701923/31250000 : ℝ), (1044016309/2000000000 : ℝ), (5428283683/10000000000 : ℝ)] ![(1397607071619/12500000000000 : ℝ), (2705710841289/6250000000000 : ℝ), (45527769945747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5701923/31250000 : ℝ)|^4581 ≤ (1397607071619/12500000000000 : ℝ)^3557
        have hw : |(-5701923/31250000 : ℝ)|=(5701923/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044016309/2000000000 : ℝ)|^4581 ≤ (2705710841289/6250000000000 : ℝ)^3557
        have hw : |(1044016309/2000000000 : ℝ)|=(1044016309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428283683/10000000000 : ℝ)|^4581 ≤ (45527769945747/100000000000000 : ℝ)^3557
        have hw : |(5428283683/10000000000 : ℝ)|=(5428283683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s5_5 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323603417/2500000000 : ℝ)*x 0 + (-861492057/5000000000 : ℝ)*x 1 + (5428283777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323603417/2500000000 : ℝ)^4581 ≤ (44086915818593/100000000000000 : ℝ)^3557 := by
    have hnat : (1323603417 : ℕ)^4581*100000000000000^3557 ≤ 44086915818593^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323603417 2500000000 44086915818593 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861492057/5000000000 : ℝ)^4581 ≤ (2077062641151/20000000000000 : ℝ)^3557 := by
    have hnat : (861492057 : ℕ)^4581*20000000000000^3557 ≤ 2077062641151^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861492057 5000000000 2077062641151 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428283777/10000000000 : ℝ)^4581 ≤ (45527770961103/100000000000000 : ℝ)^3557 := by
    have hnat : (5428283777 : ℕ)^4581*100000000000000^3557 ≤ 45527770961103^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428283777 10000000000 45527770961103 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323603417/2500000000 : ℝ), (-861492057/5000000000 : ℝ), (5428283777/10000000000 : ℝ)] ![(44086915818593/100000000000000 : ℝ), (2077062641151/20000000000000 : ℝ), (45527770961103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323603417/2500000000 : ℝ)|^4581 ≤ (44086915818593/100000000000000 : ℝ)^3557
        have hw : |(1323603417/2500000000 : ℝ)|=(1323603417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-861492057/5000000000 : ℝ)|^4581 ≤ (2077062641151/20000000000000 : ℝ)^3557
        have hw : |(-861492057/5000000000 : ℝ)|=(861492057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428283777/10000000000 : ℝ)|^4581 ≤ (45527770961103/100000000000000 : ℝ)^3557
        have hw : |(5428283777/10000000000 : ℝ)|=(5428283777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s5_6 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323603437/2500000000 : ℝ)*x 0 + (169633869/312500000 : ℝ)*x 1 + (-43074599/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323603437/2500000000 : ℝ)^4581 ≤ (8817383335307/20000000000000 : ℝ)^3557 := by
    have hnat : (1323603437 : ℕ)^4581*20000000000000^3557 ≤ 8817383335307^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323603437 2500000000 8817383335307 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169633869/312500000 : ℝ)^4581 ≤ (22763885647977/50000000000000 : ℝ)^3557 := by
    have hnat : (169633869 : ℕ)^4581*50000000000000^3557 ≤ 22763885647977^3557*312500000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169633869 312500000 22763885647977 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43074599/250000000 : ℝ)^4581 ≤ (10385312010293/100000000000000 : ℝ)^3557 := by
    have hnat : (43074599 : ℕ)^4581*100000000000000^3557 ≤ 10385312010293^3557*250000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43074599 250000000 10385312010293 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323603437/2500000000 : ℝ), (169633869/312500000 : ℝ), (-43074599/250000000 : ℝ)] ![(8817383335307/20000000000000 : ℝ), (22763885647977/50000000000000 : ℝ), (10385312010293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323603437/2500000000 : ℝ)|^4581 ≤ (8817383335307/20000000000000 : ℝ)^3557
        have hw : |(1323603437/2500000000 : ℝ)|=(1323603437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169633869/312500000 : ℝ)|^4581 ≤ (22763885647977/50000000000000 : ℝ)^3557
        have hw : |(169633869/312500000 : ℝ)|=(169633869/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43074599/250000000 : ℝ)|^4581 ≤ (10385312010293/100000000000000 : ℝ)^3557
        have hw : |(-43074599/250000000 : ℝ)|=(43074599/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s5_7 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4256065011/10000000000 : ℝ)*x 0 + (2251420557/5000000000 : ℝ)*x 1 + (2010363813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256065011/10000000000 : ℝ)^4581 ≤ (33281739611627/100000000000000 : ℝ)^3557 := by
    have hnat : (4256065011 : ℕ)^4581*100000000000000^3557 ≤ 33281739611627^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256065011 10000000000 33281739611627 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251420557/5000000000 : ℝ)^4581 ≤ (1431499785053/4000000000000 : ℝ)^3557 := by
    have hnat : (2251420557 : ℕ)^4581*4000000000000^3557 ≤ 1431499785053^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251420557 5000000000 1431499785053 4000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010363813/5000000000 : ℝ)^4581 ≤ (6186153148319/20000000000000 : ℝ)^3557 := by
    have hnat : (2010363813 : ℕ)^4581*20000000000000^3557 ≤ 6186153148319^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010363813 5000000000 6186153148319 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256065011/10000000000 : ℝ), (2251420557/5000000000 : ℝ), (2010363813/5000000000 : ℝ)] ![(33281739611627/100000000000000 : ℝ), (1431499785053/4000000000000 : ℝ), (6186153148319/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256065011/10000000000 : ℝ)|^4581 ≤ (33281739611627/100000000000000 : ℝ)^3557
        have hw : |(4256065011/10000000000 : ℝ)|=(4256065011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251420557/5000000000 : ℝ)|^4581 ≤ (1431499785053/4000000000000 : ℝ)^3557
        have hw : |(2251420557/5000000000 : ℝ)|=(2251420557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2010363813/5000000000 : ℝ)|^4581 ≤ (6186153148319/20000000000000 : ℝ)^3557
        have hw : |(2010363813/5000000000 : ℝ)|=(2010363813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1542_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5513/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5511/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5511/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5511/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5511/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5511/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5511/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5511/50000 : ℝ) ^ (4579/1024 : ℝ) ≤ (5215492373483117/100000000000000000000 : ℝ) := by
    have hpowers : (5511/50000 : ℝ)^4579 ≤ (5215492373483117/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5511 : ℕ)^4579*100000000000000000000^1024 ≤ 5215492373483117^1024*50000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5511 50000 5215492373483117 100000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5511/50000 : ℝ)) (X := (5215492373483117/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4579/1024 : ℝ) ≤ (11943713610381817/50000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4579 ≤ (11943713610381817/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4579*50000000000000000000^1024 ≤ 11943713610381817^1024*10000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 11943713610381817 50000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (11943713610381817/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005215492373483117/50000000000000000000 : ℝ) ≤ (2000046651652781/2000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (50005215492373483117/50000000000000000000 : ℝ)^1024 ≤ (2000046651652781/2000000000000000 : ℝ)^4579 := by
      have hnat : (50005215492373483117 : ℕ)^1024*2000000000000000^4579 ≤ 2000046651652781^4579*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005215492373483117 50000000000000000000 2000046651652781 2000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000046651652781/2000000000000000 : ℝ)) (X := (50005215492373483117/50000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029102919594246751/100000000000000000000 : ℝ) ≤ (39065042007627/39062500000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (100029102919594246751/100000000000000000000 : ℝ)^1024 ≤ (39065042007627/39062500000000 : ℝ)^4579 := by
      have hnat : (100029102919594246751 : ℕ)^1024*39062500000000^4579 ≤ 39065042007627^4579*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029102919594246751 100000000000000000000 39065042007627 39062500000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39065042007627/39062500000000 : ℝ)) (X := (100029102919594246751/100000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011943713610381817/25000000000000000000 : ℝ) ≤ (10001068249641119/10000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (25011943713610381817/25000000000000000000 : ℝ)^1024 ≤ (10001068249641119/10000000000000000 : ℝ)^4579 := by
      have hnat : (25011943713610381817 : ℕ)^1024*10000000000000000^4579 ≤ 10001068249641119^4579*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011943713610381817 25000000000000000000 10001068249641119 10000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001068249641119/10000000000000000 : ℝ)) (X := (25011943713610381817/25000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5215492373483117/100000000000000000000 : ℝ) ≤ ((2791989932685217177/2792500000000000000 : ℝ)+2*(417495688607/446800000000000 : ℝ)*(5511/50000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (2791989932685217177/2792500000000000000 : ℝ)+2*(417495688607/446800000000000 : ℝ)*(5511/50000 : ℝ)=(2000046651652781/2000000000000000 : ℝ) by norm_num, show 1+2*(5215492373483117/100000000000000000000 : ℝ)=(50005215492373483117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11943713610381817/50000000000000000000 : ℝ)+(5215492373483117/100000000000000000000 : ℝ) ≤ ((2791989932685217177/2792500000000000000 : ℝ)+(417495688607/446800000000000 : ℝ)*((1549/10000 : ℝ)+(5511/50000 : ℝ)))^(4579/1024 : ℝ) := by
    rw [show (2791989932685217177/2792500000000000000 : ℝ)+(417495688607/446800000000000 : ℝ)*((1549/10000 : ℝ)+(5511/50000 : ℝ))=(39065042007627/39062500000000 : ℝ) by norm_num, show 1+(11943713610381817/50000000000000000000 : ℝ)+(5215492373483117/100000000000000000000 : ℝ)=(100029102919594246751/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11943713610381817/50000000000000000000 : ℝ) ≤ ((2791989932685217177/2792500000000000000 : ℝ)+2*(417495688607/446800000000000 : ℝ)*(1549/10000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (2791989932685217177/2792500000000000000 : ℝ)+2*(417495688607/446800000000000 : ℝ)*(1549/10000 : ℝ)=(10001068249641119/10000000000000000 : ℝ) by norm_num, show 1+2*(11943713610381817/50000000000000000000 : ℝ)=(25011943713610381817/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2791989932685217177/2792500000000000000 : ℝ)*(X 1 0+X 2 0)+(417495688607/446800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (2791989932685217177/2792500000000000000 : ℝ)) (alpha := (417495688607/446800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2791989932685217177/2792500000000000000 : ℝ)*(X 0 1+X 2 1)+(417495688607/446800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (2791989932685217177/2792500000000000000 : ℝ)) (alpha := (417495688607/446800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2791989932685217177/2792500000000000000 : ℝ)*(X 0 2+X 1 2)+(417495688607/446800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (2791989932685217177/2792500000000000000 : ℝ)) (alpha := (417495688607/446800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1824587347/10000000000 : ℝ)*X 0 0+(339336349/625000000 : ℝ)*X 0 1+(5218991847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534987999/1000000000 : ℝ)*X 1 0+(-193227589/1000000000 : ℝ)*X 1 1+(1304747967/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337470001/2500000000 : ℝ)*X 2 0+(1043798371/2000000000 : ℝ)*X 2 1+(-1932275887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4256000649/10000000000 : ℝ)*X 0 0+(1004546397/2500000000 : ℝ)*X 0 1+(4505364513/10000000000 : ℝ)*X 0 2+(4256000649/10000000000 : ℝ)*X 1 0+(1004546397/2500000000 : ℝ)*X 1 1+(4505364513/10000000000 : ℝ)*X 1 2+(4256000649/10000000000 : ℝ)*X 2 0+(1004546397/2500000000 : ℝ)*X 2 1+(4505364513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-5701923/31250000 : ℝ)*X 0 0+(1044016309/2000000000 : ℝ)*X 0 1+(5428283683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323603417/2500000000 : ℝ)*X 1 0+(-861492057/5000000000 : ℝ)*X 1 1+(5428283777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323603437/2500000000 : ℝ)*X 2 0+(169633869/312500000 : ℝ)*X 2 1+(-43074599/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4256065011/10000000000 : ℝ)*X 0 0+(2251420557/5000000000 : ℝ)*X 0 1+(2010363813/5000000000 : ℝ)*X 0 2+(4256065011/10000000000 : ℝ)*X 1 0+(2251420557/5000000000 : ℝ)*X 1 1+(2010363813/5000000000 : ℝ)*X 1 2+(4256065011/10000000000 : ℝ)*X 2 0+(2251420557/5000000000 : ℝ)*X 2 1+(2010363813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111531223544240808236817/11170000000000000000000000000 : ℝ) := by norm_num
    linear_combination (426620723/25000000000000 : ℝ)*(base19) + (398895521/25000000000000 : ℝ)*(base23) + (16496249/25000000000000 : ℝ)*(lower2) + (243436893/100000000000000 : ℝ)*(upper3) + (158321363/100000000000000 : ℝ)*(upper5) + (1701449653786437/50000000000000 : ℝ)*(major0) + (1701449653786437/50000000000000 : ℝ)*(major1) + (1701449653786437/50000000000000 : ℝ)*(major2) + (475311232970649/10000000000000 : ℝ)*(sp0) + (4753138451139419/100000000000000 : ℝ)*(sp1) + (1188284640510057/25000000000000 : ℝ)*(sp2) + (513161325302741/25000000000000 : ℝ)*(sp3) + (27827915821/100000000000000 : ℝ)*(sp4) + (6411741397/50000000000000 : ℝ)*(sp7) + (1026329062346879/50000000000000 : ℝ)*(f.failure) + (594142519702789/12500000000000 : ℝ)*(f.sum) + (24290235000659/11170000000000000000000000000 : ℝ)*base65 + (234480103445227901/139625000000000000000000000000000 : ℝ)*base68 + (17802668763272099/139625000000000000000000000000000 : ℝ)*base69 + (168494509484897099/139625000000000000000000000000000 : ℝ)*base71 + (57389581939201/11170000000000000000000000000 : ℝ)*base74 + (380185676552102901/139625000000000000000000000000000 : ℝ)*base76 + (334302673368147099/139625000000000000000000000000000 : ℝ)*base77 + (1095608820594602901/139625000000000000000000000000000 : ℝ)*base80 + (21537611624541/11170000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (571427/500000000000000000000 : ℝ)*base89 + (571427/500000000000000000000 : ℝ)*base91 + (571427/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7015534879510098142983/1117000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1013635109/100000000000000 : ℝ)*(base19) + (1262957921/100000000000000 : ℝ)*(base23) + (81830661/25000000000000 : ℝ)*(lower1) + (3827149/6250000000000 : ℝ)*(upper2) + (4530771/2500000000000 : ℝ)*(upper3) + (172034147/100000000000000 : ℝ)*(upper5) + (21491256500369/625000000000 : ℝ)*(major0) + (21491256500369/625000000000 : ℝ)*(major1) + (21491256500369/625000000000 : ℝ)*(major2) + (5831179781/100000000000000 : ℝ)*(sp2) + (4803008154024249/100000000000000 : ℝ)*(sp4) + (4803007140389141/100000000000000 : ℝ)*(sp5) + (4803001059886547/100000000000000 : ℝ)*(sp6) + (259274214592171/12500000000000 : ℝ)*(sp7) + (259274214592171/12500000000000 : ℝ)*(f.failure) + (4803008154024249/100000000000000 : ℝ)*(f.sum) + (111053756867/69812500000000000000000000 : ℝ)*base66 + (28574483760223501/3490625000000000000000000000000 : ℝ)*base67 + (19429375855482749/3490625000000000000000000000000 : ℝ)*base70 + (3000213831986687/1745312500000000000000000000000 : ℝ)*base72 + (1141005095069/558500000000000000000000000 : ℝ)*base73 + (33127413853388999/3490625000000000000000000000000 : ℝ)*base76 + (9376027326194563/1745312500000000000000000000000 : ℝ)*base77 + (15347004575717251/3490625000000000000000000000000 : ℝ)*base79 + (6392231608753/1117000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (536223/125000000000000000000 : ℝ)*base89 + (536223/125000000000000000000 : ℝ)*base91 + (536223/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1542_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1542_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1542_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15893/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10651/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1542_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1542_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1542_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15893/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10651/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1542_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
