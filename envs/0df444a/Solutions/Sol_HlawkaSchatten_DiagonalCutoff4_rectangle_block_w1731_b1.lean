-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1731_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:06:52.675129+00:00
-- url     : https://prove2.me/submissions/4eb346b0-0778-4d78-9237-94e099170807

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
theorem support_rectangle_w1731_s3_0 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-167458833/1250000000 : ℝ)*x 0 + (5456954037/10000000000 : ℝ)*x 1 + (5140453869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167458833/1250000000 : ℝ)^5471 ≤ (8432842445143/100000000000000 : ℝ)^4447 := by
    have hnat : (167458833 : ℕ)^5471*100000000000000^4447 ≤ 8432842445143^4447*1250000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167458833 1250000000 8432842445143 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456954037/10000000000 : ℝ)^5471 ≤ (23732772551889/50000000000000 : ℝ)^4447 := by
    have hnat : (5456954037 : ℕ)^5471*50000000000000^4447 ≤ 23732772551889^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456954037 10000000000 23732772551889 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140453869/10000000000 : ℝ)^5471 ≤ (8820322488139/20000000000000 : ℝ)^4447 := by
    have hnat : (5140453869 : ℕ)^5471*20000000000000^4447 ≤ 8820322488139^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140453869 10000000000 8820322488139 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-167458833/1250000000 : ℝ), (5456954037/10000000000 : ℝ), (5140453869/10000000000 : ℝ)] ![(8432842445143/100000000000000 : ℝ), (23732772551889/50000000000000 : ℝ), (8820322488139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-167458833/1250000000 : ℝ)|^5471 ≤ (8432842445143/100000000000000 : ℝ)^4447
        have hw : |(-167458833/1250000000 : ℝ)|=(167458833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456954037/10000000000 : ℝ)|^5471 ≤ (23732772551889/50000000000000 : ℝ)^4447
        have hw : |(5456954037/10000000000 : ℝ)|=(5456954037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140453869/10000000000 : ℝ)|^5471 ≤ (8820322488139/20000000000000 : ℝ)^4447
        have hw : |(5140453869/10000000000 : ℝ)|=(5140453869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_1 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266823187/500000000 : ℝ)*x 0 + (-300706519/2000000000 : ℝ)*x 1 + (5140431657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266823187/500000000 : ℝ)^5471 ≤ (23089732457529/50000000000000 : ℝ)^4447 := by
    have hnat : (266823187 : ℕ)^5471*50000000000000^4447 ≤ 23089732457529^4447*500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266823187 500000000 23089732457529 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300706519/2000000000 : ℝ)^5471 ≤ (971915707789/10000000000000 : ℝ)^4447 := by
    have hnat : (300706519 : ℕ)^5471*10000000000000^4447 ≤ 971915707789^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300706519 2000000000 971915707789 10000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140431657/10000000000 : ℝ)^5471 ≤ (44101377996201/100000000000000 : ℝ)^4447 := by
    have hnat : (5140431657 : ℕ)^5471*100000000000000^4447 ≤ 44101377996201^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140431657 10000000000 44101377996201 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266823187/500000000 : ℝ), (-300706519/2000000000 : ℝ), (5140431657/10000000000 : ℝ)] ![(23089732457529/50000000000000 : ℝ), (971915707789/10000000000000 : ℝ), (44101377996201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266823187/500000000 : ℝ)|^5471 ≤ (23089732457529/50000000000000 : ℝ)^4447
        have hw : |(266823187/500000000 : ℝ)|=(266823187/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-300706519/2000000000 : ℝ)|^5471 ≤ (971915707789/10000000000000 : ℝ)^4447
        have hw : |(-300706519/2000000000 : ℝ)|=(300706519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140431657/10000000000 : ℝ)|^5471 ≤ (44101377996201/100000000000000 : ℝ)^4447
        have hw : |(5140431657/10000000000 : ℝ)|=(5140431657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_2 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2668230613/5000000000 : ℝ)*x 0 + (2570217171/5000000000 : ℝ)*x 1 + (-1503532397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2668230613/5000000000 : ℝ)^5471 ≤ (23089719075247/50000000000000 : ℝ)^4447 := by
    have hnat : (2668230613 : ℕ)^5471*50000000000000^4447 ≤ 23089719075247^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668230613 5000000000 23089719075247 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570217171/5000000000 : ℝ)^5471 ≤ (44101406335981/100000000000000 : ℝ)^4447 := by
    have hnat : (2570217171 : ℕ)^5471*100000000000000^4447 ≤ 44101406335981^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570217171 5000000000 44101406335981 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1503532397/10000000000 : ℝ)^5471 ≤ (9719155503253/100000000000000 : ℝ)^4447 := by
    have hnat : (1503532397 : ℕ)^5471*100000000000000^4447 ≤ 9719155503253^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503532397 10000000000 9719155503253 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2668230613/5000000000 : ℝ), (2570217171/5000000000 : ℝ), (-1503532397/10000000000 : ℝ)] ![(23089719075247/50000000000000 : ℝ), (44101406335981/100000000000000 : ℝ), (9719155503253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2668230613/5000000000 : ℝ)|^5471 ≤ (23089719075247/50000000000000 : ℝ)^4447
        have hw : |(2668230613/5000000000 : ℝ)|=(2668230613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570217171/5000000000 : ℝ)|^5471 ≤ (44101406335981/100000000000000 : ℝ)^4447
        have hw : |(2570217171/5000000000 : ℝ)|=(2570217171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1503532397/10000000000 : ℝ)|^5471 ≤ (9719155503253/100000000000000 : ℝ)^4447
        have hw : |(-1503532397/10000000000 : ℝ)|=(1503532397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_3 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (815731067/2000000000 : ℝ)*x 0 + (722951223/2000000000 : ℝ)*x 1 + (457649487/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (815731067/2000000000 : ℝ)^5471 ≤ (33176586082177/100000000000000 : ℝ)^4447 := by
    have hnat : (815731067 : ℕ)^5471*100000000000000^4447 ≤ 33176586082177^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815731067 2000000000 33176586082177 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (722951223/2000000000 : ℝ)^5471 ≤ (5719379450583/20000000000000 : ℝ)^4447 := by
    have hnat : (722951223 : ℕ)^5471*20000000000000^4447 ≤ 5719379450583^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722951223 2000000000 5719379450583 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457649487/1000000000 : ℝ)^5471 ≤ (38226516648371/100000000000000 : ℝ)^4447 := by
    have hnat : (457649487 : ℕ)^5471*100000000000000^4447 ≤ 38226516648371^4447*1000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457649487 1000000000 38226516648371 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(815731067/2000000000 : ℝ), (722951223/2000000000 : ℝ), (457649487/1000000000 : ℝ)] ![(33176586082177/100000000000000 : ℝ), (5719379450583/20000000000000 : ℝ), (38226516648371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(815731067/2000000000 : ℝ)|^5471 ≤ (33176586082177/100000000000000 : ℝ)^4447
        have hw : |(815731067/2000000000 : ℝ)|=(815731067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(722951223/2000000000 : ℝ)|^5471 ≤ (5719379450583/20000000000000 : ℝ)^4447
        have hw : |(722951223/2000000000 : ℝ)|=(722951223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(457649487/1000000000 : ℝ)|^5471 ≤ (38226516648371/100000000000000 : ℝ)^4447
        have hw : |(457649487/1000000000 : ℝ)|=(457649487/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_4 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-669907237/5000000000 : ℝ)*x 0 + (5144011231/10000000000 : ℝ)*x 1 + (5453340653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669907237/5000000000 : ℝ)^5471 ≤ (2108489037413/25000000000000 : ℝ)^4447 := by
    have hnat : (669907237 : ℕ)^5471*25000000000000^4447 ≤ 2108489037413^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669907237 5000000000 2108489037413 25000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144011231/10000000000 : ℝ)^5471 ≤ (22069581449619/50000000000000 : ℝ)^4447 := by
    have hnat : (5144011231 : ℕ)^5471*50000000000000^4447 ≤ 22069581449619^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144011231 10000000000 22069581449619 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453340653/10000000000 : ℝ)^5471 ≤ (47426880927409/100000000000000 : ℝ)^4447 := by
    have hnat : (5453340653 : ℕ)^5471*100000000000000^4447 ≤ 47426880927409^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453340653 10000000000 47426880927409 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-669907237/5000000000 : ℝ), (5144011231/10000000000 : ℝ), (5453340653/10000000000 : ℝ)] ![(2108489037413/25000000000000 : ℝ), (22069581449619/50000000000000 : ℝ), (47426880927409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-669907237/5000000000 : ℝ)|^5471 ≤ (2108489037413/25000000000000 : ℝ)^4447
        have hw : |(-669907237/5000000000 : ℝ)|=(669907237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144011231/10000000000 : ℝ)|^5471 ≤ (22069581449619/50000000000000 : ℝ)^4447
        have hw : |(5144011231/10000000000 : ℝ)|=(5144011231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453340653/10000000000 : ℝ)|^5471 ≤ (47426880927409/100000000000000 : ℝ)^4447
        have hw : |(5453340653/10000000000 : ℝ)|=(5453340653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_5 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625875763/5000000000 : ℝ)*x 0 + (-1190628697/10000000000 : ℝ)*x 1 + (1090668133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625875763/5000000000 : ℝ)^5471 ≤ (45279256183931/100000000000000 : ℝ)^4447 := by
    have hnat : (2625875763 : ℕ)^5471*100000000000000^4447 ≤ 45279256183931^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625875763 5000000000 45279256183931 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1190628697/10000000000 : ℝ)^5471 ≤ (145877254967/2000000000000 : ℝ)^4447 := by
    have hnat : (1190628697 : ℕ)^5471*2000000000000^4447 ≤ 145877254967^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190628697 10000000000 145877254967 2000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090668133/2000000000 : ℝ)^5471 ≤ (23713440527901/50000000000000 : ℝ)^4447 := by
    have hnat : (1090668133 : ℕ)^5471*50000000000000^4447 ≤ 23713440527901^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090668133 2000000000 23713440527901 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625875763/5000000000 : ℝ), (-1190628697/10000000000 : ℝ), (1090668133/2000000000 : ℝ)] ![(45279256183931/100000000000000 : ℝ), (145877254967/2000000000000 : ℝ), (23713440527901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625875763/5000000000 : ℝ)|^5471 ≤ (45279256183931/100000000000000 : ℝ)^4447
        have hw : |(2625875763/5000000000 : ℝ)|=(2625875763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1190628697/10000000000 : ℝ)|^5471 ≤ (145877254967/2000000000000 : ℝ)^4447
        have hw : |(-1190628697/10000000000 : ℝ)|=(1190628697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090668133/2000000000 : ℝ)|^5471 ≤ (23713440527901/50000000000000 : ℝ)^4447
        have hw : |(1090668133/2000000000 : ℝ)|=(1090668133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_6 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251751529/10000000000 : ℝ)*x 0 + (5453340667/10000000000 : ℝ)*x 1 + (-1190628689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251751529/10000000000 : ℝ)^5471 ≤ (5659907026969/12500000000000 : ℝ)^4447 := by
    have hnat : (5251751529 : ℕ)^5471*12500000000000^4447 ≤ 5659907026969^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251751529 10000000000 5659907026969 12500000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453340667/10000000000 : ℝ)^5471 ≤ (47426881077201/100000000000000 : ℝ)^4447 := by
    have hnat : (5453340667 : ℕ)^5471*100000000000000^4447 ≤ 47426881077201^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453340667 10000000000 47426881077201 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1190628689/10000000000 : ℝ)^5471 ≤ (911732836007/12500000000000 : ℝ)^4447 := by
    have hnat : (1190628689 : ℕ)^5471*12500000000000^4447 ≤ 911732836007^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190628689 10000000000 911732836007 12500000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251751529/10000000000 : ℝ), (5453340667/10000000000 : ℝ), (-1190628689/10000000000 : ℝ)] ![(5659907026969/12500000000000 : ℝ), (47426881077201/100000000000000 : ℝ), (911732836007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251751529/10000000000 : ℝ)|^5471 ≤ (5659907026969/12500000000000 : ℝ)^4447
        have hw : |(5251751529/10000000000 : ℝ)|=(5251751529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453340667/10000000000 : ℝ)|^5471 ≤ (47426881077201/100000000000000 : ℝ)^4447
        have hw : |(5453340667/10000000000 : ℝ)|=(5453340667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1190628689/10000000000 : ℝ)|^5471 ≤ (911732836007/12500000000000 : ℝ)^4447
        have hw : |(-1190628689/10000000000 : ℝ)|=(1190628689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_7 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (203953287/500000000 : ℝ)*x 0 + (2282831143/5000000000 : ℝ)*x 1 + (3625764469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203953287/500000000 : ℝ)^5471 ≤ (6636138630137/20000000000000 : ℝ)^4447 := by
    have hnat : (203953287 : ℕ)^5471*20000000000000^4447 ≤ 6636138630137^4447*500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203953287 500000000 6636138630137 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282831143/5000000000 : ℝ)^5471 ≤ (19057614757831/50000000000000 : ℝ)^4447 := by
    have hnat : (2282831143 : ℕ)^5471*50000000000000^4447 ≤ 19057614757831^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282831143 5000000000 19057614757831 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3625764469/10000000000 : ℝ)^5471 ≤ (28704077317973/100000000000000 : ℝ)^4447 := by
    have hnat : (3625764469 : ℕ)^5471*100000000000000^4447 ≤ 28704077317973^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3625764469 10000000000 28704077317973 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(203953287/500000000 : ℝ), (2282831143/5000000000 : ℝ), (3625764469/10000000000 : ℝ)] ![(6636138630137/20000000000000 : ℝ), (19057614757831/50000000000000 : ℝ), (28704077317973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(203953287/500000000 : ℝ)|^5471 ≤ (6636138630137/20000000000000 : ℝ)^4447
        have hw : |(203953287/500000000 : ℝ)|=(203953287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282831143/5000000000 : ℝ)|^5471 ≤ (19057614757831/50000000000000 : ℝ)^4447
        have hw : |(2282831143/5000000000 : ℝ)|=(2282831143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3625764469/10000000000 : ℝ)|^5471 ≤ (28704077317973/100000000000000 : ℝ)^4447
        have hw : |(3625764469/10000000000 : ℝ)|=(3625764469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_8 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4042089829/10000000000 : ℝ)*x 0 + (3075644703/5000000000 : ℝ)*x 1 + (-903610257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4042089829/10000000000 : ℝ)^5471 ≤ (8202761223217/25000000000000 : ℝ)^4447 := by
    have hnat : (4042089829 : ℕ)^5471*25000000000000^4447 ≤ 8202761223217^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4042089829 10000000000 8202761223217 25000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3075644703/5000000000 : ℝ)^5471 ≤ (55001167110427/100000000000000 : ℝ)^4447 := by
    have hnat : (3075644703 : ℕ)^5471*100000000000000^4447 ≤ 55001167110427^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3075644703 5000000000 55001167110427 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903610257/5000000000 : ℝ)^5471 ≤ (12187787983123/100000000000000 : ℝ)^4447 := by
    have hnat : (903610257 : ℕ)^5471*100000000000000^4447 ≤ 12187787983123^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903610257 5000000000 12187787983123 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4042089829/10000000000 : ℝ), (3075644703/5000000000 : ℝ), (-903610257/5000000000 : ℝ)] ![(8202761223217/25000000000000 : ℝ), (55001167110427/100000000000000 : ℝ), (12187787983123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4042089829/10000000000 : ℝ)|^5471 ≤ (8202761223217/25000000000000 : ℝ)^4447
        have hw : |(4042089829/10000000000 : ℝ)|=(4042089829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3075644703/5000000000 : ℝ)|^5471 ≤ (55001167110427/100000000000000 : ℝ)^4447
        have hw : |(3075644703/5000000000 : ℝ)|=(3075644703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-903610257/5000000000 : ℝ)|^5471 ≤ (12187787983123/100000000000000 : ℝ)^4447
        have hw : |(-903610257/5000000000 : ℝ)|=(903610257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_9 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1813345971/10000000000 : ℝ)*x 0 + (96917221/156250000 : ℝ)*x 1 + (995050703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1813345971/10000000000 : ℝ)^5471 ≤ (2447725961407/20000000000000 : ℝ)^4447 := by
    have hnat : (1813345971 : ℕ)^5471*20000000000000^4447 ≤ 2447725961407^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813345971 10000000000 2447725961407 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96917221/156250000 : ℝ)^5471 ≤ (5556726676371/10000000000000 : ℝ)^4447 := by
    have hnat : (96917221 : ℕ)^5471*10000000000000^4447 ≤ 5556726676371^4447*156250000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96917221 156250000 5556726676371 10000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995050703/2500000000 : ℝ)^5471 ≤ (8048525855707/25000000000000 : ℝ)^4447 := by
    have hnat : (995050703 : ℕ)^5471*25000000000000^4447 ≤ 8048525855707^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995050703 2500000000 8048525855707 25000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1813345971/10000000000 : ℝ), (96917221/156250000 : ℝ), (995050703/2500000000 : ℝ)] ![(2447725961407/20000000000000 : ℝ), (5556726676371/10000000000000 : ℝ), (8048525855707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1813345971/10000000000 : ℝ)|^5471 ≤ (2447725961407/20000000000000 : ℝ)^4447
        have hw : |(-1813345971/10000000000 : ℝ)|=(1813345971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96917221/156250000 : ℝ)|^5471 ≤ (5556726676371/10000000000000 : ℝ)^4447
        have hw : |(96917221/156250000 : ℝ)|=(96917221/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995050703/2500000000 : ℝ)|^5471 ≤ (8048525855707/25000000000000 : ℝ)^4447
        have hw : |(995050703/2500000000 : ℝ)|=(995050703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_10 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268105657/625000000 : ℝ)*x 0 + (-1712619621/10000000000 : ℝ)*x 1 + (2997702421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268105657/625000000 : ℝ)^5471 ≤ (35300883082423/100000000000000 : ℝ)^4447 := by
    have hnat : (268105657 : ℕ)^5471*100000000000000^4447 ≤ 35300883082423^4447*625000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268105657 625000000 35300883082423 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1712619621/10000000000 : ℝ)^5471 ≤ (11407693824017/100000000000000 : ℝ)^4447 := by
    have hnat : (1712619621 : ℕ)^5471*100000000000000^4447 ≤ 11407693824017^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712619621 10000000000 11407693824017 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2997702421/5000000000 : ℝ)^5471 ≤ (1665356971381/3125000000000 : ℝ)^4447 := by
    have hnat : (2997702421 : ℕ)^5471*3125000000000^4447 ≤ 1665356971381^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2997702421 5000000000 1665356971381 3125000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268105657/625000000 : ℝ), (-1712619621/10000000000 : ℝ), (2997702421/5000000000 : ℝ)] ![(35300883082423/100000000000000 : ℝ), (11407693824017/100000000000000 : ℝ), (1665356971381/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268105657/625000000 : ℝ)|^5471 ≤ (35300883082423/100000000000000 : ℝ)^4447
        have hw : |(268105657/625000000 : ℝ)|=(268105657/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1712619621/10000000000 : ℝ)|^5471 ≤ (11407693824017/100000000000000 : ℝ)^4447
        have hw : |(-1712619621/10000000000 : ℝ)|=(1712619621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2997702421/5000000000 : ℝ)|^5471 ≤ (1665356971381/3125000000000 : ℝ)^4447
        have hw : |(2997702421/5000000000 : ℝ)|=(2997702421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_11 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173809999/10000000000 : ℝ)*x 0 + (269419677/500000000 : ℝ)*x 1 + (-347142911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173809999/10000000000 : ℝ)^5471 ≤ (44453944405849/100000000000000 : ℝ)^4447 := by
    have hnat : (5173809999 : ℕ)^5471*100000000000000^4447 ≤ 44453944405849^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173809999 10000000000 44453944405849 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269419677/500000000 : ℝ)^5471 ≤ (46732938200611/100000000000000 : ℝ)^4447 := by
    have hnat : (269419677 : ℕ)^5471*100000000000000^4447 ≤ 46732938200611^4447*500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269419677 500000000 46732938200611 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (347142911/2500000000 : ℝ)^5471 ≤ (8813117373377/100000000000000 : ℝ)^4447 := by
    have hnat : (347142911 : ℕ)^5471*100000000000000^4447 ≤ 8813117373377^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347142911 2500000000 8813117373377 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173809999/10000000000 : ℝ), (269419677/500000000 : ℝ), (-347142911/2500000000 : ℝ)] ![(44453944405849/100000000000000 : ℝ), (46732938200611/100000000000000 : ℝ), (8813117373377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173809999/10000000000 : ℝ)|^5471 ≤ (44453944405849/100000000000000 : ℝ)^4447
        have hw : |(5173809999/10000000000 : ℝ)|=(5173809999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269419677/500000000 : ℝ)|^5471 ≤ (46732938200611/100000000000000 : ℝ)^4447
        have hw : |(269419677/500000000 : ℝ)|=(269419677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-347142911/2500000000 : ℝ)|^5471 ≤ (8813117373377/100000000000000 : ℝ)^4447
        have hw : |(-347142911/2500000000 : ℝ)|=(347142911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s3_12 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218886659/625000000 : ℝ)*x 0 + (2067854341/5000000000 : ℝ)*x 1 + (2313506873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218886659/625000000 : ℝ)^5471 ≤ (27505235977941/100000000000000 : ℝ)^4447 := by
    have hnat : (218886659 : ℕ)^5471*100000000000000^4447 ≤ 27505235977941^4447*625000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218886659 625000000 27505235977941 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067854341/5000000000 : ℝ)^5471 ≤ (6749689760973/20000000000000 : ℝ)^4447 := by
    have hnat : (2067854341 : ℕ)^5471*20000000000000^4447 ≤ 6749689760973^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067854341 5000000000 6749689760973 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2313506873/5000000000 : ℝ)^5471 ≤ (7749263040241/20000000000000 : ℝ)^4447 := by
    have hnat : (2313506873 : ℕ)^5471*20000000000000^4447 ≤ 7749263040241^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313506873 5000000000 7749263040241 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218886659/625000000 : ℝ), (2067854341/5000000000 : ℝ), (2313506873/5000000000 : ℝ)] ![(27505235977941/100000000000000 : ℝ), (6749689760973/20000000000000 : ℝ), (7749263040241/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218886659/625000000 : ℝ)|^5471 ≤ (27505235977941/100000000000000 : ℝ)^4447
        have hw : |(218886659/625000000 : ℝ)|=(218886659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2067854341/5000000000 : ℝ)|^5471 ≤ (6749689760973/20000000000000 : ℝ)^4447
        have hw : |(2067854341/5000000000 : ℝ)|=(2067854341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2313506873/5000000000 : ℝ)|^5471 ≤ (7749263040241/20000000000000 : ℝ)^4447
        have hw : |(2313506873/5000000000 : ℝ)|=(2313506873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1731_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2539/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10161/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8471/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2539/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2539/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2539/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2539/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2539/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2539/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2539/25000 : ℝ) ^ (5463/1024 : ℝ) ≤ (100446395885479/20000000000000000000 : ℝ) := by
    have hpowers : (2539/25000 : ℝ)^5463 ≤ (100446395885479/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2539 : ℕ)^5463*20000000000000000000^1024 ≤ 100446395885479^1024*25000^5463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2539 25000 100446395885479 20000000000000000000 5463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2539/25000 : ℝ)) (X := (100446395885479/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16947/100000 : ℝ) ^ (5463/1024 : ℝ) ≤ (1928325602214547/25000000000000000000 : ℝ) := by
    have hpowers : (16947/100000 : ℝ)^5463 ≤ (1928325602214547/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16947 : ℕ)^5463*25000000000000000000^1024 ≤ 1928325602214547^1024*100000^5463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16947 100000 1928325602214547 25000000000000000000 5463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16947/100000 : ℝ)) (X := (1928325602214547/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000100446395885479/10000000000000000000 : ℝ) ≤ (10000018827876559/10000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (10000100446395885479/10000000000000000000 : ℝ)^1024 ≤ (10000018827876559/10000000000000000 : ℝ)^5463 := by
      have hnat : (10000100446395885479 : ℕ)^1024*10000000000000000^5463 ≤ 10000018827876559^5463*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000100446395885479 10000000000000000000 10000018827876559 10000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000018827876559/10000000000000000 : ℝ)) (X := (10000100446395885479/10000000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008215534388285583/100000000000000000000 : ℝ) ≤ (10000153989134699/10000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (100008215534388285583/100000000000000000000 : ℝ)^1024 ≤ (10000153989134699/10000000000000000 : ℝ)^5463 := by
      have hnat : (100008215534388285583 : ℕ)^1024*10000000000000000^5463 ≤ 10000153989134699^5463*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008215534388285583 100000000000000000000 10000153989134699 10000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000153989134699/10000000000000000 : ℝ)) (X := (100008215534388285583/100000000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12501928325602214547/12500000000000000000 : ℝ) ≤ (10000289150392839/10000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (12501928325602214547/12500000000000000000 : ℝ)^1024 ≤ (10000289150392839/10000000000000000 : ℝ)^5463 := by
      have hnat : (12501928325602214547 : ℕ)^1024*10000000000000000^5463 ≤ 10000289150392839^5463*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501928325602214547 12500000000000000000 10000289150392839 10000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000289150392839/10000000000000000 : ℝ)) (X := (12501928325602214547/12500000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(100446395885479/20000000000000000000 : ℝ) ≤ ((67907382464634372489/67910000000000000000 : ℝ)+2*(6758062907/33955000000000 : ℝ)*(2539/25000 : ℝ))^(5463/1024 : ℝ) := by
    rw [show (67907382464634372489/67910000000000000000 : ℝ)+2*(6758062907/33955000000000 : ℝ)*(2539/25000 : ℝ)=(10000018827876559/10000000000000000 : ℝ) by norm_num, show 1+2*(100446395885479/20000000000000000000 : ℝ)=(10000100446395885479/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1928325602214547/25000000000000000000 : ℝ)+(100446395885479/20000000000000000000 : ℝ) ≤ ((67907382464634372489/67910000000000000000 : ℝ)+(6758062907/33955000000000 : ℝ)*((16947/100000 : ℝ)+(2539/25000 : ℝ)))^(5463/1024 : ℝ) := by
    rw [show (67907382464634372489/67910000000000000000 : ℝ)+(6758062907/33955000000000 : ℝ)*((16947/100000 : ℝ)+(2539/25000 : ℝ))=(10000153989134699/10000000000000000 : ℝ) by norm_num, show 1+(1928325602214547/25000000000000000000 : ℝ)+(100446395885479/20000000000000000000 : ℝ)=(100008215534388285583/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1928325602214547/25000000000000000000 : ℝ) ≤ ((67907382464634372489/67910000000000000000 : ℝ)+2*(6758062907/33955000000000 : ℝ)*(16947/100000 : ℝ))^(5463/1024 : ℝ) := by
    rw [show (67907382464634372489/67910000000000000000 : ℝ)+2*(6758062907/33955000000000 : ℝ)*(16947/100000 : ℝ)=(10000289150392839/10000000000000000 : ℝ) by norm_num, show 1+2*(1928325602214547/25000000000000000000 : ℝ)=(12501928325602214547/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67907382464634372489/67910000000000000000 : ℝ)*(X 1 0+X 2 0)+(6758062907/33955000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (2539/25000 : ℝ)) (hi := (16947/100000 : ℝ)) (c := (67907382464634372489/67910000000000000000 : ℝ)) (alpha := (6758062907/33955000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67907382464634372489/67910000000000000000 : ℝ)*(X 0 1+X 2 1)+(6758062907/33955000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (2539/25000 : ℝ)) (hi := (16947/100000 : ℝ)) (c := (67907382464634372489/67910000000000000000 : ℝ)) (alpha := (6758062907/33955000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67907382464634372489/67910000000000000000 : ℝ)*(X 0 2+X 1 2)+(6758062907/33955000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (2539/25000 : ℝ)) (hi := (16947/100000 : ℝ)) (c := (67907382464634372489/67910000000000000000 : ℝ)) (alpha := (6758062907/33955000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-167458833/1250000000 : ℝ)*X 0 0+(5456954037/10000000000 : ℝ)*X 0 1+(5140453869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((266823187/500000000 : ℝ)*X 1 0+(-300706519/2000000000 : ℝ)*X 1 1+(5140431657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2668230613/5000000000 : ℝ)*X 2 0+(2570217171/5000000000 : ℝ)*X 2 1+(-1503532397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((815731067/2000000000 : ℝ)*X 0 0+(722951223/2000000000 : ℝ)*X 0 1+(457649487/1000000000 : ℝ)*X 0 2+(815731067/2000000000 : ℝ)*X 1 0+(722951223/2000000000 : ℝ)*X 1 1+(457649487/1000000000 : ℝ)*X 1 2+(815731067/2000000000 : ℝ)*X 2 0+(722951223/2000000000 : ℝ)*X 2 1+(457649487/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-669907237/5000000000 : ℝ)*X 0 0+(5144011231/10000000000 : ℝ)*X 0 1+(5453340653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2625875763/5000000000 : ℝ)*X 1 0+(-1190628697/10000000000 : ℝ)*X 1 1+(1090668133/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251751529/10000000000 : ℝ)*X 2 0+(5453340667/10000000000 : ℝ)*X 2 1+(-1190628689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((203953287/500000000 : ℝ)*X 0 0+(2282831143/5000000000 : ℝ)*X 0 1+(3625764469/10000000000 : ℝ)*X 0 2+(203953287/500000000 : ℝ)*X 1 0+(2282831143/5000000000 : ℝ)*X 1 1+(3625764469/10000000000 : ℝ)*X 1 2+(203953287/500000000 : ℝ)*X 2 0+(2282831143/5000000000 : ℝ)*X 2 1+(3625764469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((4042089829/10000000000 : ℝ)*X 2 0+(3075644703/5000000000 : ℝ)*X 2 1+(-903610257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_8 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((-1813345971/10000000000 : ℝ)*X 0 0+(96917221/156250000 : ℝ)*X 0 1+(995050703/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_9 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((268105657/625000000 : ℝ)*X 1 0+(-1712619621/10000000000 : ℝ)*X 1 1+(2997702421/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_10 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((5173809999/10000000000 : ℝ)*X 2 0+(269419677/500000000 : ℝ)*X 2 1+(-347142911/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_11 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((218886659/625000000 : ℝ)*X 0 0+(2067854341/5000000000 : ℝ)*X 0 1+(2313506873/5000000000 : ℝ)*X 0 2+(218886659/625000000 : ℝ)*X 1 0+(2067854341/5000000000 : ℝ)*X 1 1+(2313506873/5000000000 : ℝ)*X 1 2+(218886659/625000000 : ℝ)*X 2 0+(2067854341/5000000000 : ℝ)*X 2 1+(2313506873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s3_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4245066106926554537512522767/3395500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49071957/25000000000000 : ℝ)*(lower2) + (2099608382648033/100000000000000 : ℝ)*(major0) + (2099608382648033/100000000000000 : ℝ)*(major1) + (2099608382648033/100000000000000 : ℝ)*(major2) + (3159398830421341/100000000000000 : ℝ)*(sp0) + (78982647651083/2500000000000 : ℝ)*(sp1) + (1579647858736949/50000000000000 : ℝ)*(sp2) + (64985576205841/6250000000000 : ℝ)*(sp3) + (99035051291/100000000000000 : ℝ)*(sp5) + (33354366127/50000000000000 : ℝ)*(sp6) + (22038519363/100000000000000 : ℝ)*(sp9) + (15927846093/100000000000000 : ℝ)*(sp10) + (7305341819/12500000000000 : ℝ)*(sp11) + (26635388449/100000000000000 : ℝ)*(sp12) + (207959170936381/20000000000000 : ℝ)*(f.failure) + (98731902154397/3125000000000 : ℝ)*(f.sum) + (5848388198281/1358200000000000000000000000 : ℝ)*base66 + (32924356453290164137/6791000000000000000000000000000000 : ℝ)*base67 + (44039578591598164137/6791000000000000000000000000000000 : ℝ)*base69 + (29255118367049164137/6791000000000000000000000000000000 : ℝ)*base71 + (4710451190213/3395500000000000000000000000 : ℝ)*base73 + (5040597459582164137/6791000000000000000000000000000000 : ℝ)*base75 + (7554652531569164137/6791000000000000000000000000000000 : ℝ)*base77 + (27453155215815164137/6791000000000000000000000000000000 : ℝ)*base79 + (42795461259/679100000000000000000000000 : ℝ)*base81 + (6132451/1000000000000000000000 : ℝ)*base90 + (6132451/1000000000000000000000 : ℝ)*base92 + (6132451/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29206088016292182324609/1697750000000000000000000000 : ℝ) := by norm_num
    linear_combination (237394171/100000000000000 : ℝ)*(upper3) + (50261683/12500000000000 : ℝ)*(upper5) + (107418758519729/5000000000000 : ℝ)*(major0) + (107418758519729/5000000000000 : ℝ)*(major1) + (107418758519729/5000000000000 : ℝ)*(major2) + (4959151293/100000000000000 : ℝ)*(sp1) + (646560595710279/20000000000000 : ℝ)*(sp4) + (808197712206579/25000000000000 : ℝ)*(sp5) + (50512350404339/1562500000000 : ℝ)*(sp6) + (1063945312066109/100000000000000 : ℝ)*(sp7) + (4868476117/100000000000000 : ℝ)*(sp8) + (3585286893/50000000000000 : ℝ)*(sp10) + (3842098791/50000000000000 : ℝ)*(sp11) + (184593039/12500000000000 : ℝ)*(sp12) + (1063946788810421/100000000000000 : ℝ)*(f.failure) + (646560595710279/20000000000000 : ℝ)*(f.sum) + (903477585631/3395500000000000000000000000 : ℝ)*base65 + (2790705518531314519/339550000000000000000000000000000 : ℝ)*base68 + (2340990424209064519/339550000000000000000000000000000 : ℝ)*base70 + (247235885942535481/339550000000000000000000000000000 : ℝ)*base71 + (130347086807/10865600000000000000000000 : ℝ)*base74 + (357096449754035481/339550000000000000000000000000000 : ℝ)*base75 + (789619091269685481/339550000000000000000000000000000 : ℝ)*base77 + (608377862745264519/339550000000000000000000000000000 : ℝ)*base80 + (8934316728713/6791000000000000000000000000 : ℝ)*base82 + (5714709/5000000000000000000000 : ℝ)*base89 + (5714709/5000000000000000000000 : ℝ)*base91 + (5714709/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1731_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2539/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8471/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1731_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1731_box_0 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-129561839/1250000000 : ℝ)*x 0 + (1351595239/2500000000 : ℝ)*x 1 + (5406380821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129561839/1250000000 : ℝ)^5471 ≤ (6150127101107/100000000000000 : ℝ)^4447 := by
    have hnat : (129561839 : ℕ)^5471*100000000000000^4447 ≤ 6150127101107^4447*1250000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129561839 1250000000 6150127101107 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351595239/2500000000 : ℝ)^5471 ≤ (23462468582231/50000000000000 : ℝ)^4447 := by
    have hnat : (1351595239 : ℕ)^5471*50000000000000^4447 ≤ 23462468582231^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351595239 2500000000 23462468582231 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406380821/10000000000 : ℝ)^5471 ≤ (4692493572291/10000000000000 : ℝ)^4447 := by
    have hnat : (5406380821 : ℕ)^5471*10000000000000^4447 ≤ 4692493572291^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406380821 10000000000 4692493572291 10000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129561839/1250000000 : ℝ), (1351595239/2500000000 : ℝ), (5406380821/10000000000 : ℝ)] ![(6150127101107/100000000000000 : ℝ), (23462468582231/50000000000000 : ℝ), (4692493572291/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129561839/1250000000 : ℝ)|^5471 ≤ (6150127101107/100000000000000 : ℝ)^4447
        have hw : |(-129561839/1250000000 : ℝ)|=(129561839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351595239/2500000000 : ℝ)|^5471 ≤ (23462468582231/50000000000000 : ℝ)^4447
        have hw : |(1351595239/2500000000 : ℝ)|=(1351595239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406380821/10000000000 : ℝ)|^5471 ≤ (4692493572291/10000000000000 : ℝ)^4447
        have hw : |(5406380821/10000000000 : ℝ)|=(5406380821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_1 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612049039/5000000000 : ℝ)*x 0 + (-129509259/1000000000 : ℝ)*x 1 + (2703190213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612049039/5000000000 : ℝ)^5471 ≤ (8997222537553/20000000000000 : ℝ)^4447 := by
    have hnat : (2612049039 : ℕ)^5471*20000000000000^4447 ≤ 8997222537553^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612049039 5000000000 8997222537553 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129509259/1000000000 : ℝ)^5471 ≤ (4044477896127/50000000000000 : ℝ)^4447 := by
    have hnat : (129509259 : ℕ)^5471*50000000000000^4447 ≤ 4044477896127^4447*1000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129509259 1000000000 4044477896127 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703190213/5000000000 : ℝ)^5471 ≤ (9384986301007/20000000000000 : ℝ)^4447 := by
    have hnat : (2703190213 : ℕ)^5471*20000000000000^4447 ≤ 9384986301007^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703190213 5000000000 9384986301007 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612049039/5000000000 : ℝ), (-129509259/1000000000 : ℝ), (2703190213/5000000000 : ℝ)] ![(8997222537553/20000000000000 : ℝ), (4044477896127/50000000000000 : ℝ), (9384986301007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612049039/5000000000 : ℝ)|^5471 ≤ (8997222537553/20000000000000 : ℝ)^4447
        have hw : |(2612049039/5000000000 : ℝ)|=(2612049039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129509259/1000000000 : ℝ)|^5471 ≤ (4044477896127/50000000000000 : ℝ)^4447
        have hw : |(-129509259/1000000000 : ℝ)|=(129509259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703190213/5000000000 : ℝ)|^5471 ≤ (9384986301007/20000000000000 : ℝ)^4447
        have hw : |(2703190213/5000000000 : ℝ)|=(2703190213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_2 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044819559/2000000000 : ℝ)*x 0 + (5406380723/10000000000 : ℝ)*x 1 + (-1295092567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044819559/2000000000 : ℝ)^5471 ≤ (2811631855601/6250000000000 : ℝ)^4447 := by
    have hnat : (1044819559 : ℕ)^5471*6250000000000^4447 ≤ 2811631855601^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044819559 2000000000 2811631855601 6250000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406380723/10000000000 : ℝ)^5471 ≤ (938498693529/2000000000000 : ℝ)^4447 := by
    have hnat : (5406380723 : ℕ)^5471*2000000000000^4447 ≤ 938498693529^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406380723 10000000000 938498693529 2000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295092567/10000000000 : ℝ)^5471 ≤ (8088955615521/100000000000000 : ℝ)^4447 := by
    have hnat : (1295092567 : ℕ)^5471*100000000000000^4447 ≤ 8088955615521^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295092567 10000000000 8088955615521 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044819559/2000000000 : ℝ), (5406380723/10000000000 : ℝ), (-1295092567/10000000000 : ℝ)] ![(2811631855601/6250000000000 : ℝ), (938498693529/2000000000000 : ℝ), (8088955615521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044819559/2000000000 : ℝ)|^5471 ≤ (2811631855601/6250000000000 : ℝ)^4447
        have hw : |(1044819559/2000000000 : ℝ)|=(1044819559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406380723/10000000000 : ℝ)|^5471 ≤ (938498693529/2000000000000 : ℝ)^4447
        have hw : |(5406380723/10000000000 : ℝ)|=(5406380723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1295092567/10000000000 : ℝ)|^5471 ≤ (8088955615521/100000000000000 : ℝ)^4447
        have hw : |(-1295092567/10000000000 : ℝ)|=(1295092567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_3 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4458524319/10000000000 : ℝ)*x 0 + (3909408467/10000000000 : ℝ)*x 1 + (1954704411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4458524319/10000000000 : ℝ)^5471 ≤ (18508926518217/50000000000000 : ℝ)^4447 := by
    have hnat : (4458524319 : ℕ)^5471*50000000000000^4447 ≤ 18508926518217^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4458524319 10000000000 18508926518217 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3909408467/10000000000 : ℝ)^5471 ≤ (31491071721693/100000000000000 : ℝ)^4447 := by
    have hnat : (3909408467 : ℕ)^5471*100000000000000^4447 ≤ 31491071721693^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3909408467 10000000000 31491071721693 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1954704411/5000000000 : ℝ)^5471 ≤ (15745537619881/50000000000000 : ℝ)^4447 := by
    have hnat : (1954704411 : ℕ)^5471*50000000000000^4447 ≤ 15745537619881^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954704411 5000000000 15745537619881 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4458524319/10000000000 : ℝ), (3909408467/10000000000 : ℝ), (1954704411/5000000000 : ℝ)] ![(18508926518217/50000000000000 : ℝ), (31491071721693/100000000000000 : ℝ), (15745537619881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4458524319/10000000000 : ℝ)|^5471 ≤ (18508926518217/50000000000000 : ℝ)^4447
        have hw : |(4458524319/10000000000 : ℝ)|=(4458524319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3909408467/10000000000 : ℝ)|^5471 ≤ (31491071721693/100000000000000 : ℝ)^4447
        have hw : |(3909408467/10000000000 : ℝ)|=(3909408467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1954704411/5000000000 : ℝ)|^5471 ≤ (15745537619881/50000000000000 : ℝ)^4447
        have hw : |(1954704411/5000000000 : ℝ)|=(1954704411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_4 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1663149333/10000000000 : ℝ)*x 0 + (517799351/1000000000 : ℝ)*x 1 + (2588996933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1663149333/10000000000 : ℝ)^5471 ≤ (687728423801/6250000000000 : ℝ)^4447 := by
    have hnat : (1663149333 : ℕ)^5471*6250000000000^4447 ≤ 687728423801^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663149333 10000000000 687728423801 6250000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517799351/1000000000 : ℝ)^5471 ≤ (22249085360067/50000000000000 : ℝ)^4447 := by
    have hnat : (517799351 : ℕ)^5471*50000000000000^4447 ≤ 22249085360067^4447*1000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517799351 1000000000 22249085360067 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588996933/5000000000 : ℝ)^5471 ≤ (22249087241983/50000000000000 : ℝ)^4447 := by
    have hnat : (2588996933 : ℕ)^5471*50000000000000^4447 ≤ 22249087241983^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588996933 5000000000 22249087241983 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1663149333/10000000000 : ℝ), (517799351/1000000000 : ℝ), (2588996933/5000000000 : ℝ)] ![(687728423801/6250000000000 : ℝ), (22249085360067/50000000000000 : ℝ), (22249087241983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1663149333/10000000000 : ℝ)|^5471 ≤ (687728423801/6250000000000 : ℝ)^4447
        have hw : |(-1663149333/10000000000 : ℝ)|=(1663149333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517799351/1000000000 : ℝ)|^5471 ≤ (22249085360067/50000000000000 : ℝ)^4447
        have hw : |(517799351/1000000000 : ℝ)|=(517799351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588996933/5000000000 : ℝ)|^5471 ≤ (22249087241983/50000000000000 : ℝ)^4447
        have hw : |(2588996933/5000000000 : ℝ)|=(2588996933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_5 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689112941/5000000000 : ℝ)*x 0 + (-349198287/2500000000 : ℝ)*x 1 + (1294498341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689112941/5000000000 : ℝ)^5471 ≤ (23312236566937/50000000000000 : ℝ)^4447 := by
    have hnat : (2689112941 : ℕ)^5471*50000000000000^4447 ≤ 23312236566937^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689112941 5000000000 23312236566937 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349198287/2500000000 : ℝ)^5471 ≤ (4438678841383/50000000000000 : ℝ)^4447 := by
    have hnat : (349198287 : ℕ)^5471*50000000000000^4447 ≤ 4438678841383^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349198287 2500000000 4438678841383 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294498341/2500000000 : ℝ)^5471 ≤ (2224908458827/5000000000000 : ℝ)^4447 := by
    have hnat : (1294498341 : ℕ)^5471*5000000000000^4447 ≤ 2224908458827^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294498341 2500000000 2224908458827 5000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689112941/5000000000 : ℝ), (-349198287/2500000000 : ℝ), (1294498341/2500000000 : ℝ)] ![(23312236566937/50000000000000 : ℝ), (4438678841383/50000000000000 : ℝ), (2224908458827/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689112941/5000000000 : ℝ)|^5471 ≤ (23312236566937/50000000000000 : ℝ)^4447
        have hw : |(2689112941/5000000000 : ℝ)|=(2689112941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-349198287/2500000000 : ℝ)|^5471 ≤ (4438678841383/50000000000000 : ℝ)^4447
        have hw : |(-349198287/2500000000 : ℝ)|=(349198287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294498341/2500000000 : ℝ)|^5471 ≤ (2224908458827/5000000000000 : ℝ)^4447
        have hw : |(1294498341/2500000000 : ℝ)|=(1294498341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_6 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378225369/10000000000 : ℝ)*x 0 + (517799381/1000000000 : ℝ)*x 1 + (-349198311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378225369/10000000000 : ℝ)^5471 ≤ (46624467662557/100000000000000 : ℝ)^4447 := by
    have hnat : (5378225369 : ℕ)^5471*100000000000000^4447 ≤ 46624467662557^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378225369 10000000000 46624467662557 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517799381/1000000000 : ℝ)^5471 ≤ (44498173891903/100000000000000 : ℝ)^4447 := by
    have hnat : (517799381 : ℕ)^5471*100000000000000^4447 ≤ 44498173891903^4447*1000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517799381 1000000000 44498173891903 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349198311/2500000000 : ℝ)^5471 ≤ (887735843339/10000000000000 : ℝ)^4447 := by
    have hnat : (349198311 : ℕ)^5471*10000000000000^4447 ≤ 887735843339^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349198311 2500000000 887735843339 10000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378225369/10000000000 : ℝ), (517799381/1000000000 : ℝ), (-349198311/2500000000 : ℝ)] ![(46624467662557/100000000000000 : ℝ), (44498173891903/100000000000000 : ℝ), (887735843339/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378225369/10000000000 : ℝ)|^5471 ≤ (46624467662557/100000000000000 : ℝ)^4447
        have hw : |(5378225369/10000000000 : ℝ)|=(5378225369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517799381/1000000000 : ℝ)|^5471 ≤ (44498173891903/100000000000000 : ℝ)^4447
        have hw : |(517799381/1000000000 : ℝ)|=(517799381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-349198311/2500000000 : ℝ)|^5471 ≤ (887735843339/10000000000000 : ℝ)^4447
        have hw : |(-349198311/2500000000 : ℝ)|=(349198311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_7 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3682044659/10000000000 : ℝ)*x 0 + (4296851641/10000000000 : ℝ)*x 1 + (134276621/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3682044659/10000000000 : ℝ)^5471 ≤ (29253202715671/100000000000000 : ℝ)^4447 := by
    have hnat : (3682044659 : ℕ)^5471*100000000000000^4447 ≤ 29253202715671^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3682044659 10000000000 29253202715671 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4296851641/10000000000 : ℝ)^5471 ≤ (4421674682437/12500000000000 : ℝ)^4447 := by
    have hnat : (4296851641 : ℕ)^5471*12500000000000^4447 ≤ 4421674682437^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296851641 10000000000 4421674682437 12500000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134276621/312500000 : ℝ)^5471 ≤ (35373399799077/100000000000000 : ℝ)^4447 := by
    have hnat : (134276621 : ℕ)^5471*100000000000000^4447 ≤ 35373399799077^4447*312500000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134276621 312500000 35373399799077 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3682044659/10000000000 : ℝ), (4296851641/10000000000 : ℝ), (134276621/312500000 : ℝ)] ![(29253202715671/100000000000000 : ℝ), (4421674682437/12500000000000 : ℝ), (35373399799077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3682044659/10000000000 : ℝ)|^5471 ≤ (29253202715671/100000000000000 : ℝ)^4447
        have hw : |(3682044659/10000000000 : ℝ)|=(3682044659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4296851641/10000000000 : ℝ)|^5471 ≤ (4421674682437/12500000000000 : ℝ)^4447
        have hw : |(4296851641/10000000000 : ℝ)|=(4296851641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134276621/312500000 : ℝ)|^5471 ≤ (35373399799077/100000000000000 : ℝ)^4447
        have hw : |(134276621/312500000 : ℝ)|=(134276621/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_8 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-382030103/2500000000 : ℝ)*x 0 + (1001687807/2000000000 : ℝ)*x 1 + (2724132261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382030103/2500000000 : ℝ)^5471 ≤ (4957531788253/50000000000000 : ℝ)^4447 := by
    have hnat : (382030103 : ℕ)^5471*50000000000000^4447 ≤ 4957531788253^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382030103 2500000000 4957531788253 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001687807/2000000000 : ℝ)^5471 ≤ (21356180738723/50000000000000 : ℝ)^4447 := by
    have hnat : (1001687807 : ℕ)^5471*50000000000000^4447 ≤ 21356180738723^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001687807 2000000000 21356180738723 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724132261/5000000000 : ℝ)^5471 ≤ (23686287465529/50000000000000 : ℝ)^4447 := by
    have hnat : (2724132261 : ℕ)^5471*50000000000000^4447 ≤ 23686287465529^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724132261 5000000000 23686287465529 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382030103/2500000000 : ℝ), (1001687807/2000000000 : ℝ), (2724132261/5000000000 : ℝ)] ![(4957531788253/50000000000000 : ℝ), (21356180738723/50000000000000 : ℝ), (23686287465529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382030103/2500000000 : ℝ)|^5471 ≤ (4957531788253/50000000000000 : ℝ)^4447
        have hw : |(-382030103/2500000000 : ℝ)|=(382030103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001687807/2000000000 : ℝ)|^5471 ≤ (21356180738723/50000000000000 : ℝ)^4447
        have hw : |(1001687807/2000000000 : ℝ)|=(1001687807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724132261/5000000000 : ℝ)|^5471 ≤ (23686287465529/50000000000000 : ℝ)^4447
        have hw : |(2724132261/5000000000 : ℝ)|=(2724132261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_9 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195858079/10000000000 : ℝ)*x 0 + (-1275713807/10000000000 : ℝ)*x 1 + (5448264493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195858079/10000000000 : ℝ)^5471 ≤ (44687119942649/100000000000000 : ℝ)^4447 := by
    have hnat : (5195858079 : ℕ)^5471*100000000000000^4447 ≤ 44687119942649^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195858079 10000000000 44687119942649 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1275713807/10000000000 : ℝ)^5471 ≤ (1588061084429/20000000000000 : ℝ)^4447 := by
    have hnat : (1275713807 : ℕ)^5471*20000000000000^4447 ≤ 1588061084429^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275713807 10000000000 1588061084429 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448264493/10000000000 : ℝ)^5471 ≤ (1184314365521/2500000000000 : ℝ)^4447 := by
    have hnat : (5448264493 : ℕ)^5471*2500000000000^4447 ≤ 1184314365521^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448264493 10000000000 1184314365521 2500000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195858079/10000000000 : ℝ), (-1275713807/10000000000 : ℝ), (5448264493/10000000000 : ℝ)] ![(44687119942649/100000000000000 : ℝ), (1588061084429/20000000000000 : ℝ), (1184314365521/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195858079/10000000000 : ℝ)|^5471 ≤ (44687119942649/100000000000000 : ℝ)^4447
        have hw : |(5195858079/10000000000 : ℝ)|=(5195858079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1275713807/10000000000 : ℝ)|^5471 ≤ (1588061084429/20000000000000 : ℝ)^4447
        have hw : |(-1275713807/10000000000 : ℝ)|=(1275713807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448264493/10000000000 : ℝ)|^5471 ≤ (1184314365521/2500000000000 : ℝ)^4447
        have hw : |(5448264493/10000000000 : ℝ)|=(5448264493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_10 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (162370563/312500000 : ℝ)*x 0 + (5448264607/10000000000 : ℝ)*x 1 + (-255142747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162370563/312500000 : ℝ)^5471 ≤ (44687119276049/100000000000000 : ℝ)^4447 := by
    have hnat : (162370563 : ℕ)^5471*100000000000000^4447 ≤ 44687119276049^4447*312500000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162370563 312500000 44687119276049 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448264607/10000000000 : ℝ)^5471 ≤ (11843143960079/25000000000000 : ℝ)^4447 := by
    have hnat : (5448264607 : ℕ)^5471*25000000000000^4447 ≤ 11843143960079^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448264607 10000000000 11843143960079 25000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255142747/2000000000 : ℝ)^5471 ≤ (7940304870809/100000000000000 : ℝ)^4447 := by
    have hnat : (255142747 : ℕ)^5471*100000000000000^4447 ≤ 7940304870809^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255142747 2000000000 7940304870809 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162370563/312500000 : ℝ), (5448264607/10000000000 : ℝ), (-255142747/2000000000 : ℝ)] ![(44687119276049/100000000000000 : ℝ), (11843143960079/25000000000000 : ℝ), (7940304870809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162370563/312500000 : ℝ)|^5471 ≤ (44687119276049/100000000000000 : ℝ)^4447
        have hw : |(162370563/312500000 : ℝ)|=(162370563/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448264607/10000000000 : ℝ)|^5471 ≤ (11843143960079/25000000000000 : ℝ)^4447
        have hw : |(5448264607/10000000000 : ℝ)|=(5448264607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255142747/2000000000 : ℝ)|^5471 ≤ (7940304870809/100000000000000 : ℝ)^4447
        have hw : |(-255142747/2000000000 : ℝ)|=(255142747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_11 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4595980727/10000000000 : ℝ)*x 0 + (767633819/2000000000 : ℝ)*x 1 + (3838168833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4595980727/10000000000 : ℝ)^5471 ≤ (38426854704977/100000000000000 : ℝ)^4447 := by
    have hnat : (4595980727 : ℕ)^5471*100000000000000^4447 ≤ 38426854704977^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595980727 10000000000 38426854704977 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (767633819/2000000000 : ℝ)^5471 ≤ (7696643482857/25000000000000 : ℝ)^4447 := by
    have hnat : (767633819 : ℕ)^5471*25000000000000^4447 ≤ 7696643482857^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767633819 2000000000 7696643482857 25000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3838168833/10000000000 : ℝ)^5471 ≤ (15393285672983/50000000000000 : ℝ)^4447 := by
    have hnat : (3838168833 : ℕ)^5471*50000000000000^4447 ≤ 15393285672983^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3838168833 10000000000 15393285672983 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4595980727/10000000000 : ℝ), (767633819/2000000000 : ℝ), (3838168833/10000000000 : ℝ)] ![(38426854704977/100000000000000 : ℝ), (7696643482857/25000000000000 : ℝ), (15393285672983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4595980727/10000000000 : ℝ)|^5471 ≤ (38426854704977/100000000000000 : ℝ)^4447
        have hw : |(4595980727/10000000000 : ℝ)|=(4595980727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(767633819/2000000000 : ℝ)|^5471 ≤ (7696643482857/25000000000000 : ℝ)^4447
        have hw : |(767633819/2000000000 : ℝ)|=(767633819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3838168833/10000000000 : ℝ)|^5471 ≤ (15393285672983/50000000000000 : ℝ)^4447
        have hw : |(3838168833/10000000000 : ℝ)|=(3838168833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_12 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1165523443/10000000000 : ℝ)*x 0 + (2784135439/5000000000 : ℝ)*x 1 + (1288280171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1165523443/10000000000 : ℝ)^5471 ≤ (3552557003369/50000000000000 : ℝ)^4447 := by
    have hnat : (1165523443 : ℕ)^5471*50000000000000^4447 ≤ 3552557003369^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165523443 10000000000 3552557003369 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2784135439/5000000000 : ℝ)^5471 ≤ (24329769566801/50000000000000 : ℝ)^4447 := by
    have hnat : (2784135439 : ℕ)^5471*50000000000000^4447 ≤ 24329769566801^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2784135439 5000000000 24329769566801 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288280171/2500000000 : ℝ)^5471 ≤ (8847069368047/20000000000000 : ℝ)^4447 := by
    have hnat : (1288280171 : ℕ)^5471*20000000000000^4447 ≤ 8847069368047^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288280171 2500000000 8847069368047 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1165523443/10000000000 : ℝ), (2784135439/5000000000 : ℝ), (1288280171/2500000000 : ℝ)] ![(3552557003369/50000000000000 : ℝ), (24329769566801/50000000000000 : ℝ), (8847069368047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1165523443/10000000000 : ℝ)|^5471 ≤ (3552557003369/50000000000000 : ℝ)^4447
        have hw : |(-1165523443/10000000000 : ℝ)|=(1165523443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2784135439/5000000000 : ℝ)|^5471 ≤ (24329769566801/50000000000000 : ℝ)^4447
        have hw : |(2784135439/5000000000 : ℝ)|=(2784135439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1288280171/2500000000 : ℝ)|^5471 ≤ (8847069368047/20000000000000 : ℝ)^4447
        have hw : |(1288280171/2500000000 : ℝ)|=(1288280171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_13 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395044813/10000000000 : ℝ)*x 0 + (-1407447453/10000000000 : ℝ)*x 1 + (1288280153/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395044813/10000000000 : ℝ)^5471 ≤ (11700979298509/25000000000000 : ℝ)^4447 := by
    have hnat : (5395044813 : ℕ)^5471*25000000000000^4447 ≤ 11700979298509^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395044813 10000000000 11700979298509 25000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1407447453/10000000000 : ℝ)^5471 ≤ (8960736709633/100000000000000 : ℝ)^4447 := by
    have hnat : (1407447453 : ℕ)^5471*100000000000000^4447 ≤ 8960736709633^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407447453 10000000000 8960736709633 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288280153/2500000000 : ℝ)^5471 ≤ (22117673039927/50000000000000 : ℝ)^4447 := by
    have hnat : (1288280153 : ℕ)^5471*50000000000000^4447 ≤ 22117673039927^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288280153 2500000000 22117673039927 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395044813/10000000000 : ℝ), (-1407447453/10000000000 : ℝ), (1288280153/2500000000 : ℝ)] ![(11700979298509/25000000000000 : ℝ), (8960736709633/100000000000000 : ℝ), (22117673039927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395044813/10000000000 : ℝ)|^5471 ≤ (11700979298509/25000000000000 : ℝ)^4447
        have hw : |(5395044813/10000000000 : ℝ)|=(5395044813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1407447453/10000000000 : ℝ)|^5471 ≤ (8960736709633/100000000000000 : ℝ)^4447
        have hw : |(-1407447453/10000000000 : ℝ)|=(1407447453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1288280153/2500000000 : ℝ)|^5471 ≤ (22117673039927/50000000000000 : ℝ)^4447
        have hw : |(1288280153/2500000000 : ℝ)|=(1288280153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_14 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697522559/5000000000 : ℝ)*x 0 + (5153120329/10000000000 : ℝ)*x 1 + (-70372371/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697522559/5000000000 : ℝ)^5471 ≤ (46803920449303/100000000000000 : ℝ)^4447 := by
    have hnat : (2697522559 : ℕ)^5471*100000000000000^4447 ≤ 46803920449303^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697522559 5000000000 46803920449303 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5153120329/10000000000 : ℝ)^5471 ≤ (22117671545567/50000000000000 : ℝ)^4447 := by
    have hnat : (5153120329 : ℕ)^5471*50000000000000^4447 ≤ 22117671545567^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153120329 10000000000 22117671545567 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70372371/500000000 : ℝ)^5471 ≤ (4480368225577/50000000000000 : ℝ)^4447 := by
    have hnat : (70372371 : ℕ)^5471*50000000000000^4447 ≤ 4480368225577^4447*500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70372371 500000000 4480368225577 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697522559/5000000000 : ℝ), (5153120329/10000000000 : ℝ), (-70372371/500000000 : ℝ)] ![(46803920449303/100000000000000 : ℝ), (22117671545567/50000000000000 : ℝ), (4480368225577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697522559/5000000000 : ℝ)|^5471 ≤ (46803920449303/100000000000000 : ℝ)^4447
        have hw : |(2697522559/5000000000 : ℝ)|=(2697522559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5153120329/10000000000 : ℝ)|^5471 ≤ (22117671545567/50000000000000 : ℝ)^4447
        have hw : |(5153120329/10000000000 : ℝ)|=(5153120329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-70372371/500000000 : ℝ)|^5471 ≤ (4480368225577/50000000000000 : ℝ)^4447
        have hw : |(-70372371/500000000 : ℝ)|=(70372371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_box_15 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3594499851/10000000000 : ℝ)*x 0 + (2169465897/5000000000 : ℝ)*x 1 + (2169465531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3594499851/10000000000 : ℝ)^5471 ≤ (28399873696733/100000000000000 : ℝ)^4447 := by
    have hnat : (3594499851 : ℕ)^5471*100000000000000^4447 ≤ 28399873696733^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3594499851 10000000000 28399873696733 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169465897/5000000000 : ℝ)^5471 ≤ (17900033427661/50000000000000 : ℝ)^4447 := by
    have hnat : (2169465897 : ℕ)^5471*50000000000000^4447 ≤ 17900033427661^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169465897 5000000000 17900033427661 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2169465531/5000000000 : ℝ)^5471 ≤ (35800059424931/100000000000000 : ℝ)^4447 := by
    have hnat : (2169465531 : ℕ)^5471*100000000000000^4447 ≤ 35800059424931^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169465531 5000000000 35800059424931 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3594499851/10000000000 : ℝ), (2169465897/5000000000 : ℝ), (2169465531/5000000000 : ℝ)] ![(28399873696733/100000000000000 : ℝ), (17900033427661/50000000000000 : ℝ), (35800059424931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3594499851/10000000000 : ℝ)|^5471 ≤ (28399873696733/100000000000000 : ℝ)^4447
        have hw : |(3594499851/10000000000 : ℝ)|=(3594499851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2169465897/5000000000 : ℝ)|^5471 ≤ (17900033427661/50000000000000 : ℝ)^4447
        have hw : |(2169465897/5000000000 : ℝ)|=(2169465897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2169465531/5000000000 : ℝ)|^5471 ≤ (35800059424931/100000000000000 : ℝ)^4447
        have hw : |(2169465531/5000000000 : ℝ)|=(2169465531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1731_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8471/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(33477/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58891/100000 : ℝ) ∧ (10267/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45357/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8471/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10161/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8471/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10161/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8471/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10161/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8471/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10161/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8471/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10161/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8471/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10161/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10161/100000 : ℝ) ^ (5463/1024 : ℝ) ≤ (251776251803781/50000000000000000000 : ℝ) := by
    have hpowers : (10161/100000 : ℝ)^5463 ≤ (251776251803781/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10161 : ℕ)^5463*50000000000000000000^1024 ≤ 251776251803781^1024*100000^5463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10161 100000 251776251803781 50000000000000000000 5463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10161/100000 : ℝ)) (X := (251776251803781/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8471/50000 : ℝ) ^ (5463/1024 : ℝ) ≤ (7701169329067197/100000000000000000000 : ℝ) := by
    have hpowers : (8471/50000 : ℝ)^5463 ≤ (7701169329067197/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8471 : ℕ)^5463*100000000000000000000^1024 ≤ 7701169329067197^1024*50000^5463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8471 50000 7701169329067197 100000000000000000000 5463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8471/50000 : ℝ)) (X := (7701169329067197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000251776251803781/25000000000000000000 : ℝ) ≤ (10000018877380703/10000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (25000251776251803781/25000000000000000000 : ℝ)^1024 ≤ (10000018877380703/10000000000000000 : ℝ)^5463 := by
      have hnat : (25000251776251803781 : ℕ)^1024*10000000000000000^5463 ≤ 10000018877380703^5463*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000251776251803781 25000000000000000000 10000018877380703 10000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000018877380703/10000000000000000 : ℝ)) (X := (25000251776251803781/25000000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008204721832674759/100000000000000000000 : ℝ) ≤ (2500038446618663/2500000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (100008204721832674759/100000000000000000000 : ℝ)^1024 ≤ (2500038446618663/2500000000000000 : ℝ)^5463 := by
      have hnat : (100008204721832674759 : ℕ)^1024*2500000000000000^5463 ≤ 2500038446618663^5463*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008204721832674759 100000000000000000000 2500038446618663 2500000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500038446618663/2500000000000000 : ℝ)) (X := (100008204721832674759/100000000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50007701169329067197/50000000000000000000 : ℝ) ≤ (10000288695568601/10000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (50007701169329067197/50000000000000000000 : ℝ)^1024 ≤ (10000288695568601/10000000000000000 : ℝ)^5463 := by
      have hnat : (50007701169329067197 : ℕ)^1024*10000000000000000^5463 ≤ 10000288695568601^5463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007701169329067197 50000000000000000000 10000288695568601 10000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000288695568601/10000000000000000 : ℝ)) (X := (50007701169329067197/50000000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(251776251803781/50000000000000000000 : ℝ) ≤ ((13561477276982263093/13562000000000000000 : ℝ)+2*(134909093949/678100000000000 : ℝ)*(10161/100000 : ℝ))^(5463/1024 : ℝ) := by
    rw [show (13561477276982263093/13562000000000000000 : ℝ)+2*(134909093949/678100000000000 : ℝ)*(10161/100000 : ℝ)=(10000018877380703/10000000000000000 : ℝ) by norm_num, show 1+2*(251776251803781/50000000000000000000 : ℝ)=(25000251776251803781/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7701169329067197/100000000000000000000 : ℝ)+(251776251803781/50000000000000000000 : ℝ) ≤ ((13561477276982263093/13562000000000000000 : ℝ)+(134909093949/678100000000000 : ℝ)*((8471/50000 : ℝ)+(10161/100000 : ℝ)))^(5463/1024 : ℝ) := by
    rw [show (13561477276982263093/13562000000000000000 : ℝ)+(134909093949/678100000000000 : ℝ)*((8471/50000 : ℝ)+(10161/100000 : ℝ))=(2500038446618663/2500000000000000 : ℝ) by norm_num, show 1+(7701169329067197/100000000000000000000 : ℝ)+(251776251803781/50000000000000000000 : ℝ)=(100008204721832674759/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7701169329067197/100000000000000000000 : ℝ) ≤ ((13561477276982263093/13562000000000000000 : ℝ)+2*(134909093949/678100000000000 : ℝ)*(8471/50000 : ℝ))^(5463/1024 : ℝ) := by
    rw [show (13561477276982263093/13562000000000000000 : ℝ)+2*(134909093949/678100000000000 : ℝ)*(8471/50000 : ℝ)=(10000288695568601/10000000000000000 : ℝ) by norm_num, show 1+2*(7701169329067197/100000000000000000000 : ℝ)=(50007701169329067197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13561477276982263093/13562000000000000000 : ℝ)*(X 1 0+X 2 0)+(134909093949/678100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (10161/100000 : ℝ)) (hi := (8471/50000 : ℝ)) (c := (13561477276982263093/13562000000000000000 : ℝ)) (alpha := (134909093949/678100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13561477276982263093/13562000000000000000 : ℝ)*(X 0 1+X 2 1)+(134909093949/678100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (10161/100000 : ℝ)) (hi := (8471/50000 : ℝ)) (c := (13561477276982263093/13562000000000000000 : ℝ)) (alpha := (134909093949/678100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13561477276982263093/13562000000000000000 : ℝ)*(X 0 2+X 1 2)+(134909093949/678100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (10161/100000 : ℝ)) (hi := (8471/50000 : ℝ)) (c := (13561477276982263093/13562000000000000000 : ℝ)) (alpha := (134909093949/678100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-129561839/1250000000 : ℝ)*X 0 0+(1351595239/2500000000 : ℝ)*X 0 1+(5406380821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612049039/5000000000 : ℝ)*X 1 0+(-129509259/1000000000 : ℝ)*X 1 1+(2703190213/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1044819559/2000000000 : ℝ)*X 2 0+(5406380723/10000000000 : ℝ)*X 2 1+(-1295092567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4458524319/10000000000 : ℝ)*X 0 0+(3909408467/10000000000 : ℝ)*X 0 1+(1954704411/5000000000 : ℝ)*X 0 2+(4458524319/10000000000 : ℝ)*X 1 0+(3909408467/10000000000 : ℝ)*X 1 1+(1954704411/5000000000 : ℝ)*X 1 2+(4458524319/10000000000 : ℝ)*X 2 0+(3909408467/10000000000 : ℝ)*X 2 1+(1954704411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1663149333/10000000000 : ℝ)*X 0 0+(517799351/1000000000 : ℝ)*X 0 1+(2588996933/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2689112941/5000000000 : ℝ)*X 1 0+(-349198287/2500000000 : ℝ)*X 1 1+(1294498341/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5378225369/10000000000 : ℝ)*X 2 0+(517799381/1000000000 : ℝ)*X 2 1+(-349198311/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3682044659/10000000000 : ℝ)*X 0 0+(4296851641/10000000000 : ℝ)*X 0 1+(134276621/312500000 : ℝ)*X 0 2+(3682044659/10000000000 : ℝ)*X 1 0+(4296851641/10000000000 : ℝ)*X 1 1+(134276621/312500000 : ℝ)*X 1 2+(3682044659/10000000000 : ℝ)*X 2 0+(4296851641/10000000000 : ℝ)*X 2 1+(134276621/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-382030103/2500000000 : ℝ)*X 0 0+(1001687807/2000000000 : ℝ)*X 0 1+(2724132261/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5195858079/10000000000 : ℝ)*X 1 0+(-1275713807/10000000000 : ℝ)*X 1 1+(5448264493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((162370563/312500000 : ℝ)*X 2 0+(5448264607/10000000000 : ℝ)*X 2 1+(-255142747/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4595980727/10000000000 : ℝ)*X 0 0+(767633819/2000000000 : ℝ)*X 0 1+(3838168833/10000000000 : ℝ)*X 0 2+(4595980727/10000000000 : ℝ)*X 1 0+(767633819/2000000000 : ℝ)*X 1 1+(3838168833/10000000000 : ℝ)*X 1 2+(4595980727/10000000000 : ℝ)*X 2 0+(767633819/2000000000 : ℝ)*X 2 1+(3838168833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1165523443/10000000000 : ℝ)*X 0 0+(2784135439/5000000000 : ℝ)*X 0 1+(1288280171/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5395044813/10000000000 : ℝ)*X 1 0+(-1407447453/10000000000 : ℝ)*X 1 1+(1288280153/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2697522559/5000000000 : ℝ)*X 2 0+(5153120329/10000000000 : ℝ)*X 2 1+(-70372371/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3594499851/10000000000 : ℝ)*X 0 0+(2169465897/5000000000 : ℝ)*X 0 1+(2169465531/5000000000 : ℝ)*X 0 2+(3594499851/10000000000 : ℝ)*X 1 0+(2169465897/5000000000 : ℝ)*X 1 1+(2169465531/5000000000 : ℝ)*X 1 2+(3594499851/10000000000 : ℝ)*X 2 0+(2169465897/5000000000 : ℝ)*X 2 1+(2169465531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-33477/50000 : ℝ) ≤ (-22699850852659256228454913263/33905000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12362957/50000000000000 : ℝ)*(lower0) + (74831/20000000000000 : ℝ)*(upper1) + (19663297/25000000000000 : ℝ)*(lower4) + (704728595460343/50000000000000 : ℝ)*(major0) + (704728595460343/50000000000000 : ℝ)*(major1) + (704728595460343/50000000000000 : ℝ)*(major2) + (177241831/4000000000000 : ℝ)*(sp1) + (2400651739/100000000000000 : ℝ)*(sp2) + (81875129/6250000000000 : ℝ)*(sp3) + (1071609514560971/50000000000000 : ℝ)*(sp4) + (1071608508414809/50000000000000 : ℝ)*(sp5) + (1071609523611827/50000000000000 : ℝ)*(sp6) + (69800873633933/10000000000000 : ℝ)*(sp7) + (48375069/2000000000000 : ℝ)*(sp12) + (349005023170697/50000000000000 : ℝ)*(f.failure) + (2143221447875393/100000000000000 : ℝ)*(f.sum) + (15426116103691/8476250000000000000000000000 : ℝ)*base65 + (1067458932593639101/678100000000000000000000000000000 : ℝ)*base68 + (401536220050160899/678100000000000000000000000000000 : ℝ)*base69 + (2626840395586960899/678100000000000000000000000000000 : ℝ)*base71 + (167085358747553/16952500000000000000000000000 : ℝ)*base74 + (5877186654042839101/678100000000000000000000000000000 : ℝ)*base76 + (312349268766460899/678100000000000000000000000000000 : ℝ)*base77 + (7232732955471339101/678100000000000000000000000000000 : ℝ)*base80 + (110586401362981/33905000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (17812713/2500000000000000000000 : ℝ)*base89 + (17812713/2500000000000000000000 : ℝ)*base91 + (17812713/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58891/100000 : ℝ) ≤ (399356782797819575131908138058143/678100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62107407/100000000000000 : ℝ)*(lower1) + (15981/2500000000000 : ℝ)*(lower3) + (37424201/50000000000000 : ℝ)*(lower5) + (1520380252012383/100000000000000 : ℝ)*(major0) + (1520380252012383/100000000000000 : ℝ)*(major1) + (1520380252012383/100000000000000 : ℝ)*(major2) + (226818463104243/10000000000000 : ℝ)*(sp0) + (113408089001929/5000000000000 : ℝ)*(sp1) + (2268184510079837/100000000000000 : ℝ)*(sp2) + (376470948198537/50000000000000 : ℝ)*(sp3) + (468244583/50000000000000 : ℝ)*(sp7) + (3090804259/12500000000000 : ℝ)*(sp9) + (399278563/20000000000000 : ℝ)*(sp10) + (937715111/50000000000000 : ℝ)*(sp12) + (4705892705539/625000000000 : ℝ)*(f.failure) + (567046626618163/25000000000000 : ℝ)*(f.sum) + (15984452088603/33905000000000000000000000000 : ℝ)*base66 + (5688672144542779381/1356200000000000000000000000000000 : ℝ)*base68 + (3302028594669620619/1356200000000000000000000000000000 : ℝ)*base69 + (784960087055620619/1356200000000000000000000000000000 : ℝ)*base71 + (138073311266833/33905000000000000000000000000 : ℝ)*base74 + (8396331201442020619/1356200000000000000000000000000000 : ℝ)*base75 + (456356180938220619/1356200000000000000000000000000000 : ℝ)*base77 + (1237275011274779381/1356200000000000000000000000000000 : ℝ)*base80 + (203633914584187/33905000000000000000000000000 : ℝ)*base81 + (60631/31250000000000000000 : ℝ)*base89 + (60631/31250000000000000000 : ℝ)*base91 + (60631/31250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (10267/12500 : ℝ) ≤ (139246044496808376371378798432559/169525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (985311/25000000000000 : ℝ)*(upper1) + (167743/20000000000000 : ℝ)*(upper3) + (14143217/100000000000000 : ℝ)*(upper4) + (3645087/20000000000000 : ℝ)*(lower5) + (382286744452893/25000000000000 : ℝ)*(major0) + (382286744452893/25000000000000 : ℝ)*(major1) + (382286744452893/25000000000000 : ℝ)*(major2) + (833497877/100000000000000 : ℝ)*(sp0) + (5040245729/50000000000000 : ℝ)*(sp2) + (552753827/25000000000000 : ℝ)*(sp3) + (2273629067310907/100000000000000 : ℝ)*(sp8) + (142101868800549/6250000000000 : ℝ)*(sp9) + (1136809910158663/50000000000000 : ℝ)*(sp10) + (757282195861807/100000000000000 : ℝ)*(sp11) + (189321101719279/25000000000000 : ℝ)*(f.failure) + (142101868800549/6250000000000 : ℝ)*(f.sum) + (40465412105037/33905000000000000000000000000 : ℝ)*base66 + (419876635465218049/339050000000000000000000000000000 : ℝ)*base67 + (3898796054174218049/339050000000000000000000000000000 : ℝ)*base69 + (278803959113268049/339050000000000000000000000000000 : ℝ)*base71 + (55667667516937/33905000000000000000000000000 : ℝ)*base74 + (4325677620873168049/339050000000000000000000000000000 : ℝ)*base75 + (1216496103183768049/339050000000000000000000000000000 : ℝ)*base77 + (1954837405271268049/339050000000000000000000000000000 : ℝ)*base79 + (215204249699373/33905000000000000000000000000 : ℝ)*base81 + (5896591/1250000000000000000000 : ℝ)*base89 + (5896591/1250000000000000000000 : ℝ)*base91 + (5896591/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-45357/50000 : ℝ) ≤ (-76889481319185261292861251329037/84762500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15802803/20000000000000 : ℝ)*(lower0) + (462811/1000000000000 : ℝ)*(lower1) + (47227909/100000000000000 : ℝ)*(lower2) + (197582880980101/12500000000000 : ℝ)*(major0) + (197582880980101/12500000000000 : ℝ)*(major1) + (197582880980101/12500000000000 : ℝ)*(major2) + (71817481/6250000000000 : ℝ)*(sp0) + (3728008323/10000000000000 : ℝ)*(sp5) + (3304916389/6250000000000 : ℝ)*(sp6) + (3812205891/100000000000000 : ℝ)*(sp7) + (301095661720901/12500000000000 : ℝ)*(sp12) + (1204364581381837/50000000000000 : ℝ)*(sp13) + (60217839104617/2500000000000 : ℝ)*(sp14) + (782793064762597/100000000000000 : ℝ)*(sp15) + (97849609621061/12500000000000 : ℝ)*(f.failure) + (301095805355863/12500000000000 : ℝ)*(f.sum) + (2676399073137/2119062500000000000000000000 : ℝ)*base65 + (956962141197467393/169525000000000000000000000000000 : ℝ)*base67 + (895824220537342393/169525000000000000000000000000000 : ℝ)*base69 + (490755356589742393/169525000000000000000000000000000 : ℝ)*base71 + (189767992087443/33905000000000000000000000000 : ℝ)*base74 + (963414936559342393/169525000000000000000000000000000 : ℝ)*base75 + (1079944397769892393/169525000000000000000000000000000 : ℝ)*base77 + (419100822698467393/169525000000000000000000000000000 : ℝ)*base79 + (38068199563379/16952500000000000000000000000 : ℝ)*base82 + (223269/625000000000000000000 : ℝ)*base89 + (223269/625000000000000000000 : ℝ)*base91 + (223269/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1731_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8471/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33477/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58891/100000 : ℝ) else (10267/12500 : ℝ) ≤ X j i ∧ X j i ≤ (45357/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1731_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1731_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2539/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33477/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58891/100000 : ℝ) else (10267/12500 : ℝ) ≤ X j i ∧ X j i ≤ (45357/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1731_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1731_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2539/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33477/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58891/100000 : ℝ) else (10267/12500 : ℝ) ≤ X j i ∧ X j i ≤ (45357/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1731_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
