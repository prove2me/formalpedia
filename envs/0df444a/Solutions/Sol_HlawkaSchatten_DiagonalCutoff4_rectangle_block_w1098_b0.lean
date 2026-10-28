-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1098_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:59:34.45799+00:00
-- url     : https://prove2.me/submissions/ca920b3d-4591-45ff-a697-96002cdf40fb

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
theorem support_rectangle_w1098_s0_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2382269/12500000 : ℝ)*x 0 + (1212911133/2000000000 : ℝ)*x 1 + (190995297/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2382269/12500000 : ℝ)^8291 ≤ (11064025058237/100000000000000 : ℝ)^6243 := by
    have hnat : (2382269 : ℕ)^8291*100000000000000^6243 ≤ 11064025058237^6243*12500000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2382269 12500000 11064025058237 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212911133/2000000000 : ℝ)^8291 ≤ (51469121568747/100000000000000 : ℝ)^6243 := by
    have hnat : (1212911133 : ℕ)^8291*100000000000000^6243 ≤ 51469121568747^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212911133 2000000000 51469121568747 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190995297/400000000 : ℝ)^8291 ≤ (37466853355139/100000000000000 : ℝ)^6243 := by
    have hnat : (190995297 : ℕ)^8291*100000000000000^6243 ≤ 37466853355139^6243*400000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190995297 400000000 37466853355139 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2382269/12500000 : ℝ), (1212911133/2000000000 : ℝ), (190995297/400000000 : ℝ)] ![(11064025058237/100000000000000 : ℝ), (51469121568747/100000000000000 : ℝ), (37466853355139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2382269/12500000 : ℝ)|^8291 ≤ (11064025058237/100000000000000 : ℝ)^6243
        have hw : |(-2382269/12500000 : ℝ)|=(2382269/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1212911133/2000000000 : ℝ)|^8291 ≤ (51469121568747/100000000000000 : ℝ)^6243
        have hw : |(1212911133/2000000000 : ℝ)|=(1212911133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190995297/400000000 : ℝ)|^8291 ≤ (37466853355139/100000000000000 : ℝ)^6243
        have hw : |(190995297/400000000 : ℝ)|=(190995297/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s0_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2759635859/5000000000 : ℝ)*x 0 + (-529443257/2000000000 : ℝ)*x 1 + (954976493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759635859/5000000000 : ℝ)^8291 ≤ (9083155621331/20000000000000 : ℝ)^6243 := by
    have hnat : (2759635859 : ℕ)^8291*20000000000000^6243 ≤ 9083155621331^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759635859 5000000000 9083155621331 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529443257/2000000000 : ℝ)^8291 ≤ (4279342026127/25000000000000 : ℝ)^6243 := by
    have hnat : (529443257 : ℕ)^8291*25000000000000^6243 ≤ 4279342026127^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529443257 2000000000 4279342026127 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954976493/2000000000 : ℝ)^8291 ≤ (585419590187/1562500000000 : ℝ)^6243 := by
    have hnat : (954976493 : ℕ)^8291*1562500000000^6243 ≤ 585419590187^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954976493 2000000000 585419590187 1562500000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759635859/5000000000 : ℝ), (-529443257/2000000000 : ℝ), (954976493/2000000000 : ℝ)] ![(9083155621331/20000000000000 : ℝ), (4279342026127/25000000000000 : ℝ), (585419590187/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759635859/5000000000 : ℝ)|^8291 ≤ (9083155621331/20000000000000 : ℝ)^6243
        have hw : |(2759635859/5000000000 : ℝ)|=(2759635859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529443257/2000000000 : ℝ)|^8291 ≤ (4279342026127/25000000000000 : ℝ)^6243
        have hw : |(-529443257/2000000000 : ℝ)|=(529443257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(954976493/2000000000 : ℝ)|^8291 ≤ (585419590187/1562500000000 : ℝ)^6243
        have hw : |(954976493/2000000000 : ℝ)|=(954976493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s0_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (220770879/400000000 : ℝ)*x 0 + (4774882351/10000000000 : ℝ)*x 1 + (-2647216097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220770879/400000000 : ℝ)^8291 ≤ (22707890457569/50000000000000 : ℝ)^6243 := by
    have hnat : (220770879 : ℕ)^8291*50000000000000^6243 ≤ 22707890457569^6243*400000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220770879 400000000 22707890457569 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4774882351/10000000000 : ℝ)^8291 ≤ (7493370516801/20000000000000 : ℝ)^6243 := by
    have hnat : (4774882351 : ℕ)^8291*20000000000000^6243 ≤ 7493370516801^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774882351 10000000000 7493370516801 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2647216097/10000000000 : ℝ)^8291 ≤ (17117366490079/100000000000000 : ℝ)^6243 := by
    have hnat : (2647216097 : ℕ)^8291*100000000000000^6243 ≤ 17117366490079^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647216097 10000000000 17117366490079 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220770879/400000000 : ℝ), (4774882351/10000000000 : ℝ), (-2647216097/10000000000 : ℝ)] ![(22707890457569/50000000000000 : ℝ), (7493370516801/20000000000000 : ℝ), (17117366490079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220770879/400000000 : ℝ)|^8291 ≤ (22707890457569/50000000000000 : ℝ)^6243
        have hw : |(220770879/400000000 : ℝ)|=(220770879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4774882351/10000000000 : ℝ)|^8291 ≤ (7493370516801/20000000000000 : ℝ)^6243
        have hw : |(4774882351/10000000000 : ℝ)|=(4774882351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2647216097/10000000000 : ℝ)|^8291 ≤ (17117366490079/100000000000000 : ℝ)^6243
        have hw : |(-2647216097/10000000000 : ℝ)|=(2647216097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s0_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1051143347/2500000000 : ℝ)*x 0 + (3123205763/10000000000 : ℝ)*x 1 + (566685279/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051143347/2500000000 : ℝ)^8291 ≤ (3955440947257/12500000000000 : ℝ)^6243 := by
    have hnat : (1051143347 : ℕ)^8291*12500000000000^6243 ≤ 3955440947257^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051143347 2500000000 3955440947257 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123205763/10000000000 : ℝ)^8291 ≤ (5330226196777/25000000000000 : ℝ)^6243 := by
    have hnat : (3123205763 : ℕ)^8291*25000000000000^6243 ≤ 5330226196777^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123205763 10000000000 5330226196777 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566685279/1000000000 : ℝ)^8291 ≤ (47035567627899/100000000000000 : ℝ)^6243 := by
    have hnat : (566685279 : ℕ)^8291*100000000000000^6243 ≤ 47035567627899^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566685279 1000000000 47035567627899 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051143347/2500000000 : ℝ), (3123205763/10000000000 : ℝ), (566685279/1000000000 : ℝ)] ![(3955440947257/12500000000000 : ℝ), (5330226196777/25000000000000 : ℝ), (47035567627899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051143347/2500000000 : ℝ)|^8291 ≤ (3955440947257/12500000000000 : ℝ)^6243
        have hw : |(1051143347/2500000000 : ℝ)|=(1051143347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3123205763/10000000000 : ℝ)|^8291 ≤ (5330226196777/25000000000000 : ℝ)^6243
        have hw : |(3123205763/10000000000 : ℝ)|=(3123205763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566685279/1000000000 : ℝ)|^8291 ≤ (47035567627899/100000000000000 : ℝ)^6243
        have hw : |(566685279/1000000000 : ℝ)|=(566685279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s0_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-955546163/5000000000 : ℝ)*x 0 + (1202042977/2500000000 : ℝ)*x 1 + (60300987/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955546163/5000000000 : ℝ)^8291 ≤ (11104729376669/100000000000000 : ℝ)^6243 := by
    have hnat : (955546163 : ℕ)^8291*100000000000000^6243 ≤ 11104729376669^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955546163 5000000000 11104729376669 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1202042977/2500000000 : ℝ)^8291 ≤ (7562830025243/20000000000000 : ℝ)^6243 := by
    have hnat : (1202042977 : ℕ)^8291*20000000000000^6243 ≤ 7562830025243^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202042977 2500000000 7562830025243 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60300987/100000000 : ℝ)^8291 ≤ (51081120490391/100000000000000 : ℝ)^6243 := by
    have hnat : (60300987 : ℕ)^8291*100000000000000^6243 ≤ 51081120490391^6243*100000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60300987 100000000 51081120490391 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955546163/5000000000 : ℝ), (1202042977/2500000000 : ℝ), (60300987/100000000 : ℝ)] ![(11104729376669/100000000000000 : ℝ), (7562830025243/20000000000000 : ℝ), (51081120490391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955546163/5000000000 : ℝ)|^8291 ≤ (11104729376669/100000000000000 : ℝ)^6243
        have hw : |(-955546163/5000000000 : ℝ)|=(955546163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1202042977/2500000000 : ℝ)|^8291 ≤ (7562830025243/20000000000000 : ℝ)^6243
        have hw : |(1202042977/2500000000 : ℝ)|=(1202042977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(60300987/100000000 : ℝ)|^8291 ≤ (51081120490391/100000000000000 : ℝ)^6243
        have hw : |(60300987/100000000 : ℝ)|=(60300987/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s0_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (516906219/1000000000 : ℝ)*x 0 + (-696000801/5000000000 : ℝ)*x 1 + (1507524773/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516906219/1000000000 : ℝ)^8291 ≤ (5203639942727/12500000000000 : ℝ)^6243 := by
    have hnat : (516906219 : ℕ)^8291*12500000000000^6243 ≤ 5203639942727^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516906219 1000000000 5203639942727 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (696000801/5000000000 : ℝ)^8291 ≤ (1822438888717/25000000000000 : ℝ)^6243 := by
    have hnat : (696000801 : ℕ)^8291*25000000000000^6243 ≤ 1822438888717^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696000801 5000000000 1822438888717 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1507524773/2500000000 : ℝ)^8291 ≤ (51081124900361/100000000000000 : ℝ)^6243 := by
    have hnat : (1507524773 : ℕ)^8291*100000000000000^6243 ≤ 51081124900361^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507524773 2500000000 51081124900361 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516906219/1000000000 : ℝ), (-696000801/5000000000 : ℝ), (1507524773/2500000000 : ℝ)] ![(5203639942727/12500000000000 : ℝ), (1822438888717/25000000000000 : ℝ), (51081124900361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516906219/1000000000 : ℝ)|^8291 ≤ (5203639942727/12500000000000 : ℝ)^6243
        have hw : |(516906219/1000000000 : ℝ)|=(516906219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-696000801/5000000000 : ℝ)|^8291 ≤ (1822438888717/25000000000000 : ℝ)^6243
        have hw : |(-696000801/5000000000 : ℝ)|=(696000801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1507524773/2500000000 : ℝ)|^8291 ≤ (51081124900361/100000000000000 : ℝ)^6243
        have hw : |(1507524773/2500000000 : ℝ)|=(1507524773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s0_6 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2584531697/5000000000 : ℝ)*x 0 + (6030099073/10000000000 : ℝ)*x 1 + (-69599989/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584531697/5000000000 : ℝ)^8291 ≤ (20814566209569/50000000000000 : ℝ)^6243 := by
    have hnat : (2584531697 : ℕ)^8291*50000000000000^6243 ≤ 20814566209569^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584531697 5000000000 20814566209569 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6030099073/10000000000 : ℝ)^8291 ≤ (51081124686613/100000000000000 : ℝ)^6243 := by
    have hnat : (6030099073 : ℕ)^8291*100000000000000^6243 ≤ 51081124686613^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6030099073 10000000000 51081124686613 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69599989/500000000 : ℝ)^8291 ≤ (3644871441581/50000000000000 : ℝ)^6243 := by
    have hnat : (69599989 : ℕ)^8291*50000000000000^6243 ≤ 3644871441581^6243*500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69599989 500000000 3644871441581 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584531697/5000000000 : ℝ), (6030099073/10000000000 : ℝ), (-69599989/500000000 : ℝ)] ![(20814566209569/50000000000000 : ℝ), (51081124686613/100000000000000 : ℝ), (3644871441581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584531697/5000000000 : ℝ)|^8291 ≤ (20814566209569/50000000000000 : ℝ)^6243
        have hw : |(2584531697/5000000000 : ℝ)|=(2584531697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6030099073/10000000000 : ℝ)|^8291 ≤ (51081124686613/100000000000000 : ℝ)^6243
        have hw : |(6030099073/10000000000 : ℝ)|=(6030099073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69599989/500000000 : ℝ)|^8291 ≤ (3644871441581/50000000000000 : ℝ)^6243
        have hw : |(-69599989/500000000 : ℝ)|=(69599989/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s0_7 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1053744697/2500000000 : ℝ)*x 0 + (1400298959/2500000000 : ℝ)*x 1 + (3191165119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053744697/2500000000 : ℝ)^8291 ≤ (634951404879/2000000000000 : ℝ)^6243 := by
    have hnat : (1053744697 : ℕ)^8291*2000000000000^6243 ≤ 634951404879^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053744697 2500000000 634951404879 2000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400298959/2500000000 : ℝ)^8291 ≤ (23156606471379/50000000000000 : ℝ)^6243 := by
    have hnat : (1400298959 : ℕ)^8291*50000000000000^6243 ≤ 23156606471379^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400298959 2500000000 23156606471379 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3191165119/10000000000 : ℝ)^8291 ≤ (10969608394787/50000000000000 : ℝ)^6243 := by
    have hnat : (3191165119 : ℕ)^8291*50000000000000^6243 ≤ 10969608394787^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3191165119 10000000000 10969608394787 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053744697/2500000000 : ℝ), (1400298959/2500000000 : ℝ), (3191165119/10000000000 : ℝ)] ![(634951404879/2000000000000 : ℝ), (23156606471379/50000000000000 : ℝ), (10969608394787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053744697/2500000000 : ℝ)|^8291 ≤ (634951404879/2000000000000 : ℝ)^6243
        have hw : |(1053744697/2500000000 : ℝ)|=(1053744697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1400298959/2500000000 : ℝ)|^8291 ≤ (23156606471379/50000000000000 : ℝ)^6243
        have hw : |(1400298959/2500000000 : ℝ)|=(1400298959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3191165119/10000000000 : ℝ)|^8291 ≤ (10969608394787/50000000000000 : ℝ)^6243
        have hw : |(3191165119/10000000000 : ℝ)|=(3191165119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (231/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5597/20000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4145/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4145 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4145*1^1024 ≤ 0^1024*1^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4145/1024 : ℝ) ≤ (2450179568820734951/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4145 ≤ (2450179568820734951/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4145*100000000000000000000^1024 ≤ 2450179568820734951^1024*5^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2450179568820734951 100000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2450179568820734951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4145 := by
      have hnat : (1 : ℕ)^1024*1^4145 ≤ 1^4145*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102450179568820734951/100000000000000000000 : ℝ) ≤ (10059979877428961/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (102450179568820734951/100000000000000000000 : ℝ)^1024 ≤ (10059979877428961/10000000000000000 : ℝ)^4145 := by
      have hnat : (102450179568820734951 : ℕ)^1024*10000000000000000^4145 ≤ 10059979877428961^4145*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102450179568820734951 100000000000000000000 10059979877428961 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059979877428961/10000000000000000 : ℝ)) (X := (102450179568820734951/100000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52450179568820734951/50000000000000000000 : ℝ) ≤ (5059979877428961/5000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (52450179568820734951/50000000000000000000 : ℝ)^1024 ≤ (5059979877428961/5000000000000000 : ℝ)^4145 := by
      have hnat : (52450179568820734951 : ℕ)^1024*5000000000000000^4145 ≤ 5059979877428961^4145*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52450179568820734951 50000000000000000000 5059979877428961 5000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059979877428961/5000000000000000 : ℝ)) (X := (52450179568820734951/50000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59979877428961/4000000000000000 : ℝ)*(0 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(59979877428961/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2450179568820734951/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59979877428961/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (1 : ℝ)+(59979877428961/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059979877428961/10000000000000000 : ℝ) by norm_num, show 1+(2450179568820734951/100000000000000000000 : ℝ)+(0 : ℝ)=(102450179568820734951/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2450179568820734951/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59979877428961/4000000000000000 : ℝ)*(2/5 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(59979877428961/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059979877428961/5000000000000000 : ℝ) by norm_num, show 1+2*(2450179568820734951/100000000000000000000 : ℝ)=(52450179568820734951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59979877428961/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59979877428961/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59979877428961/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59979877428961/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59979877428961/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59979877428961/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2382269/12500000 : ℝ)*X 0 0+(1212911133/2000000000 : ℝ)*X 0 1+(190995297/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2759635859/5000000000 : ℝ)*X 1 0+(-529443257/2000000000 : ℝ)*X 1 1+(954976493/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((220770879/400000000 : ℝ)*X 2 0+(4774882351/10000000000 : ℝ)*X 2 1+(-2647216097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1051143347/2500000000 : ℝ)*X 0 0+(3123205763/10000000000 : ℝ)*X 0 1+(566685279/1000000000 : ℝ)*X 0 2+(1051143347/2500000000 : ℝ)*X 1 0+(3123205763/10000000000 : ℝ)*X 1 1+(566685279/1000000000 : ℝ)*X 1 2+(1051143347/2500000000 : ℝ)*X 2 0+(3123205763/10000000000 : ℝ)*X 2 1+(566685279/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-955546163/5000000000 : ℝ)*X 0 0+(1202042977/2500000000 : ℝ)*X 0 1+(60300987/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((516906219/1000000000 : ℝ)*X 1 0+(-696000801/5000000000 : ℝ)*X 1 1+(1507524773/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584531697/5000000000 : ℝ)*X 2 0+(6030099073/10000000000 : ℝ)*X 2 1+(-69599989/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1053744697/2500000000 : ℝ)*X 0 0+(1400298959/2500000000 : ℝ)*X 0 1+(3191165119/10000000000 : ℝ)*X 0 2+(1053744697/2500000000 : ℝ)*X 1 0+(1400298959/2500000000 : ℝ)*X 1 1+(3191165119/10000000000 : ℝ)*X 1 2+(1053744697/2500000000 : ℝ)*X 2 0+(1400298959/2500000000 : ℝ)*X 2 1+(3191165119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53553030261508916012691/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34439139/100000000000000 : ℝ)*(base1) + (1107082763/100000000000000 : ℝ)*(base19) + (262233329/25000000000000 : ℝ)*(base23) + (18851007/20000000000000 : ℝ)*(base24) + (257247703/100000000000000 : ℝ)*(upper3) + (146066990554477/25000000000000 : ℝ)*(major0) + (146066990554477/25000000000000 : ℝ)*(major1) + (146066990554477/25000000000000 : ℝ)*(major2) + (387696936035631/50000000000000 : ℝ)*(sp0) + (775395183300811/100000000000000 : ℝ)*(sp1) + (775395147195223/100000000000000 : ℝ)*(sp2) + (393137461968201/100000000000000 : ℝ)*(sp3) + (2452751451/100000000000000 : ℝ)*(sp4) + (1994836819/100000000000000 : ℝ)*(sp7) + (196569745622079/50000000000000 : ℝ)*(f.failure) + (387698145191787/50000000000000 : ℝ)*(f.sum) + (37354578691603/50000000000000000000000000000 : ℝ)*base66 + (467252010491603/100000000000000000000000000000 : ℝ)*base68 + (35851437908397/100000000000000000000000000000 : ℝ)*base69 + (232604797791603/100000000000000000000000000000 : ℝ)*base72 + (57171477591603/50000000000000000000000000000 : ℝ)*base74 + (46391931408397/100000000000000000000000000000 : ℝ)*base75 + (444506010491603/100000000000000000000000000000 : ℝ)*base78 + (87649163991603/100000000000000000000000000000 : ℝ)*base80 + (9942562991603/50000000000000000000000000000 : ℝ)*base82 + (7794503/5000000000000000000000 : ℝ)*base90 + (7794503/5000000000000000000000 : ℝ)*base92 + (7794503/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1522550506587005394245277/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (673674347/50000000000000 : ℝ)*(base19) + (483101043/25000000000000 : ℝ)*(base23) + (359008129/100000000000000 : ℝ)*(base39) + (95168407/25000000000000 : ℝ)*(base45) + (46572687/25000000000000 : ℝ)*(upper3) + (85534471/25000000000000 : ℝ)*(upper5) + (616653052316611/100000000000000 : ℝ)*(major0) + (616653052316611/100000000000000 : ℝ)*(major1) + (616652693308481/100000000000000 : ℝ)*(major2) + (676638213/100000000000000 : ℝ)*(sp2) + (818374872803403/100000000000000 : ℝ)*(sp4) + (204593381363677/25000000000000 : ℝ)*(sp5) + (818372622769147/100000000000000 : ℝ)*(sp6) + (207465309531633/50000000000000 : ℝ)*(sp7) + (207465309531633/50000000000000 : ℝ)*(f.failure) + (204593807952883/25000000000000 : ℝ)*(f.sum) + (89054069272353/100000000000000000000000000000 : ℝ)*base65 + (868945816318241/400000000000000000000000000000 : ℝ)*base67 + (3276906268828829/400000000000000000000000000000 : ℝ)*base70 + (2049294285118241/400000000000000000000000000000 : ℝ)*base71 + (49476123727647/100000000000000000000000000000 : ℝ)*base74 + (1598274116771171/400000000000000000000000000000 : ℝ)*base75 + (1196696752371171/400000000000000000000000000000 : ℝ)*base77 + (1393475684771171/400000000000000000000000000000 : ℝ)*base79 + (197131633828829/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (23375081/5000000000000000000000 : ℝ)*base90 + (23375081/5000000000000000000000 : ℝ)*base92 + (26624919/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1098_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5597/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1098_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1098_s1_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113648493/10000000000 : ℝ)*x 0 + (5713442737/10000000000 : ℝ)*x 1 + (1248229783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113648493/10000000000 : ℝ)^8291 ≤ (3173595103427/25000000000000 : ℝ)^6243 := by
    have hnat : (2113648493 : ℕ)^8291*25000000000000^6243 ≤ 3173595103427^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113648493 10000000000 3173595103427 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5713442737/10000000000 : ℝ)^8291 ≤ (23774908897461/50000000000000 : ℝ)^6243 := by
    have hnat : (5713442737 : ℕ)^8291*50000000000000^6243 ≤ 23774908897461^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5713442737 10000000000 23774908897461 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248229783/2500000000 : ℝ)^8291 ≤ (39755801783617/100000000000000 : ℝ)^6243 := by
    have hnat : (1248229783 : ℕ)^8291*100000000000000^6243 ≤ 39755801783617^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248229783 2500000000 39755801783617 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113648493/10000000000 : ℝ), (5713442737/10000000000 : ℝ), (1248229783/2500000000 : ℝ)] ![(3173595103427/25000000000000 : ℝ), (23774908897461/50000000000000 : ℝ), (39755801783617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113648493/10000000000 : ℝ)|^8291 ≤ (3173595103427/25000000000000 : ℝ)^6243
        have hw : |(-2113648493/10000000000 : ℝ)|=(2113648493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5713442737/10000000000 : ℝ)|^8291 ≤ (23774908897461/50000000000000 : ℝ)^6243
        have hw : |(5713442737/10000000000 : ℝ)|=(5713442737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1248229783/2500000000 : ℝ)|^8291 ≤ (39755801783617/100000000000000 : ℝ)^6243
        have hw : |(1248229783/2500000000 : ℝ)|=(1248229783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s1_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5421547157/10000000000 : ℝ)*x 0 + (-1251683967/5000000000 : ℝ)*x 1 + (2496459637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421547157/10000000000 : ℝ)^8291 ≤ (44350963207613/100000000000000 : ℝ)^6243 := by
    have hnat : (5421547157 : ℕ)^8291*100000000000000^6243 ≤ 44350963207613^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421547157 10000000000 44350963207613 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251683967/5000000000 : ℝ)^8291 ≤ (794661674737/5000000000000 : ℝ)^6243 := by
    have hnat : (1251683967 : ℕ)^8291*5000000000000^6243 ≤ 794661674737^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251683967 5000000000 794661674737 5000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2496459637/5000000000 : ℝ)^8291 ≤ (7951160657039/20000000000000 : ℝ)^6243 := by
    have hnat : (2496459637 : ℕ)^8291*20000000000000^6243 ≤ 7951160657039^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2496459637 5000000000 7951160657039 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421547157/10000000000 : ℝ), (-1251683967/5000000000 : ℝ), (2496459637/5000000000 : ℝ)] ![(44350963207613/100000000000000 : ℝ), (794661674737/5000000000000 : ℝ), (7951160657039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421547157/10000000000 : ℝ)|^8291 ≤ (44350963207613/100000000000000 : ℝ)^6243
        have hw : |(5421547157/10000000000 : ℝ)|=(5421547157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1251683967/5000000000 : ℝ)|^8291 ≤ (794661674737/5000000000000 : ℝ)^6243
        have hw : |(-1251683967/5000000000 : ℝ)|=(1251683967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2496459637/5000000000 : ℝ)|^8291 ≤ (7951160657039/20000000000000 : ℝ)^6243
        have hw : |(2496459637/5000000000 : ℝ)|=(2496459637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s1_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1355387049/2500000000 : ℝ)*x 0 + (4992918243/10000000000 : ℝ)*x 1 + (-2503367887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355387049/2500000000 : ℝ)^8291 ≤ (11087743623851/25000000000000 : ℝ)^6243 := by
    have hnat : (1355387049 : ℕ)^8291*25000000000000^6243 ≤ 11087743623851^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355387049 2500000000 11087743623851 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992918243/10000000000 : ℝ)^8291 ≤ (39755792382893/100000000000000 : ℝ)^6243 := by
    have hnat : (4992918243 : ℕ)^8291*100000000000000^6243 ≤ 39755792382893^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992918243 10000000000 39755792382893 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2503367887/10000000000 : ℝ)^8291 ≤ (15893233098463/100000000000000 : ℝ)^6243 := by
    have hnat : (2503367887 : ℕ)^8291*100000000000000^6243 ≤ 15893233098463^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503367887 10000000000 15893233098463 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355387049/2500000000 : ℝ), (4992918243/10000000000 : ℝ), (-2503367887/10000000000 : ℝ)] ![(11087743623851/25000000000000 : ℝ), (39755792382893/100000000000000 : ℝ), (15893233098463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355387049/2500000000 : ℝ)|^8291 ≤ (11087743623851/25000000000000 : ℝ)^6243
        have hw : |(1355387049/2500000000 : ℝ)|=(1355387049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992918243/10000000000 : ℝ)|^8291 ≤ (39755792382893/100000000000000 : ℝ)^6243
        have hw : |(4992918243/10000000000 : ℝ)|=(4992918243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2503367887/10000000000 : ℝ)|^8291 ≤ (15893233098463/100000000000000 : ℝ)^6243
        have hw : |(-2503367887/10000000000 : ℝ)|=(2503367887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s1_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4321138899/10000000000 : ℝ)*x 0 + (733737363/2000000000 : ℝ)*x 1 + (636223449/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321138899/10000000000 : ℝ)^8291 ≤ (16406924203373/50000000000000 : ℝ)^6243 := by
    have hnat : (4321138899 : ℕ)^8291*50000000000000^6243 ≤ 16406924203373^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321138899 10000000000 16406924203373 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733737363/2000000000 : ℝ)^8291 ≤ (6600692318427/25000000000000 : ℝ)^6243 := by
    have hnat : (733737363 : ℕ)^8291*25000000000000^6243 ≤ 6600692318427^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733737363 2000000000 6600692318427 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (636223449/1250000000 : ℝ)^8291 ≤ (20391691150359/50000000000000 : ℝ)^6243 := by
    have hnat : (636223449 : ℕ)^8291*50000000000000^6243 ≤ 20391691150359^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636223449 1250000000 20391691150359 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321138899/10000000000 : ℝ), (733737363/2000000000 : ℝ), (636223449/1250000000 : ℝ)] ![(16406924203373/50000000000000 : ℝ), (6600692318427/25000000000000 : ℝ), (20391691150359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321138899/10000000000 : ℝ)|^8291 ≤ (16406924203373/50000000000000 : ℝ)^6243
        have hw : |(4321138899/10000000000 : ℝ)|=(4321138899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(733737363/2000000000 : ℝ)|^8291 ≤ (6600692318427/25000000000000 : ℝ)^6243
        have hw : |(733737363/2000000000 : ℝ)|=(733737363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(636223449/1250000000 : ℝ)|^8291 ≤ (20391691150359/50000000000000 : ℝ)^6243
        have hw : |(636223449/1250000000 : ℝ)|=(636223449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s1_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114518227/10000000000 : ℝ)*x 0 + (5002923937/10000000000 : ℝ)*x 1 + (1425809223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114518227/10000000000 : ℝ)^8291 ≤ (12701317994933/100000000000000 : ℝ)^6243 := by
    have hnat : (2114518227 : ℕ)^8291*100000000000000^6243 ≤ 12701317994933^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114518227 10000000000 12701317994933 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5002923937/10000000000 : ℝ)^8291 ≤ (19930816141507/50000000000000 : ℝ)^6243 := by
    have hnat : (5002923937 : ℕ)^8291*50000000000000^6243 ≤ 19930816141507^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002923937 10000000000 19930816141507 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1425809223/2500000000 : ℝ)^8291 ≤ (47437049708323/100000000000000 : ℝ)^6243 := by
    have hnat : (1425809223 : ℕ)^8291*100000000000000^6243 ≤ 47437049708323^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1425809223 2500000000 47437049708323 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114518227/10000000000 : ℝ), (5002923937/10000000000 : ℝ), (1425809223/2500000000 : ℝ)] ![(12701317994933/100000000000000 : ℝ), (19930816141507/50000000000000 : ℝ), (47437049708323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114518227/10000000000 : ℝ)|^8291 ≤ (12701317994933/100000000000000 : ℝ)^6243
        have hw : |(-2114518227/10000000000 : ℝ)|=(2114518227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5002923937/10000000000 : ℝ)|^8291 ≤ (19930816141507/50000000000000 : ℝ)^6243
        have hw : |(5002923937/10000000000 : ℝ)|=(5002923937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1425809223/2500000000 : ℝ)|^8291 ≤ (47437049708323/100000000000000 : ℝ)^6243
        have hw : |(1425809223/2500000000 : ℝ)|=(1425809223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s1_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5237229841/10000000000 : ℝ)*x 0 + (-1793049881/10000000000 : ℝ)*x 1 + (356452311/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5237229841/10000000000 : ℝ)^8291 ≤ (42359775658183/100000000000000 : ℝ)^6243 := by
    have hnat : (5237229841 : ℕ)^8291*100000000000000^6243 ≤ 42359775658183^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237229841 10000000000 42359775658183 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793049881/10000000000 : ℝ)^8291 ≤ (10203173688913/100000000000000 : ℝ)^6243 := by
    have hnat : (1793049881 : ℕ)^8291*100000000000000^6243 ≤ 10203173688913^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793049881 10000000000 10203173688913 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356452311/625000000 : ℝ)^8291 ≤ (47437050636197/100000000000000 : ℝ)^6243 := by
    have hnat : (356452311 : ℕ)^8291*100000000000000^6243 ≤ 47437050636197^6243*625000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356452311 625000000 47437050636197 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5237229841/10000000000 : ℝ), (-1793049881/10000000000 : ℝ), (356452311/625000000 : ℝ)] ![(42359775658183/100000000000000 : ℝ), (10203173688913/100000000000000 : ℝ), (47437050636197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5237229841/10000000000 : ℝ)|^8291 ≤ (42359775658183/100000000000000 : ℝ)^6243
        have hw : |(5237229841/10000000000 : ℝ)|=(5237229841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793049881/10000000000 : ℝ)|^8291 ≤ (10203173688913/100000000000000 : ℝ)^6243
        have hw : |(-1793049881/10000000000 : ℝ)|=(1793049881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356452311/625000000 : ℝ)|^8291 ≤ (47437050636197/100000000000000 : ℝ)^6243
        have hw : |(356452311/625000000 : ℝ)|=(356452311/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s1_6 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5237229721/10000000000 : ℝ)*x 0 + (2851618459/5000000000 : ℝ)*x 1 + (-224131267/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5237229721/10000000000 : ℝ)^8291 ≤ (42359774369201/100000000000000 : ℝ)^6243 := by
    have hnat : (5237229721 : ℕ)^8291*100000000000000^6243 ≤ 42359774369201^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237229721 10000000000 42359774369201 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2851618459/5000000000 : ℝ)^8291 ≤ (23718524997761/50000000000000 : ℝ)^6243 := by
    have hnat : (2851618459 : ℕ)^8291*50000000000000^6243 ≤ 23718524997761^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2851618459 5000000000 23718524997761 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224131267/1250000000 : ℝ)^8291 ≤ (510158780799/5000000000000 : ℝ)^6243 := by
    have hnat : (224131267 : ℕ)^8291*5000000000000^6243 ≤ 510158780799^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224131267 1250000000 510158780799 5000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5237229721/10000000000 : ℝ), (2851618459/5000000000 : ℝ), (-224131267/1250000000 : ℝ)] ![(42359774369201/100000000000000 : ℝ), (23718524997761/50000000000000 : ℝ), (510158780799/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5237229721/10000000000 : ℝ)|^8291 ≤ (42359774369201/100000000000000 : ℝ)^6243
        have hw : |(5237229721/10000000000 : ℝ)|=(5237229721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2851618459/5000000000 : ℝ)|^8291 ≤ (23718524997761/50000000000000 : ℝ)^6243
        have hw : |(2851618459/5000000000 : ℝ)|=(2851618459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224131267/1250000000 : ℝ)|^8291 ≤ (510158780799/5000000000000 : ℝ)^6243
        have hw : |(-224131267/1250000000 : ℝ)|=(224131267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s1_7 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (540356629/1250000000 : ℝ)*x 0 + (5070055401/10000000000 : ℝ)*x 1 + (147552617/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540356629/1250000000 : ℝ)^8291 ≤ (1641556821407/5000000000000 : ℝ)^6243 := by
    have hnat : (540356629 : ℕ)^8291*5000000000000^6243 ≤ 1641556821407^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540356629 1250000000 1641556821407 5000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5070055401/10000000000 : ℝ)^8291 ≤ (8114707715747/20000000000000 : ℝ)^6243 := by
    have hnat : (5070055401 : ℕ)^8291*20000000000000^6243 ≤ 8114707715747^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5070055401 10000000000 8114707715747 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147552617/400000000 : ℝ)^8291 ≤ (2659532497777/10000000000000 : ℝ)^6243 := by
    have hnat : (147552617 : ℕ)^8291*10000000000000^6243 ≤ 2659532497777^6243*400000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147552617 400000000 2659532497777 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540356629/1250000000 : ℝ), (5070055401/10000000000 : ℝ), (147552617/400000000 : ℝ)] ![(1641556821407/5000000000000 : ℝ), (8114707715747/20000000000000 : ℝ), (2659532497777/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540356629/1250000000 : ℝ)|^8291 ≤ (1641556821407/5000000000000 : ℝ)^6243
        have hw : |(540356629/1250000000 : ℝ)|=(540356629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5070055401/10000000000 : ℝ)|^8291 ≤ (8114707715747/20000000000000 : ℝ)^6243
        have hw : |(5070055401/10000000000 : ℝ)|=(5070055401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147552617/400000000 : ℝ)|^8291 ≤ (2659532497777/10000000000000 : ℝ)^6243
        have hw : |(147552617/400000000 : ℝ)|=(147552617/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5597/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5399/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (129/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5597/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5597/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5597/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5597/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5597/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5597/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (231/100000 : ℝ) ^ (4145/1024 : ℝ) ≤ (1064786749/50000000000000000000 : ℝ) := by
    have hpowers : (231/100000 : ℝ)^4145 ≤ (1064786749/50000000000000000000 : ℝ)^1024 := by
      have hnat : (231 : ℕ)^4145*50000000000000000000^1024 ≤ 1064786749^1024*100000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        231 100000 1064786749 50000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (231/100000 : ℝ)) (X := (1064786749/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5597/20000 : ℝ) ^ (4145/1024 : ℝ) ≤ (577079646297697391/100000000000000000000 : ℝ) := by
    have hpowers : (5597/20000 : ℝ)^4145 ≤ (577079646297697391/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5597 : ℕ)^4145*100000000000000000000^1024 ≤ 577079646297697391^1024*20000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5597 20000 577079646297697391 100000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5597/20000 : ℝ)) (X := (577079646297697391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000001064786749/25000000000000000000 : ℝ) ≤ (500000000005261/500000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (25000000001064786749/25000000000000000000 : ℝ)^1024 ≤ (500000000005261/500000000000000 : ℝ)^4145 := by
      have hnat : (25000000001064786749 : ℕ)^1024*500000000000000^4145 ≤ 500000000005261^4145*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000001064786749 25000000000000000000 500000000005261 500000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000005261/500000000000000 : ℝ)) (X := (25000000001064786749/25000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100577079648427270889/100000000000000000000 : ℝ) ≤ (10014225573764021/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (100577079648427270889/100000000000000000000 : ℝ)^1024 ≤ (10014225573764021/10000000000000000 : ℝ)^4145 := by
      have hnat : (100577079648427270889 : ℕ)^1024*10000000000000000^4145 ≤ 10014225573764021^4145*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100577079648427270889 100000000000000000000 10014225573764021 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014225573764021/10000000000000000 : ℝ)) (X := (100577079648427270889/100000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50577079646297697391/50000000000000000000 : ℝ) ≤ (5014225573711411/5000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (50577079646297697391/50000000000000000000 : ℝ)^1024 ≤ (5014225573711411/5000000000000000 : ℝ)^4145 := by
      have hnat : (50577079646297697391 : ℕ)^1024*5000000000000000^4145 ≤ 5014225573711411^4145*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50577079646297697391 50000000000000000000 5014225573711411 5000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014225573711411/5000000000000000 : ℝ)) (X := (50577079646297697391/50000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1064786749/50000000000000000000 : ℝ) ≤ ((138766713893944954909/138770000000000000000 : ℝ)+2*(14225573658801/2775400000000000 : ℝ)*(231/100000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (138766713893944954909/138770000000000000000 : ℝ)+2*(14225573658801/2775400000000000 : ℝ)*(231/100000 : ℝ)=(500000000005261/500000000000000 : ℝ) by norm_num, show 1+2*(1064786749/50000000000000000000 : ℝ)=(25000000001064786749/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(577079646297697391/100000000000000000000 : ℝ)+(1064786749/50000000000000000000 : ℝ) ≤ ((138766713893944954909/138770000000000000000 : ℝ)+(14225573658801/2775400000000000 : ℝ)*((5597/20000 : ℝ)+(231/100000 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (138766713893944954909/138770000000000000000 : ℝ)+(14225573658801/2775400000000000 : ℝ)*((5597/20000 : ℝ)+(231/100000 : ℝ))=(10014225573764021/10000000000000000 : ℝ) by norm_num, show 1+(577079646297697391/100000000000000000000 : ℝ)+(1064786749/50000000000000000000 : ℝ)=(100577079648427270889/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(577079646297697391/100000000000000000000 : ℝ) ≤ ((138766713893944954909/138770000000000000000 : ℝ)+2*(14225573658801/2775400000000000 : ℝ)*(5597/20000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (138766713893944954909/138770000000000000000 : ℝ)+2*(14225573658801/2775400000000000 : ℝ)*(5597/20000 : ℝ)=(5014225573711411/5000000000000000 : ℝ) by norm_num, show 1+2*(577079646297697391/100000000000000000000 : ℝ)=(50577079646297697391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (138766713893944954909/138770000000000000000 : ℝ)*(X 1 0+X 2 0)+(14225573658801/2775400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (231/100000 : ℝ)) (hi := (5597/20000 : ℝ)) (c := (138766713893944954909/138770000000000000000 : ℝ)) (alpha := (14225573658801/2775400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (138766713893944954909/138770000000000000000 : ℝ)*(X 0 1+X 2 1)+(14225573658801/2775400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (231/100000 : ℝ)) (hi := (5597/20000 : ℝ)) (c := (138766713893944954909/138770000000000000000 : ℝ)) (alpha := (14225573658801/2775400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (138766713893944954909/138770000000000000000 : ℝ)*(X 0 2+X 1 2)+(14225573658801/2775400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (231/100000 : ℝ)) (hi := (5597/20000 : ℝ)) (c := (138766713893944954909/138770000000000000000 : ℝ)) (alpha := (14225573658801/2775400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2113648493/10000000000 : ℝ)*X 0 0+(5713442737/10000000000 : ℝ)*X 0 1+(1248229783/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421547157/10000000000 : ℝ)*X 1 0+(-1251683967/5000000000 : ℝ)*X 1 1+(2496459637/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1355387049/2500000000 : ℝ)*X 2 0+(4992918243/10000000000 : ℝ)*X 2 1+(-2503367887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321138899/10000000000 : ℝ)*X 0 0+(733737363/2000000000 : ℝ)*X 0 1+(636223449/1250000000 : ℝ)*X 0 2+(4321138899/10000000000 : ℝ)*X 1 0+(733737363/2000000000 : ℝ)*X 1 1+(636223449/1250000000 : ℝ)*X 1 2+(4321138899/10000000000 : ℝ)*X 2 0+(733737363/2000000000 : ℝ)*X 2 1+(636223449/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2114518227/10000000000 : ℝ)*X 0 0+(5002923937/10000000000 : ℝ)*X 0 1+(1425809223/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5237229841/10000000000 : ℝ)*X 1 0+(-1793049881/10000000000 : ℝ)*X 1 1+(356452311/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5237229721/10000000000 : ℝ)*X 2 0+(2851618459/5000000000 : ℝ)*X 2 1+(-224131267/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540356629/1250000000 : ℝ)*X 0 0+(5070055401/10000000000 : ℝ)*X 0 1+(147552617/400000000 : ℝ)*X 0 2+(540356629/1250000000 : ℝ)*X 1 0+(5070055401/10000000000 : ℝ)*X 1 1+(147552617/400000000 : ℝ)*X 1 2+(540356629/1250000000 : ℝ)*X 2 0+(5070055401/10000000000 : ℝ)*X 2 1+(147552617/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61581329616763895378227137123/6938500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109434239/50000000000000 : ℝ)*(base1) + (223141271/12500000000000 : ℝ)*(base19) + (1025555003/50000000000000 : ℝ)*(base23) + (2214137/1562500000000 : ℝ)*(upper3) + (114727957/50000000000000 : ℝ)*(upper5) + (1045792243073451/100000000000000 : ℝ)*(major0) + (1045792243073451/100000000000000 : ℝ)*(major1) + (1045792243073451/100000000000000 : ℝ)*(major2) + (693943646414901/50000000000000 : ℝ)*(sp0) + (1387894616391619/100000000000000 : ℝ)*(sp1) + (1387894350411781/100000000000000 : ℝ)*(sp2) + (21990116058581/3125000000000 : ℝ)*(sp3) + (582972529/6250000000000 : ℝ)*(sp4) + (3856038413/100000000000000 : ℝ)*(sp7) + (175921947195371/25000000000000 : ℝ)*(f.failure) + (1387896401521787/100000000000000 : ℝ)*(f.sum) + (395520517445551/138770000000000000000000000000 : ℝ)*base65 + (56528253942612429041/13877000000000000000000000000000000 : ℝ)*base68 + (38389110434525570959/13877000000000000000000000000000000 : ℝ)*base69 + (20143476994956429041/13877000000000000000000000000000000 : ℝ)*base72 + (349392851112939/138770000000000000000000000000 : ℝ)*base74 + (102692979525567570959/13877000000000000000000000000000000 : ℝ)*base75 + (41614447749882570959/13877000000000000000000000000000000 : ℝ)*base77 + (49734236034130570959/13877000000000000000000000000000000 : ℝ)*base79 + (295384150389911/138770000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (8600147/2500000000000000000000 : ℝ)*base90 + (8600147/2500000000000000000000 : ℝ)*base92 + (8600147/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12281722429766734676082731949/1734625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61234523/100000000000000 : ℝ)*(base1) + (755869099/50000000000000 : ℝ)*(base19) + (727583983/50000000000000 : ℝ)*(base23) + (155183419/100000000000000 : ℝ)*(upper3) + (89493983/50000000000000 : ℝ)*(upper5) + (537980094464187/50000000000000 : ℝ)*(major0) + (537980094464187/50000000000000 : ℝ)*(major1) + (537980094464187/50000000000000 : ℝ)*(major2) + (265484471/4000000000000 : ℝ)*(sp1) + (5959332711/100000000000000 : ℝ)*(sp2) + (713966574059533/50000000000000 : ℝ)*(sp4) + (142792493803457/10000000000000 : ℝ)*(sp5) + (713962836191933/50000000000000 : ℝ)*(sp6) + (361993496863291/50000000000000 : ℝ)*(sp7) + (144797410992221/20000000000000 : ℝ)*(f.failure) + (1427933086884543/100000000000000 : ℝ)*(f.sum) + (56091387485383/69385000000000000000000000000 : ℝ)*base66 + (8488794894995693983/6938500000000000000000000000000000 : ℝ)*base67 + (24472951774127306017/6938500000000000000000000000000000 : ℝ)*base70 + (35788697801136806017/6938500000000000000000000000000000 : ℝ)*base72 + (220707600142417/69385000000000000000000000000 : ℝ)*base73 + (65134843139050306017/6938500000000000000000000000000000 : ℝ)*base76 + (37772024292771306017/6938500000000000000000000000000000 : ℝ)*base78 + (23982198059485806017/6938500000000000000000000000000000 : ℝ)*base80 + (52958005915629/34692500000000000000000000000 : ℝ)*base82 + (9579403/2000000000000000000000 : ℝ)*base89 + (9579403/2000000000000000000000 : ℝ)*base91 + (9579403/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1098_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5597/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (129/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1098_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1098_s2_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-271160431/1250000000 : ℝ)*x 0 + (1379850189/2500000000 : ℝ)*x 1 + (2575814873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271160431/1250000000 : ℝ)^8291 ≤ (6570018414219/50000000000000 : ℝ)^6243 := by
    have hnat : (271160431 : ℕ)^8291*50000000000000^6243 ≤ 6570018414219^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271160431 1250000000 6570018414219 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379850189/2500000000 : ℝ)^8291 ≤ (45417188232437/100000000000000 : ℝ)^6243 := by
    have hnat : (1379850189 : ℕ)^8291*100000000000000^6243 ≤ 45417188232437^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379850189 2500000000 45417188232437 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575814873/5000000000 : ℝ)^8291 ≤ (10360693732093/25000000000000 : ℝ)^6243 := by
    have hnat : (2575814873 : ℕ)^8291*25000000000000^6243 ≤ 10360693732093^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575814873 5000000000 10360693732093 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271160431/1250000000 : ℝ), (1379850189/2500000000 : ℝ), (2575814873/5000000000 : ℝ)] ![(6570018414219/50000000000000 : ℝ), (45417188232437/100000000000000 : ℝ), (10360693732093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271160431/1250000000 : ℝ)|^8291 ≤ (6570018414219/50000000000000 : ℝ)^6243
        have hw : |(-271160431/1250000000 : ℝ)|=(271160431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379850189/2500000000 : ℝ)|^8291 ≤ (45417188232437/100000000000000 : ℝ)^6243
        have hw : |(1379850189/2500000000 : ℝ)|=(1379850189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575814873/5000000000 : ℝ)|^8291 ≤ (10360693732093/25000000000000 : ℝ)^6243
        have hw : |(2575814873/5000000000 : ℝ)|=(2575814873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s2_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1343945273/2500000000 : ℝ)*x 0 + (-2360825353/10000000000 : ℝ)*x 1 + (515163083/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343945273/2500000000 : ℝ)^8291 ≤ (8770889250641/20000000000000 : ℝ)^6243 := by
    have hnat : (1343945273 : ℕ)^8291*20000000000000^6243 ≤ 8770889250641^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343945273 2500000000 8770889250641 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2360825353/10000000000 : ℝ)^8291 ≤ (14702767229781/100000000000000 : ℝ)^6243 := by
    have hnat : (2360825353 : ℕ)^8291*100000000000000^6243 ≤ 14702767229781^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360825353 10000000000 14702767229781 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515163083/1000000000 : ℝ)^8291 ≤ (41442786509399/100000000000000 : ℝ)^6243 := by
    have hnat : (515163083 : ℕ)^8291*100000000000000^6243 ≤ 41442786509399^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515163083 1000000000 41442786509399 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343945273/2500000000 : ℝ), (-2360825353/10000000000 : ℝ), (515163083/1000000000 : ℝ)] ![(8770889250641/20000000000000 : ℝ), (14702767229781/100000000000000 : ℝ), (41442786509399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343945273/2500000000 : ℝ)|^8291 ≤ (8770889250641/20000000000000 : ℝ)^6243
        have hw : |(1343945273/2500000000 : ℝ)|=(1343945273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2360825353/10000000000 : ℝ)|^8291 ≤ (14702767229781/100000000000000 : ℝ)^6243
        have hw : |(-2360825353/10000000000 : ℝ)|=(2360825353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515163083/1000000000 : ℝ)|^8291 ≤ (41442786509399/100000000000000 : ℝ)^6243
        have hw : |(515163083/1000000000 : ℝ)|=(515163083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s2_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2687890523/5000000000 : ℝ)*x 0 + (5151630879/10000000000 : ℝ)*x 1 + (-47216507/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687890523/5000000000 : ℝ)^8291 ≤ (8770889150969/20000000000000 : ℝ)^6243 := by
    have hnat : (2687890523 : ℕ)^8291*20000000000000^6243 ≤ 8770889150969^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687890523 5000000000 8770889150969 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5151630879/10000000000 : ℝ)^8291 ≤ (647543547389/1562500000000 : ℝ)^6243 := by
    have hnat : (5151630879 : ℕ)^8291*1562500000000^6243 ≤ 647543547389^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151630879 10000000000 647543547389 1562500000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47216507/200000000 : ℝ)^8291 ≤ (14702767204969/100000000000000 : ℝ)^6243 := by
    have hnat : (47216507 : ℕ)^8291*100000000000000^6243 ≤ 14702767204969^6243*200000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47216507 200000000 14702767204969 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687890523/5000000000 : ℝ), (5151630879/10000000000 : ℝ), (-47216507/200000000 : ℝ)] ![(8770889150969/20000000000000 : ℝ), (647543547389/1562500000000 : ℝ), (14702767204969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687890523/5000000000 : ℝ)|^8291 ≤ (8770889150969/20000000000000 : ℝ)^6243
        have hw : |(2687890523/5000000000 : ℝ)|=(2687890523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5151630879/10000000000 : ℝ)|^8291 ≤ (647543547389/1562500000000 : ℝ)^6243
        have hw : |(5151630879/10000000000 : ℝ)|=(5151630879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47216507/200000000 : ℝ)|^8291 ≤ (14702767204969/100000000000000 : ℝ)^6243
        have hw : |(-47216507/200000000 : ℝ)|=(47216507/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s2_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089796927/2500000000 : ℝ)*x 0 + (4011611567/10000000000 : ℝ)*x 1 + (4736971297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089796927/2500000000 : ℝ)^8291 ≤ (33198120764397/100000000000000 : ℝ)^6243 := by
    have hnat : (1089796927 : ℕ)^8291*100000000000000^6243 ≤ 33198120764397^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089796927 2500000000 33198120764397 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4011611567/10000000000 : ℝ)^8291 ≤ (29729572068423/100000000000000 : ℝ)^6243 := by
    have hnat : (4011611567 : ℕ)^8291*100000000000000^6243 ≤ 29729572068423^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011611567 10000000000 29729572068423 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4736971297/10000000000 : ℝ)^8291 ≤ (37072307155203/100000000000000 : ℝ)^6243 := by
    have hnat : (4736971297 : ℕ)^8291*100000000000000^6243 ≤ 37072307155203^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4736971297 10000000000 37072307155203 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089796927/2500000000 : ℝ), (4011611567/10000000000 : ℝ), (4736971297/10000000000 : ℝ)] ![(33198120764397/100000000000000 : ℝ), (29729572068423/100000000000000 : ℝ), (37072307155203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089796927/2500000000 : ℝ)|^8291 ≤ (33198120764397/100000000000000 : ℝ)^6243
        have hw : |(1089796927/2500000000 : ℝ)|=(1089796927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4011611567/10000000000 : ℝ)|^8291 ≤ (29729572068423/100000000000000 : ℝ)^6243
        have hw : |(4011611567/10000000000 : ℝ)|=(4011611567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4736971297/10000000000 : ℝ)|^8291 ≤ (37072307155203/100000000000000 : ℝ)^6243
        have hw : |(4736971297/10000000000 : ℝ)|=(4736971297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s2_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2169398763/10000000000 : ℝ)*x 0 + (1288561409/2500000000 : ℝ)*x 1 + (1379189517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169398763/10000000000 : ℝ)^8291 ≤ (2628192895389/20000000000000 : ℝ)^6243 := by
    have hnat : (2169398763 : ℕ)^8291*20000000000000^6243 ≤ 2628192895389^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169398763 10000000000 2628192895389 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288561409/2500000000 : ℝ)^8291 ≤ (41470724387551/100000000000000 : ℝ)^6243 := by
    have hnat : (1288561409 : ℕ)^8291*100000000000000^6243 ≤ 41470724387551^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288561409 2500000000 41470724387551 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379189517/2500000000 : ℝ)^8291 ≤ (45388311125863/100000000000000 : ℝ)^6243 := by
    have hnat : (1379189517 : ℕ)^8291*100000000000000^6243 ≤ 45388311125863^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379189517 2500000000 45388311125863 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2169398763/10000000000 : ℝ), (1288561409/2500000000 : ℝ), (1379189517/2500000000 : ℝ)] ![(2628192895389/20000000000000 : ℝ), (41470724387551/100000000000000 : ℝ), (45388311125863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2169398763/10000000000 : ℝ)|^8291 ≤ (2628192895389/20000000000000 : ℝ)^6243
        have hw : |(-2169398763/10000000000 : ℝ)|=(2169398763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1288561409/2500000000 : ℝ)|^8291 ≤ (41470724387551/100000000000000 : ℝ)^6243
        have hw : |(1288561409/2500000000 : ℝ)|=(1288561409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379189517/2500000000 : ℝ)|^8291 ≤ (45388311125863/100000000000000 : ℝ)^6243
        have hw : |(1379189517/2500000000 : ℝ)|=(1379189517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s2_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056549091/2000000000 : ℝ)*x 0 + (-399139517/2000000000 : ℝ)*x 1 + (1379189539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056549091/2000000000 : ℝ)^8291 ≤ (21424688978241/50000000000000 : ℝ)^6243 := by
    have hnat : (1056549091 : ℕ)^8291*50000000000000^6243 ≤ 21424688978241^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056549091 2000000000 21424688978241 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399139517/2000000000 : ℝ)^8291 ≤ (735144371479/6250000000000 : ℝ)^6243 := by
    have hnat : (399139517 : ℕ)^8291*6250000000000^6243 ≤ 735144371479^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399139517 2000000000 735144371479 6250000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379189539/2500000000 : ℝ)^8291 ≤ (22694156043689/50000000000000 : ℝ)^6243 := by
    have hnat : (1379189539 : ℕ)^8291*50000000000000^6243 ≤ 22694156043689^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379189539 2500000000 22694156043689 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056549091/2000000000 : ℝ), (-399139517/2000000000 : ℝ), (1379189539/2500000000 : ℝ)] ![(21424688978241/50000000000000 : ℝ), (735144371479/6250000000000 : ℝ), (22694156043689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056549091/2000000000 : ℝ)|^8291 ≤ (21424688978241/50000000000000 : ℝ)^6243
        have hw : |(1056549091/2000000000 : ℝ)|=(1056549091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399139517/2000000000 : ℝ)|^8291 ≤ (735144371479/6250000000000 : ℝ)^6243
        have hw : |(-399139517/2000000000 : ℝ)|=(399139517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379189539/2500000000 : ℝ)|^8291 ≤ (22694156043689/50000000000000 : ℝ)^6243
        have hw : |(1379189539/2500000000 : ℝ)|=(1379189539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s2_6 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641372811/5000000000 : ℝ)*x 0 + (1379189521/2500000000 : ℝ)*x 1 + (-124731091/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641372811/5000000000 : ℝ)^8291 ≤ (21424689877707/50000000000000 : ℝ)^6243 := by
    have hnat : (2641372811 : ℕ)^8291*50000000000000^6243 ≤ 21424689877707^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641372811 5000000000 21424689877707 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379189521/2500000000 : ℝ)^8291 ≤ (11347077825171/25000000000000 : ℝ)^6243 := by
    have hnat : (1379189521 : ℕ)^8291*25000000000000^6243 ≤ 11347077825171^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379189521 2500000000 11347077825171 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124731091/625000000 : ℝ)^8291 ≤ (1470288616743/12500000000000 : ℝ)^6243 := by
    have hnat : (124731091 : ℕ)^8291*12500000000000^6243 ≤ 1470288616743^6243*625000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124731091 625000000 1470288616743 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641372811/5000000000 : ℝ), (1379189521/2500000000 : ℝ), (-124731091/625000000 : ℝ)] ![(21424689877707/50000000000000 : ℝ), (11347077825171/25000000000000 : ℝ), (1470288616743/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641372811/5000000000 : ℝ)|^8291 ≤ (21424689877707/50000000000000 : ℝ)^6243
        have hw : |(2641372811/5000000000 : ℝ)|=(2641372811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379189521/2500000000 : ℝ)|^8291 ≤ (11347077825171/25000000000000 : ℝ)^6243
        have hw : |(1379189521/2500000000 : ℝ)|=(1379189521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124731091/625000000 : ℝ)|^8291 ≤ (1470288616743/12500000000000 : ℝ)^6243
        have hw : |(-124731091/625000000 : ℝ)|=(124731091/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s2_7 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272463529/625000000 : ℝ)*x 0 + (236590633/500000000 : ℝ)*x 1 + (1004205529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272463529/625000000 : ℝ)^8291 ≤ (3320043441483/10000000000000 : ℝ)^6243 := by
    have hnat : (272463529 : ℕ)^8291*10000000000000^6243 ≤ 3320043441483^6243*625000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272463529 625000000 3320043441483 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236590633/500000000 : ℝ)^8291 ≤ (37018700364363/100000000000000 : ℝ)^6243 := by
    have hnat : (236590633 : ℕ)^8291*100000000000000^6243 ≤ 37018700364363^6243*500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236590633 500000000 37018700364363 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004205529/2500000000 : ℝ)^8291 ≤ (29780865214229/100000000000000 : ℝ)^6243 := by
    have hnat : (1004205529 : ℕ)^8291*100000000000000^6243 ≤ 29780865214229^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004205529 2500000000 29780865214229 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272463529/625000000 : ℝ), (236590633/500000000 : ℝ), (1004205529/2500000000 : ℝ)] ![(3320043441483/10000000000000 : ℝ), (37018700364363/100000000000000 : ℝ), (29780865214229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272463529/625000000 : ℝ)|^8291 ≤ (3320043441483/10000000000000 : ℝ)^6243
        have hw : |(272463529/625000000 : ℝ)|=(272463529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(236590633/500000000 : ℝ)|^8291 ≤ (37018700364363/100000000000000 : ℝ)^6243
        have hw : |(236590633/500000000 : ℝ)|=(236590633/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004205529/2500000000 : ℝ)|^8291 ≤ (29780865214229/100000000000000 : ℝ)^6243
        have hw : |(1004205529/2500000000 : ℝ)|=(1004205529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (129/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4433/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8319/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (129/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (129/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (129/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (129/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (129/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (129/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5399/100000 : ℝ) ^ (4145/1024 : ℝ) ≤ (369455831769089/50000000000000000000 : ℝ) := by
    have hpowers : (5399/100000 : ℝ)^4145 ≤ (369455831769089/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5399 : ℕ)^4145*50000000000000000000^1024 ≤ 369455831769089^1024*100000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5399 100000 369455831769089 50000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5399/100000 : ℝ)) (X := (369455831769089/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (129/625 : ℝ) ^ (4145/1024 : ℝ) ≤ (168285446693776191/100000000000000000000 : ℝ) := by
    have hpowers : (129/625 : ℝ)^4145 ≤ (168285446693776191/100000000000000000000 : ℝ)^1024 := by
      have hnat : (129 : ℕ)^4145*100000000000000000000^1024 ≤ 168285446693776191^1024*625^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        129 625 168285446693776191 100000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (129/625 : ℝ)) (X := (168285446693776191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000369455831769089/25000000000000000000 : ℝ) ≤ (2500009127157223/2500000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (25000369455831769089/25000000000000000000 : ℝ)^1024 ≤ (2500009127157223/2500000000000000 : ℝ)^4145 := by
      have hnat : (25000369455831769089 : ℕ)^1024*2500000000000000^4145 ≤ 2500009127157223^4145*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000369455831769089 25000000000000000000 2500009127157223 2500000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500009127157223/2500000000000000 : ℝ)) (X := (25000369455831769089/25000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100169024358357314369/100000000000000000000 : ℝ) ≤ (5002086500765453/5000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (100169024358357314369/100000000000000000000 : ℝ)^1024 ≤ (5002086500765453/5000000000000000 : ℝ)^4145 := by
      have hnat : (100169024358357314369 : ℕ)^1024*5000000000000000^4145 ≤ 5002086500765453^4145*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100169024358357314369 100000000000000000000 5002086500765453 5000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002086500765453/5000000000000000 : ℝ)) (X := (100169024358357314369/100000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50168285446693776191/50000000000000000000 : ℝ) ≤ (250207737360823/250000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (50168285446693776191/50000000000000000000 : ℝ)^1024 ≤ (250207737360823/250000000000000 : ℝ)^4145 := by
      have hnat : (50168285446693776191 : ℕ)^1024*250000000000000^4145 ≤ 250207737360823^4145*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50168285446693776191 50000000000000000000 250207737360823 250000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250207737360823/250000000000000 : ℝ)) (X := (50168285446693776191/50000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(369455831769089/50000000000000000000 : ℝ) ≤ ((761829452888284979/762050000000000000 : ℝ)+2*(2068246451007/762050000000000 : ℝ)*(5399/100000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (761829452888284979/762050000000000000 : ℝ)+2*(2068246451007/762050000000000 : ℝ)*(5399/100000 : ℝ)=(2500009127157223/2500000000000000 : ℝ) by norm_num, show 1+2*(369455831769089/50000000000000000000 : ℝ)=(25000369455831769089/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(168285446693776191/100000000000000000000 : ℝ)+(369455831769089/50000000000000000000 : ℝ) ≤ ((761829452888284979/762050000000000000 : ℝ)+(2068246451007/762050000000000 : ℝ)*((129/625 : ℝ)+(5399/100000 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (761829452888284979/762050000000000000 : ℝ)+(2068246451007/762050000000000 : ℝ)*((129/625 : ℝ)+(5399/100000 : ℝ))=(5002086500765453/5000000000000000 : ℝ) by norm_num, show 1+(168285446693776191/100000000000000000000 : ℝ)+(369455831769089/50000000000000000000 : ℝ)=(100169024358357314369/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(168285446693776191/100000000000000000000 : ℝ) ≤ ((761829452888284979/762050000000000000 : ℝ)+2*(2068246451007/762050000000000 : ℝ)*(129/625 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (761829452888284979/762050000000000000 : ℝ)+2*(2068246451007/762050000000000 : ℝ)*(129/625 : ℝ)=(250207737360823/250000000000000 : ℝ) by norm_num, show 1+2*(168285446693776191/100000000000000000000 : ℝ)=(50168285446693776191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (761829452888284979/762050000000000000 : ℝ)*(X 1 0+X 2 0)+(2068246451007/762050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (5399/100000 : ℝ)) (hi := (129/625 : ℝ)) (c := (761829452888284979/762050000000000000 : ℝ)) (alpha := (2068246451007/762050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (761829452888284979/762050000000000000 : ℝ)*(X 0 1+X 2 1)+(2068246451007/762050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (5399/100000 : ℝ)) (hi := (129/625 : ℝ)) (c := (761829452888284979/762050000000000000 : ℝ)) (alpha := (2068246451007/762050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (761829452888284979/762050000000000000 : ℝ)*(X 0 2+X 1 2)+(2068246451007/762050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (5399/100000 : ℝ)) (hi := (129/625 : ℝ)) (c := (761829452888284979/762050000000000000 : ℝ)) (alpha := (2068246451007/762050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-271160431/1250000000 : ℝ)*X 0 0+(1379850189/2500000000 : ℝ)*X 0 1+(2575814873/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343945273/2500000000 : ℝ)*X 1 0+(-2360825353/10000000000 : ℝ)*X 1 1+(515163083/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687890523/5000000000 : ℝ)*X 2 0+(5151630879/10000000000 : ℝ)*X 2 1+(-47216507/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089796927/2500000000 : ℝ)*X 0 0+(4011611567/10000000000 : ℝ)*X 0 1+(4736971297/10000000000 : ℝ)*X 0 2+(1089796927/2500000000 : ℝ)*X 1 0+(4011611567/10000000000 : ℝ)*X 1 1+(4736971297/10000000000 : ℝ)*X 1 2+(1089796927/2500000000 : ℝ)*X 2 0+(4011611567/10000000000 : ℝ)*X 2 1+(4736971297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2169398763/10000000000 : ℝ)*X 0 0+(1288561409/2500000000 : ℝ)*X 0 1+(1379189517/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1056549091/2000000000 : ℝ)*X 1 0+(-399139517/2000000000 : ℝ)*X 1 1+(1379189539/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641372811/5000000000 : ℝ)*X 2 0+(1379189521/2500000000 : ℝ)*X 2 1+(-124731091/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272463529/625000000 : ℝ)*X 0 0+(236590633/500000000 : ℝ)*X 0 1+(1004205529/2500000000 : ℝ)*X 0 2+(272463529/625000000 : ℝ)*X 1 0+(236590633/500000000 : ℝ)*X 1 1+(1004205529/2500000000 : ℝ)*X 1 2+(272463529/625000000 : ℝ)*X 2 0+(236590633/500000000 : ℝ)*X 2 1+(1004205529/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (308127472356660973486213809/38102500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (989513691/100000000000000 : ℝ)*(base19) + (2914649/400000000000 : ℝ)*(base23) + (108397903/50000000000000 : ℝ)*(upper3) + (3991253/3125000000000 : ℝ)*(upper4) + (30868321/100000000000000 : ℝ)*(upper5) + (2048877460917081/100000000000000 : ℝ)*(major0) + (2048877460917081/100000000000000 : ℝ)*(major1) + (2048877460917081/100000000000000 : ℝ)*(major2) + (339887537948657/12500000000000 : ℝ)*(sp0) + (1359557294203349/50000000000000 : ℝ)*(sp1) + (135955742462907/5000000000000 : ℝ)*(sp2) + (1378631771721549/100000000000000 : ℝ)*(sp3) + (15274331133/100000000000000 : ℝ)*(sp4) + (912829007/12500000000000 : ℝ)*(sp7) + (344659768588401/25000000000000 : ℝ)*(f.failure) + (271911557792039/10000000000000 : ℝ)*(f.sum) + (182499986417211/76205000000000000000000000000 : ℝ)*base66 + (631306097555158299/76205000000000000000000000000000 : ℝ)*base67 + (794733801061748299/76205000000000000000000000000000 : ℝ)*base69 + (675474932777533299/76205000000000000000000000000000 : ℝ)*base71 + (229343606851911/76205000000000000000000000000 : ℝ)*base74 + (570816129081148299/76205000000000000000000000000000 : ℝ)*base75 + (168051730407613299/76205000000000000000000000000000 : ℝ)*base77 + (623529991822278299/76205000000000000000000000000000 : ℝ)*base79 + (153654439664589/76205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (31522857/2500000000000000000000 : ℝ)*base90 + (31522857/2500000000000000000000 : ℝ)*base92 + (31522857/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63272804536627763931375567/7620500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1649182041/100000000000000 : ℝ)*(base19) + (473378733/25000000000000 : ℝ)*(base23) + (220400251/100000000000000 : ℝ)*(upper3) + (55502041/100000000000000 : ℝ)*(lower4) + (409651/250000000000 : ℝ)*(upper5) + (415714566286503/20000000000000 : ℝ)*(major0) + (415714566286503/20000000000000 : ℝ)*(major1) + (415714566286503/20000000000000 : ℝ)*(major2) + (7439089393/50000000000000 : ℝ)*(sp1) + (17834664051/100000000000000 : ℝ)*(sp2) + (1379262514924083/50000000000000 : ℝ)*(sp4) + (1379254251243669/50000000000000 : ℝ)*(sp5) + (1379252650834591/50000000000000 : ℝ)*(sp6) + (87413772265693/6250000000000 : ℝ)*(sp7) + (87413772265693/6250000000000 : ℝ)*(f.failure) + (1379262514924083/50000000000000 : ℝ)*(f.sum) + (15008053902777/3810250000000000000000000000 : ℝ)*base65 + (137153178528763437/15241000000000000000000000000000 : ℝ)*base67 + (39037902259323437/15241000000000000000000000000000 : ℝ)*base69 + (123242744073765437/15241000000000000000000000000000 : ℝ)*base71 + (9058981526907/1524100000000000000000000000 : ℝ)*base73 + (255272671184703437/15241000000000000000000000000000 : ℝ)*base75 + (192477494510797437/15241000000000000000000000000000 : ℝ)*base77 + (123940838829382437/15241000000000000000000000000000 : ℝ)*base79 + (12054827462709/3810250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7006501/625000000000000000000 : ℝ)*base90 + (7006501/625000000000000000000 : ℝ)*base92 + (7006501/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1098_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (129/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4433/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8319/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1098_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1098_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4433/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8319/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1098_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1098_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1098_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4433/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8319/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1098_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
