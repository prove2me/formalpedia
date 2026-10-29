-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1730_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:06:21.484997+00:00
-- url     : https://prove2.me/submissions/87572428-f3c1-4596-b162-18e2ef0ef3d0

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
theorem support_rectangle_w1730_s0_0 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-319932237/2500000000 : ℝ)*x 0 + (707449643/1250000000 : ℝ)*x 1 + (2490110723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319932237/2500000000 : ℝ)^5463 ≤ (3982132147357/50000000000000 : ℝ)^4439 := by
    have hnat : (319932237 : ℕ)^5463*50000000000000^4439 ≤ 3982132147357^4439*2500000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319932237 2500000000 3982132147357 50000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (707449643/1250000000 : ℝ)^5463 ≤ (49631504790573/100000000000000 : ℝ)^4439 := by
    have hnat : (707449643 : ℕ)^5463*100000000000000^4439 ≤ 49631504790573^4439*1250000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707449643 1250000000 49631504790573 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2490110723/5000000000 : ℝ)^5463 ≤ (42404230903197/100000000000000 : ℝ)^4439 := by
    have hnat : (2490110723 : ℕ)^5463*100000000000000^4439 ≤ 42404230903197^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490110723 5000000000 42404230903197 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-319932237/2500000000 : ℝ), (707449643/1250000000 : ℝ), (2490110723/5000000000 : ℝ)] ![(3982132147357/50000000000000 : ℝ), (49631504790573/100000000000000 : ℝ), (42404230903197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-319932237/2500000000 : ℝ)|^5463 ≤ (3982132147357/50000000000000 : ℝ)^4439
        have hw : |(-319932237/2500000000 : ℝ)|=(319932237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(707449643/1250000000 : ℝ)|^5463 ≤ (49631504790573/100000000000000 : ℝ)^4439
        have hw : |(707449643/1250000000 : ℝ)|=(707449643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2490110723/5000000000 : ℝ)|^5463 ≤ (42404230903197/100000000000000 : ℝ)^4439
        have hw : |(2490110723/5000000000 : ℝ)|=(2490110723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s0_1 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695328819/5000000000 : ℝ)*x 0 + (-164533071/1000000000 : ℝ)*x 1 + (2490110363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695328819/5000000000 : ℝ)^5463 ≤ (5843138608173/12500000000000 : ℝ)^4439 := by
    have hnat : (2695328819 : ℕ)^5463*12500000000000^4439 ≤ 5843138608173^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695328819 5000000000 5843138608173 12500000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164533071/1000000000 : ℝ)^5463 ≤ (2712666940889/25000000000000 : ℝ)^4439 := by
    have hnat : (164533071 : ℕ)^5463*25000000000000^4439 ≤ 2712666940889^4439*1000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164533071 1000000000 2712666940889 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2490110363/5000000000 : ℝ)^5463 ≤ (10601055839637/25000000000000 : ℝ)^4439 := by
    have hnat : (2490110363 : ℕ)^5463*25000000000000^4439 ≤ 10601055839637^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490110363 5000000000 10601055839637 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695328819/5000000000 : ℝ), (-164533071/1000000000 : ℝ), (2490110363/5000000000 : ℝ)] ![(5843138608173/12500000000000 : ℝ), (2712666940889/25000000000000 : ℝ), (10601055839637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695328819/5000000000 : ℝ)|^5463 ≤ (5843138608173/12500000000000 : ℝ)^4439
        have hw : |(2695328819/5000000000 : ℝ)|=(2695328819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-164533071/1000000000 : ℝ)|^5463 ≤ (2712666940889/25000000000000 : ℝ)^4439
        have hw : |(-164533071/1000000000 : ℝ)|=(164533071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2490110363/5000000000 : ℝ)|^5463 ≤ (10601055839637/25000000000000 : ℝ)^4439
        have hw : |(2490110363/5000000000 : ℝ)|=(2490110363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s0_2 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215626243/400000000 : ℝ)*x 0 + (4980221737/10000000000 : ℝ)*x 1 + (-82266573/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215626243/400000000 : ℝ)^5463 ≤ (23372546092627/50000000000000 : ℝ)^4439 := by
    have hnat : (215626243 : ℕ)^5463*50000000000000^4439 ≤ 23372546092627^4439*400000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215626243 400000000 23372546092627 50000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4980221737/10000000000 : ℝ)^5463 ≤ (42404233952493/100000000000000 : ℝ)^4439 := by
    have hnat : (4980221737 : ℕ)^5463*100000000000000^4439 ≤ 42404233952493^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4980221737 10000000000 42404233952493 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82266573/500000000 : ℝ)^5463 ≤ (5425336925329/50000000000000 : ℝ)^4439 := by
    have hnat : (82266573 : ℕ)^5463*50000000000000^4439 ≤ 5425336925329^4439*500000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82266573 500000000 5425336925329 50000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215626243/400000000 : ℝ), (4980221737/10000000000 : ℝ), (-82266573/500000000 : ℝ)] ![(23372546092627/50000000000000 : ℝ), (42404233952493/100000000000000 : ℝ), (5425336925329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215626243/400000000 : ℝ)|^5463 ≤ (23372546092627/50000000000000 : ℝ)^4439
        have hw : |(215626243/400000000 : ℝ)|=(215626243/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4980221737/10000000000 : ℝ)|^5463 ≤ (42404233952493/100000000000000 : ℝ)^4439
        have hw : |(4980221737/10000000000 : ℝ)|=(4980221737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82266573/500000000 : ℝ)|^5463 ≤ (5425336925329/50000000000000 : ℝ)^4439
        have hw : |(-82266573/500000000 : ℝ)|=(82266573/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s0_3 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (804616253/2000000000 : ℝ)*x 0 + (3071764101/10000000000 : ℝ)*x 1 + (5131528743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804616253/2000000000 : ℝ)^5463 ≤ (2038062157553/6250000000000 : ℝ)^4439 := by
    have hnat : (804616253 : ℕ)^5463*6250000000000^4439 ≤ 2038062157553^4439*2000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804616253 2000000000 2038062157553 6250000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3071764101/10000000000 : ℝ)^5463 ≤ (23395760482881/100000000000000 : ℝ)^4439 := by
    have hnat : (3071764101 : ℕ)^5463*100000000000000^4439 ≤ 23395760482881^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071764101 10000000000 23395760482881 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5131528743/10000000000 : ℝ)^5463 ≤ (43995244989913/100000000000000 : ℝ)^4439 := by
    have hnat : (5131528743 : ℕ)^5463*100000000000000^4439 ≤ 43995244989913^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131528743 10000000000 43995244989913 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(804616253/2000000000 : ℝ), (3071764101/10000000000 : ℝ), (5131528743/10000000000 : ℝ)] ![(2038062157553/6250000000000 : ℝ), (23395760482881/100000000000000 : ℝ), (43995244989913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(804616253/2000000000 : ℝ)|^5463 ≤ (2038062157553/6250000000000 : ℝ)^4439
        have hw : |(804616253/2000000000 : ℝ)|=(804616253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3071764101/10000000000 : ℝ)|^5463 ≤ (23395760482881/100000000000000 : ℝ)^4439
        have hw : |(3071764101/10000000000 : ℝ)|=(3071764101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5131528743/10000000000 : ℝ)|^5463 ≤ (43995244989913/100000000000000 : ℝ)^4439
        have hw : |(5131528743/10000000000 : ℝ)|=(5131528743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s0_4 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1281116969/10000000000 : ℝ)*x 0 + (2498273889/5000000000 : ℝ)*x 1 + (705343557/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1281116969/10000000000 : ℝ)^5463 ≤ (7974896517653/100000000000000 : ℝ)^4439 := by
    have hnat : (1281116969 : ℕ)^5463*100000000000000^4439 ≤ 7974896517653^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281116969 10000000000 7974896517653 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498273889/5000000000 : ℝ)^5463 ≤ (8515074790097/20000000000000 : ℝ)^4439 := by
    have hnat : (2498273889 : ℕ)^5463*20000000000000^4439 ≤ 8515074790097^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498273889 5000000000 8515074790097 20000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (705343557/1250000000 : ℝ)^5463 ≤ (49449729518463/100000000000000 : ℝ)^4439 := by
    have hnat : (705343557 : ℕ)^5463*100000000000000^4439 ≤ 49449729518463^4439*1250000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705343557 1250000000 49449729518463 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1281116969/10000000000 : ℝ), (2498273889/5000000000 : ℝ), (705343557/1250000000 : ℝ)] ![(7974896517653/100000000000000 : ℝ), (8515074790097/20000000000000 : ℝ), (49449729518463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1281116969/10000000000 : ℝ)|^5463 ≤ (7974896517653/100000000000000 : ℝ)^4439
        have hw : |(-1281116969/10000000000 : ℝ)|=(1281116969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498273889/5000000000 : ℝ)|^5463 ≤ (8515074790097/20000000000000 : ℝ)^4439
        have hw : |(2498273889/5000000000 : ℝ)|=(2498273889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(705343557/1250000000 : ℝ)|^5463 ≤ (49449729518463/100000000000000 : ℝ)^4439
        have hw : |(705343557/1250000000 : ℝ)|=(705343557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s0_5 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2603610877/5000000000 : ℝ)*x 0 + (-491401651/5000000000 : ℝ)*x 1 + (5642748671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2603610877/5000000000 : ℝ)^5463 ≤ (44795256616647/100000000000000 : ℝ)^4439 := by
    have hnat : (2603610877 : ℕ)^5463*100000000000000^4439 ≤ 44795256616647^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603610877 5000000000 44795256616647 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491401651/5000000000 : ℝ)^5463 ≤ (719376441447/12500000000000 : ℝ)^4439 := by
    have hnat : (491401651 : ℕ)^5463*12500000000000^4439 ≤ 719376441447^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491401651 5000000000 719376441447 12500000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5642748671/10000000000 : ℝ)^5463 ≤ (49449731837233/100000000000000 : ℝ)^4439 := by
    have hnat : (5642748671 : ℕ)^5463*100000000000000^4439 ≤ 49449731837233^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5642748671 10000000000 49449731837233 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2603610877/5000000000 : ℝ), (-491401651/5000000000 : ℝ), (5642748671/10000000000 : ℝ)] ![(44795256616647/100000000000000 : ℝ), (719376441447/12500000000000 : ℝ), (49449731837233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2603610877/5000000000 : ℝ)|^5463 ≤ (44795256616647/100000000000000 : ℝ)^4439
        have hw : |(2603610877/5000000000 : ℝ)|=(2603610877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491401651/5000000000 : ℝ)|^5463 ≤ (719376441447/12500000000000 : ℝ)^4439
        have hw : |(-491401651/5000000000 : ℝ)|=(491401651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5642748671/10000000000 : ℝ)|^5463 ≤ (49449731837233/100000000000000 : ℝ)^4439
        have hw : |(5642748671/10000000000 : ℝ)|=(5642748671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s0_6 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2603610657/5000000000 : ℝ)*x 0 + (352671783/625000000 : ℝ)*x 1 + (-491402081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2603610657/5000000000 : ℝ)^5463 ≤ (44795251958377/100000000000000 : ℝ)^4439 := by
    have hnat : (2603610657 : ℕ)^5463*100000000000000^4439 ≤ 44795251958377^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603610657 5000000000 44795251958377 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352671783/625000000 : ℝ)^5463 ≤ (49449730294981/100000000000000 : ℝ)^4439 := by
    have hnat : (352671783 : ℕ)^5463*100000000000000^4439 ≤ 49449730294981^4439*625000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352671783 625000000 49449730294981 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491402081/5000000000 : ℝ)^5463 ≤ (1151003545837/20000000000000 : ℝ)^4439 := by
    have hnat : (491402081 : ℕ)^5463*20000000000000^4439 ≤ 1151003545837^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491402081 5000000000 1151003545837 20000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2603610657/5000000000 : ℝ), (352671783/625000000 : ℝ), (-491402081/5000000000 : ℝ)] ![(44795251958377/100000000000000 : ℝ), (49449730294981/100000000000000 : ℝ), (1151003545837/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2603610657/5000000000 : ℝ)|^5463 ≤ (44795251958377/100000000000000 : ℝ)^4439
        have hw : |(2603610657/5000000000 : ℝ)|=(2603610657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(352671783/625000000 : ℝ)|^5463 ≤ (49449730294981/100000000000000 : ℝ)^4439
        have hw : |(352671783/625000000 : ℝ)|=(352671783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491402081/5000000000 : ℝ)|^5463 ≤ (1151003545837/20000000000000 : ℝ)^4439
        have hw : |(-491402081/5000000000 : ℝ)|=(491402081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s0_7 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1006821637/2500000000 : ℝ)*x 0 + (2541016059/5000000000 : ℝ)*x 1 + (3122845219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006821637/2500000000 : ℝ)^5463 ≤ (16325474205129/50000000000000 : ℝ)^4439 := by
    have hnat : (1006821637 : ℕ)^5463*50000000000000^4439 ≤ 16325474205129^4439*2500000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006821637 2500000000 16325474205129 50000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541016059/5000000000 : ℝ)^5463 ≤ (43473574849967/100000000000000 : ℝ)^4439 := by
    have hnat : (2541016059 : ℕ)^5463*100000000000000^4439 ≤ 43473574849967^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541016059 5000000000 43473574849967 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3122845219/10000000000 : ℝ)^5463 ≤ (5968869183647/25000000000000 : ℝ)^4439 := by
    have hnat : (3122845219 : ℕ)^5463*25000000000000^4439 ≤ 5968869183647^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122845219 10000000000 5968869183647 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1006821637/2500000000 : ℝ), (2541016059/5000000000 : ℝ), (3122845219/10000000000 : ℝ)] ![(16325474205129/50000000000000 : ℝ), (43473574849967/100000000000000 : ℝ), (5968869183647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1006821637/2500000000 : ℝ)|^5463 ≤ (16325474205129/50000000000000 : ℝ)^4439
        have hw : |(1006821637/2500000000 : ℝ)|=(1006821637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2541016059/5000000000 : ℝ)|^5463 ≤ (43473574849967/100000000000000 : ℝ)^4439
        have hw : |(2541016059/5000000000 : ℝ)|=(2541016059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3122845219/10000000000 : ℝ)|^5463 ≤ (5968869183647/25000000000000 : ℝ)^4439
        have hw : |(3122845219/10000000000 : ℝ)|=(3122845219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1730_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (201592627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6599/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4247/20000 : ℝ)*pair X 0 0 := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (5455/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5455 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5455*1^1024 ≤ 0^1024*1^5455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5455/1024 : ℝ) ≤ (379388802671340333/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5455 ≤ (379388802671340333/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5455*50000000000000000000^1024 ≤ 379388802671340333^1024*5^5455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 379388802671340333 50000000000000000000 5455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (379388802671340333/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5455/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5455 := by
      have hnat : (1 : ℕ)^1024*1^5455 ≤ 1^5455*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50379388802671340333/50000000000000000000 : ℝ) ≤ (10014199903466791/10000000000000000 : ℝ) ^ (5455/1024 : ℝ) := by
    have hpowers : (50379388802671340333/50000000000000000000 : ℝ)^1024 ≤ (10014199903466791/10000000000000000 : ℝ)^5455 := by
      have hnat : (50379388802671340333 : ℕ)^1024*10000000000000000^5455 ≤ 10014199903466791^5455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50379388802671340333 50000000000000000000 10014199903466791 10000000000000000 1024 5455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014199903466791/10000000000000000 : ℝ)) (X := (50379388802671340333/50000000000000000000 : ℝ)) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25379388802671340333/25000000000000000000 : ℝ) ≤ (5014199903466791/5000000000000000 : ℝ) ^ (5455/1024 : ℝ) := by
    have hpowers : (25379388802671340333/25000000000000000000 : ℝ)^1024 ≤ (5014199903466791/5000000000000000 : ℝ)^5455 := by
      have hnat : (25379388802671340333 : ℕ)^1024*5000000000000000^5455 ≤ 5014199903466791^5455*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25379388802671340333 25000000000000000000 5014199903466791 5000000000000000 1024 5455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014199903466791/5000000000000000 : ℝ)) (X := (25379388802671340333/25000000000000000000 : ℝ)) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14199903466791/4000000000000000 : ℝ)*(0 : ℝ))^(5455/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14199903466791/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(379388802671340333/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14199903466791/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5455/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14199903466791/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10014199903466791/10000000000000000 : ℝ) by norm_num, show 1+(379388802671340333/50000000000000000000 : ℝ)+(0 : ℝ)=(50379388802671340333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(379388802671340333/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14199903466791/4000000000000000 : ℝ)*(2/5 : ℝ))^(5455/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14199903466791/4000000000000000 : ℝ)*(2/5 : ℝ)=(5014199903466791/5000000000000000 : ℝ) by norm_num, show 1+2*(379388802671340333/50000000000000000000 : ℝ)=(25379388802671340333/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14199903466791/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5455/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14199903466791/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14199903466791/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5455/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14199903466791/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14199903466791/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5455/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14199903466791/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-319932237/2500000000 : ℝ)*X 0 0+(707449643/1250000000 : ℝ)*X 0 1+(2490110723/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2695328819/5000000000 : ℝ)*X 1 0+(-164533071/1000000000 : ℝ)*X 1 1+(2490110363/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((215626243/400000000 : ℝ)*X 2 0+(4980221737/10000000000 : ℝ)*X 2 1+(-82266573/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((804616253/2000000000 : ℝ)*X 0 0+(3071764101/10000000000 : ℝ)*X 0 1+(5131528743/10000000000 : ℝ)*X 0 2+(804616253/2000000000 : ℝ)*X 1 0+(3071764101/10000000000 : ℝ)*X 1 1+(5131528743/10000000000 : ℝ)*X 1 2+(804616253/2000000000 : ℝ)*X 2 0+(3071764101/10000000000 : ℝ)*X 2 1+(5131528743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1281116969/10000000000 : ℝ)*X 0 0+(2498273889/5000000000 : ℝ)*X 0 1+(705343557/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2603610877/5000000000 : ℝ)*X 1 0+(-491401651/5000000000 : ℝ)*X 1 1+(5642748671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2603610657/5000000000 : ℝ)*X 2 0+(352671783/625000000 : ℝ)*X 2 1+(-491402081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1006821637/2500000000 : ℝ)*X 0 0+(2541016059/5000000000 : ℝ)*X 0 1+(3122845219/10000000000 : ℝ)*X 0 2+(1006821637/2500000000 : ℝ)*X 1 0+(2541016059/5000000000 : ℝ)*X 1 1+(3122845219/10000000000 : ℝ)*X 1 2+(1006821637/2500000000 : ℝ)*X 2 0+(2541016059/5000000000 : ℝ)*X 2 1+(3122845219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (287857561620656554115427/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7106131/4000000000000 : ℝ)*(base1) + (37405851/6250000000000 : ℝ)*(base19) + (113781329/100000000000000 : ℝ)*(base23) + (23819319/100000000000000 : ℝ)*(base37) + (52987779/50000000000000 : ℝ)*(upper3) + (58729/781250000000 : ℝ)*(upper5) + (978716771795401/100000000000000 : ℝ)*(major0) + (978716771795401/100000000000000 : ℝ)*(major1) + (978716771795401/100000000000000 : ℝ)*(major2) + (1471941328453331/100000000000000 : ℝ)*(sp0) + (1471940552306439/100000000000000 : ℝ)*(sp1) + (1471939334646997/100000000000000 : ℝ)*(sp2) + (485492143341883/100000000000000 : ℝ)*(sp3) + (1702371729/100000000000000 : ℝ)*(sp6) + (121373086203619/25000000000000 : ℝ)*(f.failure) + (183992643850007/12500000000000 : ℝ)*(f.sum) + (37209991371809/200000000000000000000000000000 : ℝ)*base66 + (637057711228191/400000000000000000000000000000 : ℝ)*base67 + (3887962627971809/400000000000000000000000000000 : ℝ)*base70 + (851048019228191/400000000000000000000000000000 : ℝ)*base71 + (620329151428191/200000000000000000000000000000 : ℝ)*base73 + (1890150136828191/400000000000000000000000000000 : ℝ)*base75 + (832464979628191/400000000000000000000000000000 : ℝ)*base77 + (4021116896428191/400000000000000000000000000000 : ℝ)*base79 + (1189187020171809/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13882887/2500000000000000000000 : ℝ)*base90 + (13882887/2500000000000000000000 : ℝ)*base92 + (13882887/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1903958893889724039348219/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1004619791/50000000000000 : ℝ)*(base19) + (1842587979/100000000000000 : ℝ)*(base23) + (9400737/100000000000000 : ℝ)*(upper2) + (5393487/1562500000000 : ℝ)*(upper3) + (135037203/50000000000000 : ℝ)*(upper5) + (1028960951739099/100000000000000 : ℝ)*(major0) + (1028960951739099/100000000000000 : ℝ)*(major1) + (1028960951739099/100000000000000 : ℝ)*(major2) + (8506273449/100000000000000 : ℝ)*(sp1) + (3487502099/50000000000000 : ℝ)*(sp2) + (773752810757361/50000000000000 : ℝ)*(sp4) + (1547495106001691/100000000000000 : ℝ)*(sp5) + (773748401961273/50000000000000 : ℝ)*(sp6) + (51041596463699/10000000000000 : ℝ)*(sp7) + (51041596463699/10000000000000 : ℝ)*(f.failure) + (773752810757361/50000000000000 : ℝ)*(f.sum) + (260192062361309/200000000000000000000000000000 : ℝ)*base65 + (1161037628361309/400000000000000000000000000000 : ℝ)*base67 + (103202625961309/400000000000000000000000000000 : ℝ)*base69 + (855129355638691/400000000000000000000000000000 : ℝ)*base72 + (566502173161309/200000000000000000000000000000 : ℝ)*base73 + (182987664761309/400000000000000000000000000000 : ℝ)*base75 + (2187572882838691/400000000000000000000000000000 : ℝ)*base78 + (3002952970838691/400000000000000000000000000000 : ℝ)*base80 + (487501587161309/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1547273/1000000000000000000000 : ℝ)*base89 + (1547273/1000000000000000000000 : ℝ)*base91 + (1547273/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1730_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (201592627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6599/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4247/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1730_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1730_s1_0 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-670316427/5000000000 : ℝ)*x 0 + (1093455961/2000000000 : ℝ)*x 1 + (5132225299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670316427/5000000000 : ℝ)^5463 ≤ (8433259016361/100000000000000 : ℝ)^4439 := by
    have hnat : (670316427 : ℕ)^5463*100000000000000^4439 ≤ 8433259016361^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670316427 5000000000 8433259016361 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093455961/2000000000 : ℝ)^5463 ≤ (47564146307679/100000000000000 : ℝ)^4439 := by
    have hnat : (1093455961 : ℕ)^5463*100000000000000^4439 ≤ 47564146307679^4439*2000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093455961 2000000000 47564146307679 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5132225299/10000000000 : ℝ)^5463 ≤ (11000648665093/25000000000000 : ℝ)^4439 := by
    have hnat : (5132225299 : ℕ)^5463*25000000000000^4439 ≤ 11000648665093^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132225299 10000000000 11000648665093 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-670316427/5000000000 : ℝ), (1093455961/2000000000 : ℝ), (5132225299/10000000000 : ℝ)] ![(8433259016361/100000000000000 : ℝ), (47564146307679/100000000000000 : ℝ), (11000648665093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-670316427/5000000000 : ℝ)|^5463 ≤ (8433259016361/100000000000000 : ℝ)^4439
        have hw : |(-670316427/5000000000 : ℝ)|=(670316427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093455961/2000000000 : ℝ)|^5463 ≤ (47564146307679/100000000000000 : ℝ)^4439
        have hw : |(1093455961/2000000000 : ℝ)|=(1093455961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5132225299/10000000000 : ℝ)|^5463 ≤ (11000648665093/25000000000000 : ℝ)^4439
        have hw : |(5132225299/10000000000 : ℝ)|=(5132225299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s1_1 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533944957/1000000000 : ℝ)*x 0 + (-1514427027/10000000000 : ℝ)*x 1 + (5132224403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533944957/1000000000 : ℝ)^5463 ≤ (4619922331347/10000000000000 : ℝ)^4439 := by
    have hnat : (533944957 : ℕ)^5463*10000000000000^4439 ≤ 4619922331347^4439*1000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533944957 1000000000 4619922331347 10000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1514427027/10000000000 : ℝ)^5463 ≤ (4899095728459/50000000000000 : ℝ)^4439 := by
    have hnat : (1514427027 : ℕ)^5463*50000000000000^4439 ≤ 4899095728459^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514427027 10000000000 4899095728459 50000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5132224403/10000000000 : ℝ)^5463 ≤ (11000646301533/25000000000000 : ℝ)^4439 := by
    have hnat : (5132224403 : ℕ)^5463*25000000000000^4439 ≤ 11000646301533^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132224403 10000000000 11000646301533 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533944957/1000000000 : ℝ), (-1514427027/10000000000 : ℝ), (5132224403/10000000000 : ℝ)] ![(4619922331347/10000000000000 : ℝ), (4899095728459/50000000000000 : ℝ), (11000646301533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533944957/1000000000 : ℝ)|^5463 ≤ (4619922331347/10000000000000 : ℝ)^4439
        have hw : |(533944957/1000000000 : ℝ)|=(533944957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1514427027/10000000000 : ℝ)|^5463 ≤ (4899095728459/50000000000000 : ℝ)^4439
        have hw : |(-1514427027/10000000000 : ℝ)|=(1514427027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5132224403/10000000000 : ℝ)|^5463 ≤ (11000646301533/25000000000000 : ℝ)^4439
        have hw : |(5132224403/10000000000 : ℝ)|=(5132224403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s1_2 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339448151/10000000000 : ℝ)*x 0 + (641528171/1250000000 : ℝ)*x 1 + (-1514427647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339448151/10000000000 : ℝ)^5463 ≤ (9239841640679/20000000000000 : ℝ)^4439 := by
    have hnat : (5339448151 : ℕ)^5463*20000000000000^4439 ≤ 9239841640679^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339448151 10000000000 9239841640679 20000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641528171/1250000000 : ℝ)^5463 ≤ (44002595388433/100000000000000 : ℝ)^4439 := by
    have hnat : (641528171 : ℕ)^5463*100000000000000^4439 ≤ 44002595388433^4439*1250000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641528171 1250000000 44002595388433 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1514427647/10000000000 : ℝ)^5463 ≤ (4899098196801/50000000000000 : ℝ)^4439 := by
    have hnat : (1514427647 : ℕ)^5463*50000000000000^4439 ≤ 4899098196801^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514427647 10000000000 4899098196801 50000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339448151/10000000000 : ℝ), (641528171/1250000000 : ℝ), (-1514427647/10000000000 : ℝ)] ![(9239841640679/20000000000000 : ℝ), (44002595388433/100000000000000 : ℝ), (4899098196801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339448151/10000000000 : ℝ)|^5463 ≤ (9239841640679/20000000000000 : ℝ)^4439
        have hw : |(5339448151/10000000000 : ℝ)|=(5339448151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641528171/1250000000 : ℝ)|^5463 ≤ (44002595388433/100000000000000 : ℝ)^4439
        have hw : |(641528171/1250000000 : ℝ)|=(641528171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1514427647/10000000000 : ℝ)|^5463 ≤ (4899098196801/50000000000000 : ℝ)^4439
        have hw : |(-1514427647/10000000000 : ℝ)|=(1514427647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s1_3 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4078024347/10000000000 : ℝ)*x 0 + (1794554631/5000000000 : ℝ)*x 1 + (4604940103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4078024347/10000000000 : ℝ)^5463 ≤ (16578963460419/50000000000000 : ℝ)^4439 := by
    have hnat : (4078024347 : ℕ)^5463*50000000000000^4439 ≤ 16578963460419^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4078024347 10000000000 16578963460419 50000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1794554631/5000000000 : ℝ)^5463 ≤ (28335433156909/100000000000000 : ℝ)^4439 := by
    have hnat : (1794554631 : ℕ)^5463*100000000000000^4439 ≤ 28335433156909^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794554631 5000000000 28335433156909 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4604940103/10000000000 : ℝ)^5463 ≤ (38506639907123/100000000000000 : ℝ)^4439 := by
    have hnat : (4604940103 : ℕ)^5463*100000000000000^4439 ≤ 38506639907123^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4604940103 10000000000 38506639907123 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4078024347/10000000000 : ℝ), (1794554631/5000000000 : ℝ), (4604940103/10000000000 : ℝ)] ![(16578963460419/50000000000000 : ℝ), (28335433156909/100000000000000 : ℝ), (38506639907123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4078024347/10000000000 : ℝ)|^5463 ≤ (16578963460419/50000000000000 : ℝ)^4439
        have hw : |(4078024347/10000000000 : ℝ)|=(4078024347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1794554631/5000000000 : ℝ)|^5463 ≤ (28335433156909/100000000000000 : ℝ)^4439
        have hw : |(1794554631/5000000000 : ℝ)|=(1794554631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4604940103/10000000000 : ℝ)|^5463 ≤ (38506639907123/100000000000000 : ℝ)^4439
        have hw : |(4604940103/10000000000 : ℝ)|=(4604940103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s1_4 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-268159951/2000000000 : ℝ)*x 0 + (5136210623/10000000000 : ℝ)*x 1 + (5463230821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268159951/2000000000 : ℝ)^5463 ≤ (8434551118399/100000000000000 : ℝ)^4439 := by
    have hnat : (268159951 : ℕ)^5463*100000000000000^4439 ≤ 8434551118399^4439*2000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268159951 2000000000 8434551118399 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136210623/10000000000 : ℝ)^5463 ≤ (5505581250081/12500000000000 : ℝ)^4439 := by
    have hnat : (5136210623 : ℕ)^5463*12500000000000^4439 ≤ 5505581250081^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136210623 10000000000 5505581250081 12500000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463230821/10000000000 : ℝ)^5463 ≤ (11880199717883/25000000000000 : ℝ)^4439 := by
    have hnat : (5463230821 : ℕ)^5463*25000000000000^4439 ≤ 11880199717883^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463230821 10000000000 11880199717883 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268159951/2000000000 : ℝ), (5136210623/10000000000 : ℝ), (5463230821/10000000000 : ℝ)] ![(8434551118399/100000000000000 : ℝ), (5505581250081/12500000000000 : ℝ), (11880199717883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268159951/2000000000 : ℝ)|^5463 ≤ (8434551118399/100000000000000 : ℝ)^4439
        have hw : |(-268159951/2000000000 : ℝ)|=(268159951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136210623/10000000000 : ℝ)|^5463 ≤ (5505581250081/12500000000000 : ℝ)^4439
        have hw : |(5136210623/10000000000 : ℝ)|=(5136210623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463230821/10000000000 : ℝ)|^5463 ≤ (11880199717883/25000000000000 : ℝ)^4439
        have hw : |(5463230821/10000000000 : ℝ)|=(5463230821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s1_5 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524975997/1000000000 : ℝ)*x 0 + (-591710979/5000000000 : ℝ)*x 1 + (1092646037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524975997/1000000000 : ℝ)^5463 ≤ (45246031224203/100000000000000 : ℝ)^4439 := by
    have hnat : (524975997 : ℕ)^5463*100000000000000^4439 ≤ 45246031224203^4439*1000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524975997 1000000000 45246031224203 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (591710979/5000000000 : ℝ)^5463 ≤ (1808294174247/25000000000000 : ℝ)^4439 := by
    have hnat : (591710979 : ℕ)^5463*25000000000000^4439 ≤ 1808294174247^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591710979 5000000000 1808294174247 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092646037/2000000000 : ℝ)^5463 ≤ (47520792063253/100000000000000 : ℝ)^4439 := by
    have hnat : (1092646037 : ℕ)^5463*100000000000000^4439 ≤ 47520792063253^4439*2000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092646037 2000000000 47520792063253 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524975997/1000000000 : ℝ), (-591710979/5000000000 : ℝ), (1092646037/2000000000 : ℝ)] ![(45246031224203/100000000000000 : ℝ), (1808294174247/25000000000000 : ℝ), (47520792063253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524975997/1000000000 : ℝ)|^5463 ≤ (45246031224203/100000000000000 : ℝ)^4439
        have hw : |(524975997/1000000000 : ℝ)|=(524975997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-591710979/5000000000 : ℝ)|^5463 ≤ (1808294174247/25000000000000 : ℝ)^4439
        have hw : |(-591710979/5000000000 : ℝ)|=(591710979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092646037/2000000000 : ℝ)|^5463 ≤ (47520792063253/100000000000000 : ℝ)^4439
        have hw : |(1092646037/2000000000 : ℝ)|=(1092646037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s1_6 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524975993/1000000000 : ℝ)*x 0 + (2731614951/5000000000 : ℝ)*x 1 + (-1183422417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524975993/1000000000 : ℝ)^5463 ≤ (5655753849991/12500000000000 : ℝ)^4439 := by
    have hnat : (524975993 : ℕ)^5463*12500000000000^4439 ≤ 5655753849991^4439*1000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524975993 1000000000 5655753849991 12500000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731614951/5000000000 : ℝ)^5463 ≤ (47520789033783/100000000000000 : ℝ)^4439 := by
    have hnat : (2731614951 : ℕ)^5463*100000000000000^4439 ≤ 47520789033783^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731614951 5000000000 47520789033783 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183422417/10000000000 : ℝ)^5463 ≤ (1808295037401/25000000000000 : ℝ)^4439 := by
    have hnat : (1183422417 : ℕ)^5463*25000000000000^4439 ≤ 1808295037401^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183422417 10000000000 1808295037401 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524975993/1000000000 : ℝ), (2731614951/5000000000 : ℝ), (-1183422417/10000000000 : ℝ)] ![(5655753849991/12500000000000 : ℝ), (47520789033783/100000000000000 : ℝ), (1808295037401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524975993/1000000000 : ℝ)|^5463 ≤ (5655753849991/12500000000000 : ℝ)^4439
        have hw : |(524975993/1000000000 : ℝ)|=(524975993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731614951/5000000000 : ℝ)|^5463 ≤ (47520789033783/100000000000000 : ℝ)^4439
        have hw : |(2731614951/5000000000 : ℝ)|=(2731614951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1183422417/10000000000 : ℝ)|^5463 ≤ (1808295037401/25000000000000 : ℝ)^4439
        have hw : |(-1183422417/10000000000 : ℝ)|=(1183422417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s1_7 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1019631453/2500000000 : ℝ)*x 0 + (2296428099/5000000000 : ℝ)*x 1 + (144055323/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019631453/2500000000 : ℝ)^5463 ≤ (33162944917837/100000000000000 : ℝ)^4439 := by
    have hnat : (1019631453 : ℕ)^5463*100000000000000^4439 ≤ 33162944917837^4439*2500000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019631453 2500000000 33162944917837 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296428099/5000000000 : ℝ)^5463 ≤ (3838232207167/10000000000000 : ℝ)^4439 := by
    have hnat : (2296428099 : ℕ)^5463*10000000000000^4439 ≤ 3838232207167^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296428099 5000000000 3838232207167 10000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (144055323/400000000 : ℝ)^5463 ≤ (7113683248607/25000000000000 : ℝ)^4439 := by
    have hnat : (144055323 : ℕ)^5463*25000000000000^4439 ≤ 7113683248607^4439*400000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144055323 400000000 7113683248607 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1019631453/2500000000 : ℝ), (2296428099/5000000000 : ℝ), (144055323/400000000 : ℝ)] ![(33162944917837/100000000000000 : ℝ), (3838232207167/10000000000000 : ℝ), (7113683248607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1019631453/2500000000 : ℝ)|^5463 ≤ (33162944917837/100000000000000 : ℝ)^4439
        have hw : |(1019631453/2500000000 : ℝ)|=(1019631453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2296428099/5000000000 : ℝ)|^5463 ≤ (3838232207167/10000000000000 : ℝ)^4439
        have hw : |(2296428099/5000000000 : ℝ)|=(2296428099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(144055323/400000000 : ℝ)|^5463 ≤ (7113683248607/25000000000000 : ℝ)^4439
        have hw : |(144055323/400000000 : ℝ)|=(144055323/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1730_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (201592627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4247/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9977/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8577/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4247/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4247/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4247/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4247/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4247/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4247/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6599/100000 : ℝ) ^ (5455/1024 : ℝ) ≤ (51426238079273/100000000000000000000 : ℝ) := by
    have hpowers : (6599/100000 : ℝ)^5455 ≤ (51426238079273/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6599 : ℕ)^5455*100000000000000000000^1024 ≤ 51426238079273^1024*100000^5455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6599 100000 51426238079273 100000000000000000000 5455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6599/100000 : ℝ)) (X := (51426238079273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4247/20000 : ℝ) ^ (5455/1024 : ℝ) ≤ (26008034148480369/100000000000000000000 : ℝ) := by
    have hpowers : (4247/20000 : ℝ)^5455 ≤ (26008034148480369/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4247 : ℕ)^5455*100000000000000000000^1024 ≤ 26008034148480369^1024*20000^5455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4247 20000 26008034148480369 100000000000000000000 5455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4247/20000 : ℝ)) (X := (26008034148480369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000051426238079273/50000000000000000000 : ℝ) ≤ (10000001930722119/10000000000000000 : ℝ) ^ (5455/1024 : ℝ) := by
    have hpowers : (50000051426238079273/50000000000000000000 : ℝ)^1024 ≤ (10000001930722119/10000000000000000 : ℝ)^5455 := by
      have hnat : (50000051426238079273 : ℕ)^1024*10000000000000000^5455 ≤ 10000001930722119^5455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000051426238079273 50000000000000000000 10000001930722119 10000000000000000 1024 5455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001930722119/10000000000000000 : ℝ)) (X := (50000051426238079273/50000000000000000000 : ℝ)) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013029730193279821/50000000000000000000 : ℝ) ≤ (2000097826081027/2000000000000000 : ℝ) ^ (5455/1024 : ℝ) := by
    have hpowers : (50013029730193279821/50000000000000000000 : ℝ)^1024 ≤ (2000097826081027/2000000000000000 : ℝ)^5455 := by
      have hnat : (50013029730193279821 : ℕ)^1024*2000000000000000^5455 ≤ 2000097826081027^5455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013029730193279821 50000000000000000000 2000097826081027 2000000000000000 1024 5455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000097826081027/2000000000000000 : ℝ)) (X := (50013029730193279821/50000000000000000000 : ℝ)) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026008034148480369/50000000000000000000 : ℝ) ≤ (10000976330088151/10000000000000000 : ℝ) ^ (5455/1024 : ℝ) := by
    have hpowers : (50026008034148480369/50000000000000000000 : ℝ)^1024 ≤ (10000976330088151/10000000000000000 : ℝ)^5455 := by
      have hnat : (50026008034148480369 : ℕ)^1024*10000000000000000^5455 ≤ 10000976330088151^5455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026008034148480369 50000000000000000000 10000976330088151 10000000000000000 1024 5455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000976330088151/10000000000000000 : ℝ)) (X := (50026008034148480369/50000000000000000000 : ℝ)) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51426238079273/100000000000000000000 : ℝ) ≤ ((36588399549158122129/36590000000000000000 : ℝ)+2*(60899960377/182950000000000 : ℝ)*(6599/100000 : ℝ))^(5455/1024 : ℝ) := by
    rw [show (36588399549158122129/36590000000000000000 : ℝ)+2*(60899960377/182950000000000 : ℝ)*(6599/100000 : ℝ)=(10000001930722119/10000000000000000 : ℝ) by norm_num, show 1+2*(51426238079273/100000000000000000000 : ℝ)=(50000051426238079273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26008034148480369/100000000000000000000 : ℝ)+(51426238079273/100000000000000000000 : ℝ) ≤ ((36588399549158122129/36590000000000000000 : ℝ)+(60899960377/182950000000000 : ℝ)*((4247/20000 : ℝ)+(6599/100000 : ℝ)))^(5455/1024 : ℝ) := by
    rw [show (36588399549158122129/36590000000000000000 : ℝ)+(60899960377/182950000000000 : ℝ)*((4247/20000 : ℝ)+(6599/100000 : ℝ))=(2000097826081027/2000000000000000 : ℝ) by norm_num, show 1+(26008034148480369/100000000000000000000 : ℝ)+(51426238079273/100000000000000000000 : ℝ)=(50013029730193279821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26008034148480369/100000000000000000000 : ℝ) ≤ ((36588399549158122129/36590000000000000000 : ℝ)+2*(60899960377/182950000000000 : ℝ)*(4247/20000 : ℝ))^(5455/1024 : ℝ) := by
    rw [show (36588399549158122129/36590000000000000000 : ℝ)+2*(60899960377/182950000000000 : ℝ)*(4247/20000 : ℝ)=(10000976330088151/10000000000000000 : ℝ) by norm_num, show 1+2*(26008034148480369/100000000000000000000 : ℝ)=(50026008034148480369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36588399549158122129/36590000000000000000 : ℝ)*(X 1 0+X 2 0)+(60899960377/182950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5455/1024 : ℝ)) (lo := (6599/100000 : ℝ)) (hi := (4247/20000 : ℝ)) (c := (36588399549158122129/36590000000000000000 : ℝ)) (alpha := (60899960377/182950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36588399549158122129/36590000000000000000 : ℝ)*(X 0 1+X 2 1)+(60899960377/182950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5455/1024 : ℝ)) (lo := (6599/100000 : ℝ)) (hi := (4247/20000 : ℝ)) (c := (36588399549158122129/36590000000000000000 : ℝ)) (alpha := (60899960377/182950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36588399549158122129/36590000000000000000 : ℝ)*(X 0 2+X 1 2)+(60899960377/182950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5455/1024 : ℝ)) (lo := (6599/100000 : ℝ)) (hi := (4247/20000 : ℝ)) (c := (36588399549158122129/36590000000000000000 : ℝ)) (alpha := (60899960377/182950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-670316427/5000000000 : ℝ)*X 0 0+(1093455961/2000000000 : ℝ)*X 0 1+(5132225299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((533944957/1000000000 : ℝ)*X 1 0+(-1514427027/10000000000 : ℝ)*X 1 1+(5132224403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5339448151/10000000000 : ℝ)*X 2 0+(641528171/1250000000 : ℝ)*X 2 1+(-1514427647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4078024347/10000000000 : ℝ)*X 0 0+(1794554631/5000000000 : ℝ)*X 0 1+(4604940103/10000000000 : ℝ)*X 0 2+(4078024347/10000000000 : ℝ)*X 1 0+(1794554631/5000000000 : ℝ)*X 1 1+(4604940103/10000000000 : ℝ)*X 1 2+(4078024347/10000000000 : ℝ)*X 2 0+(1794554631/5000000000 : ℝ)*X 2 1+(4604940103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-268159951/2000000000 : ℝ)*X 0 0+(5136210623/10000000000 : ℝ)*X 0 1+(5463230821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((524975997/1000000000 : ℝ)*X 1 0+(-591710979/5000000000 : ℝ)*X 1 1+(1092646037/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((524975993/1000000000 : ℝ)*X 2 0+(2731614951/5000000000 : ℝ)*X 2 1+(-1183422417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1019631453/2500000000 : ℝ)*X 0 0+(2296428099/5000000000 : ℝ)*X 0 1+(144055323/400000000 : ℝ)*X 0 2+(1019631453/2500000000 : ℝ)*X 1 0+(2296428099/5000000000 : ℝ)*X 1 1+(144055323/400000000 : ℝ)*X 1 2+(1019631453/2500000000 : ℝ)*X 2 0+(2296428099/5000000000 : ℝ)*X 2 1+(144055323/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5195519712402454062592509669/914750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (937365061/100000000000000 : ℝ)*(base19) + (63432397/50000000000000 : ℝ)*(lower2) + (52015753/50000000000000 : ℝ)*(lower4) + (12587651/12500000000000 : ℝ)*(lower5) + (992255167755971/50000000000000 : ℝ)*(major0) + (992255167755971/50000000000000 : ℝ)*(major1) + (992255167755971/50000000000000 : ℝ)*(major2) + (149229929583463/5000000000000 : ℝ)*(sp0) + (1492301680091343/50000000000000 : ℝ)*(sp1) + (1492299129831793/50000000000000 : ℝ)*(sp2) + (123052016152849/12500000000000 : ℝ)*(sp3) + (720100997/12500000000000 : ℝ)*(sp4) + (54929489/100000000000000 : ℝ)*(sp5) + (121856273/2000000000000 : ℝ)*(sp6) + (123052016152849/12500000000000 : ℝ)*(f.failure) + (746151088119309/25000000000000 : ℝ)*(f.sum) + (40389600128897/4573750000000000000000000000 : ℝ)*base65 + (603696579766382259/1829500000000000000000000000000000 : ℝ)*base67 + (2051669429846382259/1829500000000000000000000000000000 : ℝ)*base69 + (9108503617667382259/1829500000000000000000000000000000 : ℝ)*base71 + (16260513436033/4573750000000000000000000000 : ℝ)*base74 + (7868976524079882259/1829500000000000000000000000000000 : ℝ)*base75 + (4593528800605382259/1829500000000000000000000000000000 : ℝ)*base77 + (5402130036066382259/1829500000000000000000000000000000 : ℝ)*base79 + (996756479003/4573750000000000000000000000 : ℝ)*base82 + (11555677/1250000000000000000000 : ℝ)*base90 + (11555677/1250000000000000000000 : ℝ)*base92 + (11555677/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (189960555962436989409801/18295000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1896289119/100000000000000 : ℝ)*(base19) + (215577657/10000000000000 : ℝ)*(base23) + (202269899/100000000000000 : ℝ)*(upper2) + (101739647/100000000000000 : ℝ)*(upper3) + (451866337/100000000000000 : ℝ)*(upper5) + (1016629174323099/50000000000000 : ℝ)*(major0) + (1016629174323099/50000000000000 : ℝ)*(major1) + (1016629174323099/50000000000000 : ℝ)*(major2) + (17041377301/100000000000000 : ℝ)*(sp1) + (2208314117/20000000000000 : ℝ)*(sp2) + (3057918775518499/100000000000000 : ℝ)*(sp4) + (3057899837852079/100000000000000 : ℝ)*(sp5) + (191119098635709/6250000000000 : ℝ)*(sp6) + (1008597575667387/100000000000000 : ℝ)*(sp7) + (1008597575667387/100000000000000 : ℝ)*(f.failure) + (3057918775518499/100000000000000 : ℝ)*(f.sum) + (45411991389087/18295000000000000000000000000 : ℝ)*base65 + (5288006625473857771/1829500000000000000000000000000000 : ℝ)*base67 + (10096264730755642229/1829500000000000000000000000000000 : ℝ)*base70 + (5619965849414357771/1829500000000000000000000000000000 : ℝ)*base71 + (10154027508723/18295000000000000000000000000 : ℝ)*base74 + (18306737346506142229/1829500000000000000000000000000000 : ℝ)*base76 + (2926949066791857771/1829500000000000000000000000000000 : ℝ)*base77 + (7560779872210642229/1829500000000000000000000000000000 : ℝ)*base80 + (43519778270949/9147500000000000000000000000 : ℝ)*base82 + (23555649/10000000000000000000000 : ℝ)*base89 + (23555649/10000000000000000000000 : ℝ)*base91 + (23555649/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1730_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (201592627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4247/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9977/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8577/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1730_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1730_s2_0 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1342904017/10000000000 : ℝ)*x 0 + (5457831667/10000000000 : ℝ)*x 1 + (5140142309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342904017/10000000000 : ℝ)^5463 ≤ (422542246137/5000000000000 : ℝ)^4439 := by
    have hnat : (1342904017 : ℕ)^5463*5000000000000^4439 ≤ 422542246137^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342904017 10000000000 422542246137 5000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457831667/10000000000 : ℝ)^5463 ≤ (47463008373961/100000000000000 : ℝ)^4439 := by
    have hnat : (5457831667 : ℕ)^5463*100000000000000^4439 ≤ 47463008373961^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457831667 10000000000 47463008373961 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140142309/10000000000 : ℝ)^5463 ≤ (8817229340023/20000000000000 : ℝ)^4439 := by
    have hnat : (5140142309 : ℕ)^5463*20000000000000^4439 ≤ 8817229340023^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140142309 10000000000 8817229340023 20000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1342904017/10000000000 : ℝ), (5457831667/10000000000 : ℝ), (5140142309/10000000000 : ℝ)] ![(422542246137/5000000000000 : ℝ), (47463008373961/100000000000000 : ℝ), (8817229340023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1342904017/10000000000 : ℝ)|^5463 ≤ (422542246137/5000000000000 : ℝ)^4439
        have hw : |(-1342904017/10000000000 : ℝ)|=(1342904017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457831667/10000000000 : ℝ)|^5463 ≤ (47463008373961/100000000000000 : ℝ)^4439
        have hw : |(5457831667/10000000000 : ℝ)|=(5457831667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140142309/10000000000 : ℝ)|^5463 ≤ (8817229340023/20000000000000 : ℝ)^4439
        have hw : |(5140142309/10000000000 : ℝ)|=(5140142309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s2_1 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5336866981/10000000000 : ℝ)*x 0 + (-15073827/100000000 : ℝ)*x 1 + (5140142023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5336866981/10000000000 : ℝ)^5463 ≤ (46171724414497/100000000000000 : ℝ)^4439 := by
    have hnat : (5336866981 : ℕ)^5463*100000000000000^4439 ≤ 46171724414497^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5336866981 10000000000 46171724414497 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15073827/100000000 : ℝ)^5463 ≤ (9742131883389/100000000000000 : ℝ)^4439 := by
    have hnat : (15073827 : ℕ)^5463*100000000000000^4439 ≤ 9742131883389^4439*100000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15073827 100000000 9742131883389 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140142023/10000000000 : ℝ)^5463 ≤ (22043071840641/50000000000000 : ℝ)^4439 := by
    have hnat : (5140142023 : ℕ)^5463*50000000000000^4439 ≤ 22043071840641^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140142023 10000000000 22043071840641 50000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5336866981/10000000000 : ℝ), (-15073827/100000000 : ℝ), (5140142023/10000000000 : ℝ)] ![(46171724414497/100000000000000 : ℝ), (9742131883389/100000000000000 : ℝ), (22043071840641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5336866981/10000000000 : ℝ)|^5463 ≤ (46171724414497/100000000000000 : ℝ)^4439
        have hw : |(5336866981/10000000000 : ℝ)|=(5336866981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15073827/100000000 : ℝ)|^5463 ≤ (9742131883389/100000000000000 : ℝ)^4439
        have hw : |(-15073827/100000000 : ℝ)|=(15073827/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140142023/10000000000 : ℝ)|^5463 ≤ (22043071840641/50000000000000 : ℝ)^4439
        have hw : |(5140142023/10000000000 : ℝ)|=(5140142023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s2_2 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41694271/78125000 : ℝ)*x 0 + (2570071153/5000000000 : ℝ)*x 1 + (-1507382717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41694271/78125000 : ℝ)^5463 ≤ (9234344258973/20000000000000 : ℝ)^4439 := by
    have hnat : (41694271 : ℕ)^5463*20000000000000^4439 ≤ 9234344258973^4439*78125000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41694271 78125000 9234344258973 20000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570071153/5000000000 : ℝ)^5463 ≤ (44086146668449/100000000000000 : ℝ)^4439 := by
    have hnat : (2570071153 : ℕ)^5463*100000000000000^4439 ≤ 44086146668449^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570071153 5000000000 44086146668449 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1507382717/10000000000 : ℝ)^5463 ≤ (2435533004651/25000000000000 : ℝ)^4439 := by
    have hnat : (1507382717 : ℕ)^5463*25000000000000^4439 ≤ 2435533004651^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507382717 10000000000 2435533004651 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41694271/78125000 : ℝ), (2570071153/5000000000 : ℝ), (-1507382717/10000000000 : ℝ)] ![(9234344258973/20000000000000 : ℝ), (44086146668449/100000000000000 : ℝ), (2435533004651/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41694271/78125000 : ℝ)|^5463 ≤ (9234344258973/20000000000000 : ℝ)^4439
        have hw : |(41694271/78125000 : ℝ)|=(41694271/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570071153/5000000000 : ℝ)|^5463 ≤ (44086146668449/100000000000000 : ℝ)^4439
        have hw : |(2570071153/5000000000 : ℝ)|=(2570071153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1507382717/10000000000 : ℝ)|^5463 ≤ (2435533004651/25000000000000 : ℝ)^4439
        have hw : |(-1507382717/10000000000 : ℝ)|=(1507382717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s2_3 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1019948689/2500000000 : ℝ)*x 0 + (3615281689/10000000000 : ℝ)*x 1 + (4578470067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019948689/2500000000 : ℝ)^5463 ≤ (33175643463061/100000000000000 : ℝ)^4439 := by
    have hnat : (1019948689 : ℕ)^5463*100000000000000^4439 ≤ 33175643463061^4439*2500000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019948689 2500000000 33175643463061 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3615281689/10000000000 : ℝ)^5463 ≤ (1786871184499/6250000000000 : ℝ)^4439 := by
    have hnat : (3615281689 : ℕ)^5463*6250000000000^4439 ≤ 1786871184499^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3615281689 10000000000 1786871184499 6250000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4578470067/10000000000 : ℝ)^5463 ≤ (2389651097831/6250000000000 : ℝ)^4439 := by
    have hnat : (4578470067 : ℕ)^5463*6250000000000^4439 ≤ 2389651097831^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578470067 10000000000 2389651097831 6250000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1019948689/2500000000 : ℝ), (3615281689/10000000000 : ℝ), (4578470067/10000000000 : ℝ)] ![(33175643463061/100000000000000 : ℝ), (1786871184499/6250000000000 : ℝ), (2389651097831/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1019948689/2500000000 : ℝ)|^5463 ≤ (33175643463061/100000000000000 : ℝ)^4439
        have hw : |(1019948689/2500000000 : ℝ)|=(1019948689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3615281689/10000000000 : ℝ)|^5463 ≤ (1786871184499/6250000000000 : ℝ)^4439
        have hw : |(3615281689/10000000000 : ℝ)|=(3615281689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4578470067/10000000000 : ℝ)|^5463 ≤ (2389651097831/6250000000000 : ℝ)^4439
        have hw : |(4578470067/10000000000 : ℝ)|=(4578470067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s2_4 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-41970159/312500000 : ℝ)*x 0 + (1028745481/2000000000 : ℝ)*x 1 + (681774147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41970159/312500000 : ℝ)^5463 ≤ (2112984370009/25000000000000 : ℝ)^4439 := by
    have hnat : (41970159 : ℕ)^5463*25000000000000^4439 ≤ 2112984370009^4439*312500000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41970159 312500000 2112984370009 25000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028745481/2000000000 : ℝ)^5463 ≤ (44123991723121/100000000000000 : ℝ)^4439 := by
    have hnat : (1028745481 : ℕ)^5463*100000000000000^4439 ≤ 44123991723121^4439*2000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028745481 2000000000 44123991723121 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681774147/1250000000 : ℝ)^5463 ≤ (23712035391237/50000000000000 : ℝ)^4439 := by
    have hnat : (681774147 : ℕ)^5463*50000000000000^4439 ≤ 23712035391237^4439*1250000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681774147 1250000000 23712035391237 50000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41970159/312500000 : ℝ), (1028745481/2000000000 : ℝ), (681774147/1250000000 : ℝ)] ![(2112984370009/25000000000000 : ℝ), (44123991723121/100000000000000 : ℝ), (23712035391237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41970159/312500000 : ℝ)|^5463 ≤ (2112984370009/25000000000000 : ℝ)^4439
        have hw : |(-41970159/312500000 : ℝ)|=(41970159/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028745481/2000000000 : ℝ)|^5463 ≤ (44123991723121/100000000000000 : ℝ)^4439
        have hw : |(1028745481/2000000000 : ℝ)|=(1028745481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681774147/1250000000 : ℝ)|^5463 ≤ (23712035391237/50000000000000 : ℝ)^4439
        have hw : |(681774147/1250000000 : ℝ)|=(681774147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s2_5 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251844207/10000000000 : ℝ)*x 0 + (-59666583/500000000 : ℝ)*x 1 + (5454193181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251844207/10000000000 : ℝ)^5463 ≤ (1131703486497/2500000000000 : ℝ)^4439 := by
    have hnat : (5251844207 : ℕ)^5463*2500000000000^4439 ≤ 1131703486497^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251844207 10000000000 1131703486497 2500000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59666583/500000000 : ℝ)^5463 ≤ (7307789690097/100000000000000 : ℝ)^4439 := by
    have hnat : (59666583 : ℕ)^5463*100000000000000^4439 ≤ 7307789690097^4439*500000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59666583 500000000 7307789690097 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454193181/10000000000 : ℝ)^5463 ≤ (23712035417989/50000000000000 : ℝ)^4439 := by
    have hnat : (5454193181 : ℕ)^5463*50000000000000^4439 ≤ 23712035417989^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454193181 10000000000 23712035417989 50000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251844207/10000000000 : ℝ), (-59666583/500000000 : ℝ), (5454193181/10000000000 : ℝ)] ![(1131703486497/2500000000000 : ℝ), (7307789690097/100000000000000 : ℝ), (23712035417989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251844207/10000000000 : ℝ)|^5463 ≤ (1131703486497/2500000000000 : ℝ)^4439
        have hw : |(5251844207/10000000000 : ℝ)|=(5251844207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-59666583/500000000 : ℝ)|^5463 ≤ (7307789690097/100000000000000 : ℝ)^4439
        have hw : |(-59666583/500000000 : ℝ)|=(59666583/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454193181/10000000000 : ℝ)|^5463 ≤ (23712035417989/50000000000000 : ℝ)^4439
        have hw : |(5454193181/10000000000 : ℝ)|=(5454193181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s2_6 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050368841/2000000000 : ℝ)*x 0 + (5454193183/10000000000 : ℝ)*x 1 + (-59666583/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050368841/2000000000 : ℝ)^5463 ≤ (5658517429833/12500000000000 : ℝ)^4439 := by
    have hnat : (1050368841 : ℕ)^5463*12500000000000^4439 ≤ 5658517429833^4439*2000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050368841 2000000000 5658517429833 12500000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454193183/10000000000 : ℝ)^5463 ≤ (47424070857379/100000000000000 : ℝ)^4439 := by
    have hnat : (5454193183 : ℕ)^5463*100000000000000^4439 ≤ 47424070857379^4439*10000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454193183 10000000000 47424070857379 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59666583/500000000 : ℝ)^5463 ≤ (7307789690097/100000000000000 : ℝ)^4439 := by
    have hnat : (59666583 : ℕ)^5463*100000000000000^4439 ≤ 7307789690097^4439*500000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59666583 500000000 7307789690097 100000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050368841/2000000000 : ℝ), (5454193183/10000000000 : ℝ), (-59666583/500000000 : ℝ)] ![(5658517429833/12500000000000 : ℝ), (47424070857379/100000000000000 : ℝ), (7307789690097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050368841/2000000000 : ℝ)|^5463 ≤ (5658517429833/12500000000000 : ℝ)^4439
        have hw : |(1050368841/2000000000 : ℝ)|=(1050368841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454193183/10000000000 : ℝ)|^5463 ≤ (47424070857379/100000000000000 : ℝ)^4439
        have hw : |(5454193183/10000000000 : ℝ)|=(5454193183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59666583/500000000 : ℝ)|^5463 ≤ (7307789690097/100000000000000 : ℝ)^4439
        have hw : |(-59666583/500000000 : ℝ)|=(59666583/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1730_s2_7 (p : ℝ) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2040111283/5000000000 : ℝ)*x 0 + (285474999/625000000 : ℝ)*x 1 + (56661149/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040111283/5000000000 : ℝ)^5463 ≤ (4147490604771/12500000000000 : ℝ)^4439 := by
    have hnat : (2040111283 : ℕ)^5463*12500000000000^4439 ≤ 4147490604771^4439*5000000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040111283 5000000000 4147490604771 12500000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285474999/625000000 : ℝ)^5463 ≤ (7624546556741/20000000000000 : ℝ)^4439 := by
    have hnat : (285474999 : ℕ)^5463*20000000000000^4439 ≤ 7624546556741^4439*625000000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285474999 625000000 7624546556741 20000000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56661149/156250000 : ℝ)^5463 ≤ (896791948881/3125000000000 : ℝ)^4439 := by
    have hnat : (56661149 : ℕ)^5463*3125000000000^4439 ≤ 896791948881^4439*156250000^5463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56661149 156250000 896791948881 3125000000000 5463 4439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5463/1024 : ℝ)) 5463 4439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2040111283/5000000000 : ℝ), (285474999/625000000 : ℝ), (56661149/156250000 : ℝ)] ![(4147490604771/12500000000000 : ℝ), (7624546556741/20000000000000 : ℝ), (896791948881/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2040111283/5000000000 : ℝ)|^5463 ≤ (4147490604771/12500000000000 : ℝ)^4439
        have hw : |(2040111283/5000000000 : ℝ)|=(2040111283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285474999/625000000 : ℝ)|^5463 ≤ (7624546556741/20000000000000 : ℝ)^4439
        have hw : |(285474999/625000000 : ℝ)|=(285474999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56661149/156250000 : ℝ)|^5463 ≤ (896791948881/3125000000000 : ℝ)^4439
        have hw : |(56661149/156250000 : ℝ)|=(56661149/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1730_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (201592627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8577/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9977/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10149/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8477/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8577/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9977/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8577/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9977/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8577/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9977/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8577/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9977/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8577/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9977/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8577/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9977/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9977/100000 : ℝ) ^ (5455/1024 : ℝ) ≤ (46507636143369/10000000000000000000 : ℝ) := by
    have hpowers : (9977/100000 : ℝ)^5455 ≤ (46507636143369/10000000000000000000 : ℝ)^1024 := by
      have hnat : (9977 : ℕ)^5455*10000000000000000000^1024 ≤ 46507636143369^1024*100000^5455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9977 100000 46507636143369 10000000000000000000 5455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9977/100000 : ℝ)) (X := (46507636143369/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8577/50000 : ℝ) ^ (5455/1024 : ℝ) ≤ (1042943737117777/12500000000000000000 : ℝ) := by
    have hpowers : (8577/50000 : ℝ)^5455 ≤ (1042943737117777/12500000000000000000 : ℝ)^1024 := by
      have hnat : (8577 : ℕ)^5455*12500000000000000000^1024 ≤ 1042943737117777^1024*50000^5455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8577 50000 1042943737117777 12500000000000000000 5455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8577/50000 : ℝ)) (X := (1042943737117777/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000046507636143369/5000000000000000000 : ℝ) ≤ (5000008730273053/5000000000000000 : ℝ) ^ (5455/1024 : ℝ) := by
    have hpowers : (5000046507636143369/5000000000000000000 : ℝ)^1024 ≤ (5000008730273053/5000000000000000 : ℝ)^5455 := by
      have hnat : (5000046507636143369 : ℕ)^1024*5000000000000000^5455 ≤ 5000008730273053^5455*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000046507636143369 5000000000000000000 5000008730273053 5000000000000000 1024 5455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000008730273053/5000000000000000 : ℝ)) (X := (5000046507636143369/5000000000000000000 : ℝ)) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004404313129187953/50000000000000000000 : ℝ) ≤ (5000082673791109/5000000000000000 : ℝ) ^ (5455/1024 : ℝ) := by
    have hpowers : (50004404313129187953/50000000000000000000 : ℝ)^1024 ≤ (5000082673791109/5000000000000000 : ℝ)^5455 := by
      have hnat : (50004404313129187953 : ℕ)^1024*5000000000000000^5455 ≤ 5000082673791109^5455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004404313129187953 50000000000000000000 5000082673791109 5000000000000000 1024 5455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000082673791109/5000000000000000 : ℝ)) (X := (50004404313129187953/50000000000000000000 : ℝ)) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251042943737117777/6250000000000000000 : ℝ) ≤ (1000031323461833/1000000000000000 : ℝ) ^ (5455/1024 : ℝ) := by
    have hpowers : (6251042943737117777/6250000000000000000 : ℝ)^1024 ≤ (1000031323461833/1000000000000000 : ℝ)^5455 := by
      have hnat : (6251042943737117777 : ℕ)^1024*1000000000000000^5455 ≤ 1000031323461833^5455*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251042943737117777 6250000000000000000 1000031323461833 1000000000000000 1024 5455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000031323461833/1000000000000000 : ℝ)) (X := (6251042943737117777/6250000000000000000 : ℝ)) (by norm_num) 5455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(46507636143369/10000000000000000000 : ℝ) ≤ ((35883587188210411957/35885000000000000000 : ℝ)+2*(9242939757/44856250000000 : ℝ)*(9977/100000 : ℝ))^(5455/1024 : ℝ) := by
    rw [show (35883587188210411957/35885000000000000000 : ℝ)+2*(9242939757/44856250000000 : ℝ)*(9977/100000 : ℝ)=(5000008730273053/5000000000000000 : ℝ) by norm_num, show 1+2*(46507636143369/10000000000000000000 : ℝ)=(5000046507636143369/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1042943737117777/12500000000000000000 : ℝ)+(46507636143369/10000000000000000000 : ℝ) ≤ ((35883587188210411957/35885000000000000000 : ℝ)+(9242939757/44856250000000 : ℝ)*((8577/50000 : ℝ)+(9977/100000 : ℝ)))^(5455/1024 : ℝ) := by
    rw [show (35883587188210411957/35885000000000000000 : ℝ)+(9242939757/44856250000000 : ℝ)*((8577/50000 : ℝ)+(9977/100000 : ℝ))=(5000082673791109/5000000000000000 : ℝ) by norm_num, show 1+(1042943737117777/12500000000000000000 : ℝ)+(46507636143369/10000000000000000000 : ℝ)=(50004404313129187953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1042943737117777/12500000000000000000 : ℝ) ≤ ((35883587188210411957/35885000000000000000 : ℝ)+2*(9242939757/44856250000000 : ℝ)*(8577/50000 : ℝ))^(5455/1024 : ℝ) := by
    rw [show (35883587188210411957/35885000000000000000 : ℝ)+2*(9242939757/44856250000000 : ℝ)*(8577/50000 : ℝ)=(1000031323461833/1000000000000000 : ℝ) by norm_num, show 1+2*(1042943737117777/12500000000000000000 : ℝ)=(6251042943737117777/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35883587188210411957/35885000000000000000 : ℝ)*(X 1 0+X 2 0)+(9242939757/44856250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5455/1024 : ℝ)) (lo := (9977/100000 : ℝ)) (hi := (8577/50000 : ℝ)) (c := (35883587188210411957/35885000000000000000 : ℝ)) (alpha := (9242939757/44856250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35883587188210411957/35885000000000000000 : ℝ)*(X 0 1+X 2 1)+(9242939757/44856250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5455/1024 : ℝ)) (lo := (9977/100000 : ℝ)) (hi := (8577/50000 : ℝ)) (c := (35883587188210411957/35885000000000000000 : ℝ)) (alpha := (9242939757/44856250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35883587188210411957/35885000000000000000 : ℝ)*(X 0 2+X 1 2)+(9242939757/44856250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5455/1024 : ℝ)) (lo := (9977/100000 : ℝ)) (hi := (8577/50000 : ℝ)) (c := (35883587188210411957/35885000000000000000 : ℝ)) (alpha := (9242939757/44856250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1342904017/10000000000 : ℝ)*X 0 0+(5457831667/10000000000 : ℝ)*X 0 1+(5140142309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5336866981/10000000000 : ℝ)*X 1 0+(-15073827/100000000 : ℝ)*X 1 1+(5140142023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((41694271/78125000 : ℝ)*X 2 0+(2570071153/5000000000 : ℝ)*X 2 1+(-1507382717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1019948689/2500000000 : ℝ)*X 0 0+(3615281689/10000000000 : ℝ)*X 0 1+(4578470067/10000000000 : ℝ)*X 0 2+(1019948689/2500000000 : ℝ)*X 1 0+(3615281689/10000000000 : ℝ)*X 1 1+(4578470067/10000000000 : ℝ)*X 1 2+(1019948689/2500000000 : ℝ)*X 2 0+(3615281689/10000000000 : ℝ)*X 2 1+(4578470067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-41970159/312500000 : ℝ)*X 0 0+(1028745481/2000000000 : ℝ)*X 0 1+(681774147/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251844207/10000000000 : ℝ)*X 1 0+(-59666583/500000000 : ℝ)*X 1 1+(5454193181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1050368841/2000000000 : ℝ)*X 2 0+(5454193183/10000000000 : ℝ)*X 2 1+(-59666583/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2040111283/5000000000 : ℝ)*X 0 0+(285474999/625000000 : ℝ)*X 0 1+(56661149/156250000 : ℝ)*X 0 2+(2040111283/5000000000 : ℝ)*X 1 0+(285474999/625000000 : ℝ)*X 1 1+(56661149/156250000 : ℝ)*X 1 2+(2040111283/5000000000 : ℝ)*X 2 0+(285474999/625000000 : ℝ)*X 2 1+(56661149/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1730_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25066578074301897723666963123/1794250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5048851/250000000000 : ℝ)*(base19) + (1750691859/100000000000000 : ℝ)*(base23) + (10250281/20000000000000 : ℝ)*(lower2) + (42071869/12500000000000 : ℝ)*(upper3) + (237187579/100000000000000 : ℝ)*(upper5) + (2092999081549729/100000000000000 : ℝ)*(major0) + (2092999081549729/100000000000000 : ℝ)*(major1) + (2092999081549729/100000000000000 : ℝ)*(major2) + (786937017459457/25000000000000 : ℝ)*(sp0) + (786940929588917/25000000000000 : ℝ)*(sp1) + (196735249200263/6250000000000 : ℝ)*(sp2) + (103822487505669/10000000000000 : ℝ)*(sp3) + (17668058239/100000000000000 : ℝ)*(sp4) + (7084463203/100000000000000 : ℝ)*(sp7) + (1038231959519893/100000000000000 : ℝ)*(f.failure) + (786941434474017/25000000000000 : ℝ)*(f.sum) + (92249781350951/17942500000000000000000000000 : ℝ)*base66 + (48121261623133609653/3588500000000000000000000000000000 : ℝ)*base67 + (16044095332825109653/3588500000000000000000000000000000 : ℝ)*base69 + (2048231608883109653/3588500000000000000000000000000000 : ℝ)*base71 + (74976594978139/17942500000000000000000000000 : ℝ)*base73 + (20525434056177109653/3588500000000000000000000000000000 : ℝ)*base75 + (10067722428437109653/3588500000000000000000000000000000 : ℝ)*base77 + (12563588168569109653/3588500000000000000000000000000000 : ℝ)*base79 + (26611082977311/17942500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (11371089/10000000000000000000000 : ℝ)*base90 + (11371089/10000000000000000000000 : ℝ)*base92 + (11371089/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29455060279399172055327/8971250000000000000000000000 : ℝ) := by norm_num
    linear_combination (436259111/100000000000000 : ℝ)*(base19) + (466774947/100000000000000 : ℝ)*(base23) + (14054503/20000000000000 : ℝ)*(upper3) + (7047239/50000000000000 : ℝ)*(lower4) + (16879913/25000000000000 : ℝ)*(upper5) + (2141671338573203/100000000000000 : ℝ)*(major0) + (2141671338573203/100000000000000 : ℝ)*(major1) + (2141671338573203/100000000000000 : ℝ)*(major2) + (4128401699/100000000000000 : ℝ)*(sp1) + (276963307/6250000000000 : ℝ)*(sp2) + (161048337027487/5000000000000 : ℝ)*(sp4) + (3220962175888929/100000000000000 : ℝ)*(sp5) + (1610480921180941/50000000000000 : ℝ)*(sp6) + (265593956788559/25000000000000 : ℝ)*(sp7) + (265593956788559/25000000000000 : ℝ)*(f.failure) + (161048337027487/5000000000000 : ℝ)*(f.sum) + (6537885684603/4485625000000000000000000000 : ℝ)*base66 + (10481584264793788271/3588500000000000000000000000000000 : ℝ)*base67 + (29462568366568211729/3588500000000000000000000000000000 : ℝ)*base70 + (1368883941644788271/3588500000000000000000000000000000 : ℝ)*base71 + (745040008639/560703125000000000000000000 : ℝ)*base73 + (22128879917670788271/3588500000000000000000000000000000 : ℝ)*base75 + (19369001017949211729/3588500000000000000000000000000000 : ℝ)*base78 + (23055391207059211729/3588500000000000000000000000000000 : ℝ)*base80 + (21772413943873/4485625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (17354493/2500000000000000000000 : ℝ)*base89 + (17354493/2500000000000000000000 : ℝ)*base91 + (17354493/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1730_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (201592627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8577/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9977/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8477/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1730_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1730_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (201592627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8477/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1730_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1730_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1730_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5455/1024 : ℝ) ≤ p) (hpb : p ≤ (5463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (201592627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8477/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1730_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
