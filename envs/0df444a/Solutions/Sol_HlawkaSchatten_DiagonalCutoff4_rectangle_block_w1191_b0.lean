-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1191_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:53:15.238688+00:00
-- url     : https://prove2.me/submissions/a4fd62ed-fcbd-4e32-8dd2-8245830311f0

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
theorem support_rectangle_w1191_s0_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-58637463/312500000 : ℝ)*x 0 + (3021537009/5000000000 : ℝ)*x 1 + (4786638123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58637463/312500000 : ℝ)^131 ≤ (10925475571389/100000000000000 : ℝ)^99 := by
    have hnat : (58637463 : ℕ)^131*100000000000000^99 ≤ 10925475571389^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58637463 312500000 10925475571389 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3021537009/5000000000 : ℝ)^131 ≤ (51351531558227/100000000000000 : ℝ)^99 := by
    have hnat : (3021537009 : ℕ)^131*100000000000000^99 ≤ 51351531558227^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021537009 5000000000 51351531558227 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4786638123/10000000000 : ℝ)^131 ≤ (37722992859363/100000000000000 : ℝ)^99 := by
    have hnat : (4786638123 : ℕ)^131*100000000000000^99 ≤ 37722992859363^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4786638123 10000000000 37722992859363 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58637463/312500000 : ℝ), (3021537009/5000000000 : ℝ), (4786638123/10000000000 : ℝ)] ![(10925475571389/100000000000000 : ℝ), (51351531558227/100000000000000 : ℝ), (37722992859363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58637463/312500000 : ℝ)|^131 ≤ (10925475571389/100000000000000 : ℝ)^99
        have hw : |(-58637463/312500000 : ℝ)|=(58637463/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3021537009/5000000000 : ℝ)|^131 ≤ (51351531558227/100000000000000 : ℝ)^99
        have hw : |(3021537009/5000000000 : ℝ)|=(3021537009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4786638123/10000000000 : ℝ)|^131 ≤ (37722992859363/100000000000000 : ℝ)^99
        have hw : |(4786638123/10000000000 : ℝ)|=(4786638123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s0_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2757016369/5000000000 : ℝ)*x 0 + (-162254781/625000000 : ℝ)*x 1 + (598329763/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757016369/5000000000 : ℝ)^131 ≤ (45488736554543/100000000000000 : ℝ)^99 := by
    have hnat : (2757016369 : ℕ)^131*100000000000000^99 ≤ 45488736554543^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757016369 5000000000 45488736554543 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162254781/625000000 : ℝ)^131 ≤ (16788270777463/100000000000000 : ℝ)^99 := by
    have hnat : (162254781 : ℕ)^131*100000000000000^99 ≤ 16788270777463^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162254781 625000000 16788270777463 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598329763/1250000000 : ℝ)^131 ≤ (18861496330613/50000000000000 : ℝ)^99 := by
    have hnat : (598329763 : ℕ)^131*50000000000000^99 ≤ 18861496330613^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598329763 1250000000 18861496330613 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757016369/5000000000 : ℝ), (-162254781/625000000 : ℝ), (598329763/1250000000 : ℝ)] ![(45488736554543/100000000000000 : ℝ), (16788270777463/100000000000000 : ℝ), (18861496330613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757016369/5000000000 : ℝ)|^131 ≤ (45488736554543/100000000000000 : ℝ)^99
        have hw : |(2757016369/5000000000 : ℝ)|=(2757016369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-162254781/625000000 : ℝ)|^131 ≤ (16788270777463/100000000000000 : ℝ)^99
        have hw : |(-162254781/625000000 : ℝ)|=(162254781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598329763/1250000000 : ℝ)|^131 ≤ (18861496330613/50000000000000 : ℝ)^99
        have hw : |(598329763/1250000000 : ℝ)|=(598329763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s0_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (689254131/1250000000 : ℝ)*x 0 + (4786637787/10000000000 : ℝ)*x 1 + (-1298038243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689254131/1250000000 : ℝ)^131 ≤ (22744369969279/50000000000000 : ℝ)^99 := by
    have hnat : (689254131 : ℕ)^131*50000000000000^99 ≤ 22744369969279^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689254131 1250000000 22744369969279 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4786637787/10000000000 : ℝ)^131 ≤ (37722989355469/100000000000000 : ℝ)^99 := by
    have hnat : (4786637787 : ℕ)^131*100000000000000^99 ≤ 37722989355469^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4786637787 10000000000 37722989355469 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298038243/5000000000 : ℝ)^131 ≤ (4197067672973/25000000000000 : ℝ)^99 := by
    have hnat : (1298038243 : ℕ)^131*25000000000000^99 ≤ 4197067672973^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298038243 5000000000 4197067672973 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689254131/1250000000 : ℝ), (4786637787/10000000000 : ℝ), (-1298038243/5000000000 : ℝ)] ![(22744369969279/50000000000000 : ℝ), (37722989355469/100000000000000 : ℝ), (4197067672973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689254131/1250000000 : ℝ)|^131 ≤ (22744369969279/50000000000000 : ℝ)^99
        have hw : |(689254131/1250000000 : ℝ)|=(689254131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4786637787/10000000000 : ℝ)|^131 ≤ (37722989355469/100000000000000 : ℝ)^99
        have hw : |(4786637787/10000000000 : ℝ)|=(4786637787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1298038243/5000000000 : ℝ)|^131 ≤ (4197067672973/25000000000000 : ℝ)^99
        have hw : |(-1298038243/5000000000 : ℝ)|=(1298038243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s0_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (839411341/2000000000 : ℝ)*x 0 + (3118916657/10000000000 : ℝ)*x 1 + (705326289/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839411341/2000000000 : ℝ)^131 ≤ (31700668486859/100000000000000 : ℝ)^99 := by
    have hnat : (839411341 : ℕ)^131*100000000000000^99 ≤ 31700668486859^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839411341 2000000000 31700668486859 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118916657/10000000000 : ℝ)^131 ≤ (21401757200763/100000000000000 : ℝ)^99 := by
    have hnat : (3118916657 : ℕ)^131*100000000000000^99 ≤ 21401757200763^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118916657 10000000000 21401757200763 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (705326289/1250000000 : ℝ)^131 ≤ (23448787146171/50000000000000 : ℝ)^99 := by
    have hnat : (705326289 : ℕ)^131*50000000000000^99 ≤ 23448787146171^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705326289 1250000000 23448787146171 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839411341/2000000000 : ℝ), (3118916657/10000000000 : ℝ), (705326289/1250000000 : ℝ)] ![(31700668486859/100000000000000 : ℝ), (21401757200763/100000000000000 : ℝ), (23448787146171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839411341/2000000000 : ℝ)|^131 ≤ (31700668486859/100000000000000 : ℝ)^99
        have hw : |(839411341/2000000000 : ℝ)|=(839411341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118916657/10000000000 : ℝ)|^131 ≤ (21401757200763/100000000000000 : ℝ)^99
        have hw : |(3118916657/10000000000 : ℝ)|=(3118916657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(705326289/1250000000 : ℝ)|^131 ≤ (23448787146171/50000000000000 : ℝ)^99
        have hw : |(705326289/1250000000 : ℝ)|=(705326289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s0_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-470350437/2500000000 : ℝ)*x 0 + (963804827/2000000000 : ℝ)*x 1 + (3004772967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470350437/2500000000 : ℝ)^131 ≤ (1370504733483/12500000000000 : ℝ)^99 := by
    have hnat : (470350437 : ℕ)^131*12500000000000^99 ≤ 1370504733483^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470350437 2500000000 1370504733483 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963804827/2000000000 : ℝ)^131 ≤ (38061091193771/100000000000000 : ℝ)^99 := by
    have hnat : (963804827 : ℕ)^131*100000000000000^99 ≤ 38061091193771^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963804827 2000000000 38061091193771 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3004772967/5000000000 : ℝ)^131 ≤ (50974870919063/100000000000000 : ℝ)^99 := by
    have hnat : (3004772967 : ℕ)^131*100000000000000^99 ≤ 50974870919063^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3004772967 5000000000 50974870919063 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-470350437/2500000000 : ℝ), (963804827/2000000000 : ℝ), (3004772967/5000000000 : ℝ)] ![(1370504733483/12500000000000 : ℝ), (38061091193771/100000000000000 : ℝ), (50974870919063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-470350437/2500000000 : ℝ)|^131 ≤ (1370504733483/12500000000000 : ℝ)^99
        have hw : |(-470350437/2500000000 : ℝ)|=(470350437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(963804827/2000000000 : ℝ)|^131 ≤ (38061091193771/100000000000000 : ℝ)^99
        have hw : |(963804827/2000000000 : ℝ)|=(963804827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3004772967/5000000000 : ℝ)|^131 ≤ (50974870919063/100000000000000 : ℝ)^99
        have hw : |(3004772967/5000000000 : ℝ)|=(3004772967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s0_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5172400419/10000000000 : ℝ)*x 0 + (-274633743/2000000000 : ℝ)*x 1 + (6009545553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172400419/10000000000 : ℝ)^131 ≤ (20898647812381/50000000000000 : ℝ)^99 := by
    have hnat : (5172400419 : ℕ)^131*50000000000000^99 ≤ 20898647812381^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172400419 10000000000 20898647812381 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274633743/2000000000 : ℝ)^131 ≤ (3613918861239/50000000000000 : ℝ)^99 := by
    have hnat : (274633743 : ℕ)^131*50000000000000^99 ≤ 3613918861239^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274633743 2000000000 3613918861239 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6009545553/10000000000 : ℝ)^131 ≤ (50974866642691/100000000000000 : ℝ)^99 := by
    have hnat : (6009545553 : ℕ)^131*100000000000000^99 ≤ 50974866642691^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6009545553 10000000000 50974866642691 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172400419/10000000000 : ℝ), (-274633743/2000000000 : ℝ), (6009545553/10000000000 : ℝ)] ![(20898647812381/50000000000000 : ℝ), (3613918861239/50000000000000 : ℝ), (50974866642691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172400419/10000000000 : ℝ)|^131 ≤ (20898647812381/50000000000000 : ℝ)^99
        have hw : |(5172400419/10000000000 : ℝ)|=(5172400419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274633743/2000000000 : ℝ)|^131 ≤ (3613918861239/50000000000000 : ℝ)^99
        have hw : |(-274633743/2000000000 : ℝ)|=(274633743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6009545553/10000000000 : ℝ)|^131 ≤ (50974866642691/100000000000000 : ℝ)^99
        have hw : |(6009545553/10000000000 : ℝ)|=(6009545553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s0_6 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (258620017/500000000 : ℝ)*x 0 + (6009545777/10000000000 : ℝ)*x 1 + (-54926739/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258620017/500000000 : ℝ)^131 ≤ (4179729478003/10000000000000 : ℝ)^99 := by
    have hnat : (258620017 : ℕ)^131*10000000000000^99 ≤ 4179729478003^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258620017 500000000 4179729478003 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6009545777/10000000000 : ℝ)^131 ≤ (50974869156883/100000000000000 : ℝ)^99 := by
    have hnat : (6009545777 : ℕ)^131*100000000000000^99 ≤ 50974869156883^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6009545777 10000000000 50974869156883 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54926739/400000000 : ℝ)^131 ≤ (22586987659/312500000000 : ℝ)^99 := by
    have hnat : (54926739 : ℕ)^131*312500000000^99 ≤ 22586987659^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54926739 400000000 22586987659 312500000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258620017/500000000 : ℝ), (6009545777/10000000000 : ℝ), (-54926739/400000000 : ℝ)] ![(4179729478003/10000000000000 : ℝ), (50974869156883/100000000000000 : ℝ), (22586987659/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258620017/500000000 : ℝ)|^131 ≤ (4179729478003/10000000000000 : ℝ)^99
        have hw : |(258620017/500000000 : ℝ)|=(258620017/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6009545777/10000000000 : ℝ)|^131 ≤ (50974869156883/100000000000000 : ℝ)^99
        have hw : |(6009545777/10000000000 : ℝ)|=(6009545777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54926739/400000000 : ℝ)|^131 ≤ (22586987659/312500000000 : ℝ)^99
        have hw : |(-54926739/400000000 : ℝ)|=(54926739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s0_7 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (65736027/156250000 : ℝ)*x 0 + (5577558797/10000000000 : ℝ)*x 1 + (3186262111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65736027/156250000 : ℝ)^131 ≤ (15900570984671/50000000000000 : ℝ)^99 := by
    have hnat : (65736027 : ℕ)^131*50000000000000^99 ≤ 15900570984671^99*156250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65736027 156250000 15900570984671 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5577558797/10000000000 : ℝ)^131 ≤ (11545871553579/25000000000000 : ℝ)^99 := by
    have hnat : (5577558797 : ℕ)^131*25000000000000^99 ≤ 11545871553579^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5577558797 10000000000 11545871553579 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3186262111/10000000000 : ℝ)^131 ≤ (2201537179657/10000000000000 : ℝ)^99 := by
    have hnat : (3186262111 : ℕ)^131*10000000000000^99 ≤ 2201537179657^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3186262111 10000000000 2201537179657 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65736027/156250000 : ℝ), (5577558797/10000000000 : ℝ), (3186262111/10000000000 : ℝ)] ![(15900570984671/50000000000000 : ℝ), (11545871553579/25000000000000 : ℝ), (2201537179657/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65736027/156250000 : ℝ)|^131 ≤ (15900570984671/50000000000000 : ℝ)^99
        have hw : |(65736027/156250000 : ℝ)|=(65736027/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5577558797/10000000000 : ℝ)|^131 ≤ (11545871553579/25000000000000 : ℝ)^99
        have hw : |(5577558797/10000000000 : ℝ)|=(5577558797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3186262111/10000000000 : ℝ)|^131 ≤ (2201537179657/10000000000000 : ℝ)^99
        have hw : |(3186262111/10000000000 : ℝ)|=(3186262111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (307/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6907/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8383/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8383 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8383*1^2048 ≤ 0^2048*1^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8383/2048 : ℝ) ≤ (146895135270332603/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8383 ≤ (146895135270332603/6250000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8383*6250000000000000000^2048 ≤ 146895135270332603^2048*5^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 146895135270332603 6250000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (146895135270332603/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8383 := by
      have hnat : (1 : ℕ)^2048*1^8383 ≤ 1^8383*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6396895135270332603/6250000000000000000 : ℝ) ≤ (10056916280307223/10000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (6396895135270332603/6250000000000000000 : ℝ)^2048 ≤ (10056916280307223/10000000000000000 : ℝ)^8383 := by
      have hnat : (6396895135270332603 : ℕ)^2048*10000000000000000^8383 ≤ 10056916280307223^8383*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6396895135270332603 6250000000000000000 10056916280307223 10000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056916280307223/10000000000000000 : ℝ)) (X := (6396895135270332603/6250000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3271895135270332603/3125000000000000000 : ℝ) ≤ (5056916280307223/5000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (3271895135270332603/3125000000000000000 : ℝ)^2048 ≤ (5056916280307223/5000000000000000 : ℝ)^8383 := by
      have hnat : (3271895135270332603 : ℕ)^2048*5000000000000000^8383 ≤ 5056916280307223^8383*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3271895135270332603 3125000000000000000 5056916280307223 5000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056916280307223/5000000000000000 : ℝ)) (X := (3271895135270332603/3125000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(56916280307223/4000000000000000 : ℝ)*(0 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56916280307223/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(146895135270332603/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(56916280307223/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (1 : ℝ)+(56916280307223/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10056916280307223/10000000000000000 : ℝ) by norm_num, show 1+(146895135270332603/6250000000000000000 : ℝ)+(0 : ℝ)=(6396895135270332603/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(146895135270332603/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(56916280307223/4000000000000000 : ℝ)*(2/5 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56916280307223/4000000000000000 : ℝ)*(2/5 : ℝ)=(5056916280307223/5000000000000000 : ℝ) by norm_num, show 1+2*(146895135270332603/6250000000000000000 : ℝ)=(3271895135270332603/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(56916280307223/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56916280307223/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(56916280307223/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56916280307223/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(56916280307223/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56916280307223/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-58637463/312500000 : ℝ)*X 0 0+(3021537009/5000000000 : ℝ)*X 0 1+(4786638123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757016369/5000000000 : ℝ)*X 1 0+(-162254781/625000000 : ℝ)*X 1 1+(598329763/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((689254131/1250000000 : ℝ)*X 2 0+(4786637787/10000000000 : ℝ)*X 2 1+(-1298038243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((839411341/2000000000 : ℝ)*X 0 0+(3118916657/10000000000 : ℝ)*X 0 1+(705326289/1250000000 : ℝ)*X 0 2+(839411341/2000000000 : ℝ)*X 1 0+(3118916657/10000000000 : ℝ)*X 1 1+(705326289/1250000000 : ℝ)*X 1 2+(839411341/2000000000 : ℝ)*X 2 0+(3118916657/10000000000 : ℝ)*X 2 1+(705326289/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-470350437/2500000000 : ℝ)*X 0 0+(963804827/2000000000 : ℝ)*X 0 1+(3004772967/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5172400419/10000000000 : ℝ)*X 1 0+(-274633743/2000000000 : ℝ)*X 1 1+(6009545553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((258620017/500000000 : ℝ)*X 2 0+(6009545777/10000000000 : ℝ)*X 2 1+(-54926739/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((65736027/156250000 : ℝ)*X 0 0+(5577558797/10000000000 : ℝ)*X 0 1+(3186262111/10000000000 : ℝ)*X 0 2+(65736027/156250000 : ℝ)*X 1 0+(5577558797/10000000000 : ℝ)*X 1 1+(3186262111/10000000000 : ℝ)*X 1 2+(65736027/156250000 : ℝ)*X 2 0+(5577558797/10000000000 : ℝ)*X 2 1+(3186262111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142937048640391611710187/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9748223/100000000000000 : ℝ)*(base1) + (20389379/6250000000000 : ℝ)*(base19) + (339712681/100000000000000 : ℝ)*(base23) + (31263227/100000000000000 : ℝ)*(base24) + (17338899/20000000000000 : ℝ)*(upper3) + (596074645037777/100000000000000 : ℝ)*(major0) + (596074645037777/100000000000000 : ℝ)*(major1) + (596074645037777/100000000000000 : ℝ)*(major2) + (159180630042283/20000000000000 : ℝ)*(sp0) + (795903445537497/100000000000000 : ℝ)*(sp1) + (198975850197913/25000000000000 : ℝ)*(sp2) + (396244884317473/100000000000000 : ℝ)*(sp3) + (631304369/100000000000000 : ℝ)*(sp4) + (576596611/100000000000000 : ℝ)*(sp7) + (396245470662307/100000000000000 : ℝ)*(f.failure) + (795903771767561/100000000000000 : ℝ)*(f.sum) + (232087476763271/200000000000000000000000000000 : ℝ)*base65 + (854916404236729/400000000000000000000000000000 : ℝ)*base68 + (1134563165763271/400000000000000000000000000000 : ℝ)*base69 + (1466433577363271/400000000000000000000000000000 : ℝ)*base71 + (52799157763271/200000000000000000000000000000 : ℝ)*base73 + (270167233036729/400000000000000000000000000000 : ℝ)*base76 + (1456058173363271/400000000000000000000000000000 : ℝ)*base77 + (1848326460163271/400000000000000000000000000000 : ℝ)*base79 + (162936504036729/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3458541/2500000000000000000000 : ℝ)*base89 + (3458541/2500000000000000000000 : ℝ)*base91 + (3458541/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (300580063223804142734661/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29977537/100000000000000 : ℝ)*(base1) + (400023533/50000000000000 : ℝ)*(base19) + (193429/24414062500 : ℝ)*(base23) + (75528729/100000000000000 : ℝ)*(upper3) + (102274509/100000000000000 : ℝ)*(upper5) + (629075589154431/100000000000000 : ℝ)*(major0) + (629075589154431/100000000000000 : ℝ)*(major1) + (629075589154431/100000000000000 : ℝ)*(major2) + (1583999597/100000000000000 : ℝ)*(sp1) + (1660717163/100000000000000 : ℝ)*(sp2) + (839967991294191/100000000000000 : ℝ)*(sp4) + (83996557726999/10000000000000 : ℝ)*(sp5) + (419982754157153/50000000000000 : ℝ)*(sp6) + (6534110731583/1562500000000 : ℝ)*(sp7) + (8363662335977/2000000000000 : ℝ)*(f.failure) + (839967961316653/100000000000000 : ℝ)*(f.sum) + (388157618155113/200000000000000000000000000000 : ℝ)*base65 + (483029107844887/400000000000000000000000000000 : ℝ)*base68 + (1662148138644887/400000000000000000000000000000 : ℝ)*base70 + (641120458955113/400000000000000000000000000000 : ℝ)*base71 + (109534131355113/200000000000000000000000000000 : ℝ)*base73 + (1904320195755113/400000000000000000000000000000 : ℝ)*base75 + (99066671755113/400000000000000000000000000000 : ℝ)*base77 + (1264201188955113/400000000000000000000000000000 : ℝ)*base79 + (492491941044887/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (291751/50000000000000000000 : ℝ)*base89 + (291751/50000000000000000000 : ℝ)*base91 + (291751/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1191_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (307/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6907/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1191_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1191_s1_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-519379487/2500000000 : ℝ)*x 0 + (5688599597/10000000000 : ℝ)*x 1 + (100247399/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519379487/2500000000 : ℝ)^131 ≤ (12501243071051/100000000000000 : ℝ)^99 := by
    have hnat : (519379487 : ℕ)^131*100000000000000^99 ≤ 12501243071051^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519379487 2500000000 12501243071051 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5688599597/10000000000 : ℝ)^131 ≤ (11851005241383/25000000000000 : ℝ)^99 := by
    have hnat : (5688599597 : ℕ)^131*25000000000000^99 ≤ 11851005241383^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688599597 10000000000 11851005241383 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100247399/200000000 : ℝ)^131 ≤ (40094735949287/100000000000000 : ℝ)^99 := by
    have hnat : (100247399 : ℕ)^131*100000000000000^99 ≤ 40094735949287^99*200000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100247399 200000000 40094735949287 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-519379487/2500000000 : ℝ), (5688599597/10000000000 : ℝ), (100247399/200000000 : ℝ)] ![(12501243071051/100000000000000 : ℝ), (11851005241383/25000000000000 : ℝ), (40094735949287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-519379487/2500000000 : ℝ)|^131 ≤ (12501243071051/100000000000000 : ℝ)^99
        have hw : |(-519379487/2500000000 : ℝ)|=(519379487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5688599597/10000000000 : ℝ)|^131 ≤ (11851005241383/25000000000000 : ℝ)^99
        have hw : |(5688599597/10000000000 : ℝ)|=(5688599597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100247399/200000000 : ℝ)|^131 ≤ (40094735949287/100000000000000 : ℝ)^99
        have hw : |(100247399/200000000 : ℝ)|=(100247399/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s1_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5416435561/10000000000 : ℝ)*x 0 + (-610386871/2500000000 : ℝ)*x 1 + (626546281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416435561/10000000000 : ℝ)^131 ≤ (11106602052813/25000000000000 : ℝ)^99 := by
    have hnat : (5416435561 : ℕ)^131*25000000000000^99 ≤ 11106602052813^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416435561 10000000000 11106602052813 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610386871/2500000000 : ℝ)^131 ≤ (241857073157/1562500000000 : ℝ)^99 := by
    have hnat : (610386871 : ℕ)^131*1562500000000^99 ≤ 241857073157^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610386871 2500000000 241857073157 1562500000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626546281/1250000000 : ℝ)^131 ≤ (40094739103541/100000000000000 : ℝ)^99 := by
    have hnat : (626546281 : ℕ)^131*100000000000000^99 ≤ 40094739103541^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626546281 1250000000 40094739103541 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416435561/10000000000 : ℝ), (-610386871/2500000000 : ℝ), (626546281/1250000000 : ℝ)] ![(11106602052813/25000000000000 : ℝ), (241857073157/1562500000000 : ℝ), (40094739103541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416435561/10000000000 : ℝ)|^131 ≤ (11106602052813/25000000000000 : ℝ)^99
        have hw : |(5416435561/10000000000 : ℝ)|=(5416435561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-610386871/2500000000 : ℝ)|^131 ≤ (241857073157/1562500000000 : ℝ)^99
        have hw : |(-610386871/2500000000 : ℝ)|=(610386871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(626546281/1250000000 : ℝ)|^131 ≤ (40094739103541/100000000000000 : ℝ)^99
        have hw : |(626546281/1250000000 : ℝ)|=(626546281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s1_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (270821731/500000000 : ℝ)*x 0 + (1002474173/2000000000 : ℝ)*x 1 + (-2441547921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270821731/500000000 : ℝ)^131 ≤ (11106599499563/25000000000000 : ℝ)^99 := by
    have hnat : (270821731 : ℕ)^131*25000000000000^99 ≤ 11106599499563^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270821731 500000000 11106599499563 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002474173/2000000000 : ℝ)^131 ≤ (5011843204291/12500000000000 : ℝ)^99 := by
    have hnat : (1002474173 : ℕ)^131*12500000000000^99 ≤ 5011843204291^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002474173 2000000000 5011843204291 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2441547921/10000000000 : ℝ)^131 ≤ (15478856348037/100000000000000 : ℝ)^99 := by
    have hnat : (2441547921 : ℕ)^131*100000000000000^99 ≤ 15478856348037^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441547921 10000000000 15478856348037 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270821731/500000000 : ℝ), (1002474173/2000000000 : ℝ), (-2441547921/10000000000 : ℝ)] ![(11106599499563/25000000000000 : ℝ), (5011843204291/12500000000000 : ℝ), (15478856348037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270821731/500000000 : ℝ)|^131 ≤ (11106599499563/25000000000000 : ℝ)^99
        have hw : |(270821731/500000000 : ℝ)|=(270821731/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1002474173/2000000000 : ℝ)|^131 ≤ (5011843204291/12500000000000 : ℝ)^99
        have hw : |(1002474173/2000000000 : ℝ)|=(1002474173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2441547921/10000000000 : ℝ)|^131 ≤ (15478856348037/100000000000000 : ℝ)^99
        have hw : |(-2441547921/10000000000 : ℝ)|=(2441547921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s1_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (431326167/1000000000 : ℝ)*x 0 + (1843087133/5000000000 : ℝ)*x 1 + (2522229091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431326167/1000000000 : ℝ)^131 ≤ (16433620082799/50000000000000 : ℝ)^99 := by
    have hnat : (431326167 : ℕ)^131*50000000000000^99 ≤ 16433620082799^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431326167 1000000000 16433620082799 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1843087133/5000000000 : ℝ)^131 ≤ (26698027256611/100000000000000 : ℝ)^99 := by
    have hnat : (1843087133 : ℕ)^131*100000000000000^99 ≤ 26698027256611^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843087133 5000000000 26698027256611 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2522229091/5000000000 : ℝ)^131 ≤ (2021736628003/5000000000000 : ℝ)^99 := by
    have hnat : (2522229091 : ℕ)^131*5000000000000^99 ≤ 2021736628003^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522229091 5000000000 2021736628003 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431326167/1000000000 : ℝ), (1843087133/5000000000 : ℝ), (2522229091/5000000000 : ℝ)] ![(16433620082799/50000000000000 : ℝ), (26698027256611/100000000000000 : ℝ), (2021736628003/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431326167/1000000000 : ℝ)|^131 ≤ (16433620082799/50000000000000 : ℝ)^99
        have hw : |(431326167/1000000000 : ℝ)|=(431326167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1843087133/5000000000 : ℝ)|^131 ≤ (26698027256611/100000000000000 : ℝ)^99
        have hw : |(1843087133/5000000000 : ℝ)|=(1843087133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2522229091/5000000000 : ℝ)|^131 ≤ (2021736628003/5000000000000 : ℝ)^99
        have hw : |(2522229091/5000000000 : ℝ)|=(2522229091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s1_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2078257867/10000000000 : ℝ)*x 0 + (2510715537/5000000000 : ℝ)*x 1 + (2839681181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078257867/10000000000 : ℝ)^131 ≤ (12507134948313/100000000000000 : ℝ)^99 := by
    have hnat : (2078257867 : ℕ)^131*100000000000000^99 ≤ 12507134948313^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078257867 10000000000 12507134948313 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2510715537/5000000000 : ℝ)^131 ≤ (40190673633029/100000000000000 : ℝ)^99 := by
    have hnat : (2510715537 : ℕ)^131*100000000000000^99 ≤ 40190673633029^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510715537 5000000000 40190673633029 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2839681181/5000000000 : ℝ)^131 ≤ (23651095701489/50000000000000 : ℝ)^99 := by
    have hnat : (2839681181 : ℕ)^131*50000000000000^99 ≤ 23651095701489^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2839681181 5000000000 23651095701489 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2078257867/10000000000 : ℝ), (2510715537/5000000000 : ℝ), (2839681181/5000000000 : ℝ)] ![(12507134948313/100000000000000 : ℝ), (40190673633029/100000000000000 : ℝ), (23651095701489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2078257867/10000000000 : ℝ)|^131 ≤ (12507134948313/100000000000000 : ℝ)^99
        have hw : |(-2078257867/10000000000 : ℝ)|=(2078257867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2510715537/5000000000 : ℝ)|^131 ≤ (40190673633029/100000000000000 : ℝ)^99
        have hw : |(2510715537/5000000000 : ℝ)|=(2510715537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2839681181/5000000000 : ℝ)|^131 ≤ (23651095701489/50000000000000 : ℝ)^99
        have hw : |(2839681181/5000000000 : ℝ)|=(2839681181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s1_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5242642591/10000000000 : ℝ)*x 0 + (-1774555071/10000000000 : ℝ)*x 1 + (709920357/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242642591/10000000000 : ℝ)^131 ≤ (1702001031297/4000000000000 : ℝ)^99 := by
    have hnat : (5242642591 : ℕ)^131*4000000000000^99 ≤ 1702001031297^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242642591 10000000000 1702001031297 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1774555071/10000000000 : ℝ)^131 ≤ (5073888679321/50000000000000 : ℝ)^99 := by
    have hnat : (1774555071 : ℕ)^131*50000000000000^99 ≤ 5073888679321^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774555071 10000000000 5073888679321 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709920357/1250000000 : ℝ)^131 ≤ (2956387302957/6250000000000 : ℝ)^99 := by
    have hnat : (709920357 : ℕ)^131*6250000000000^99 ≤ 2956387302957^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709920357 1250000000 2956387302957 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242642591/10000000000 : ℝ), (-1774555071/10000000000 : ℝ), (709920357/1250000000 : ℝ)] ![(1702001031297/4000000000000 : ℝ), (5073888679321/50000000000000 : ℝ), (2956387302957/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242642591/10000000000 : ℝ)|^131 ≤ (1702001031297/4000000000000 : ℝ)^99
        have hw : |(5242642591/10000000000 : ℝ)|=(5242642591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1774555071/10000000000 : ℝ)|^131 ≤ (5073888679321/50000000000000 : ℝ)^99
        have hw : |(-1774555071/10000000000 : ℝ)|=(1774555071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709920357/1250000000 : ℝ)|^131 ≤ (2956387302957/6250000000000 : ℝ)^99
        have hw : |(709920357/1250000000 : ℝ)|=(709920357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s1_6 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5242642473/10000000000 : ℝ)*x 0 + (5679363563/10000000000 : ℝ)*x 1 + (-55454819/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242642473/10000000000 : ℝ)^131 ≤ (1063750612879/2500000000000 : ℝ)^99 := by
    have hnat : (5242642473 : ℕ)^131*2500000000000^99 ≤ 1063750612879^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242642473 10000000000 1063750612879 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5679363563/10000000000 : ℝ)^131 ≤ (23651102319551/50000000000000 : ℝ)^99 := by
    have hnat : (5679363563 : ℕ)^131*50000000000000^99 ≤ 23651102319551^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5679363563 10000000000 23651102319551 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55454819/312500000 : ℝ)^131 ≤ (5073885414207/50000000000000 : ℝ)^99 := by
    have hnat : (55454819 : ℕ)^131*50000000000000^99 ≤ 5073885414207^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55454819 312500000 5073885414207 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242642473/10000000000 : ℝ), (5679363563/10000000000 : ℝ), (-55454819/312500000 : ℝ)] ![(1063750612879/2500000000000 : ℝ), (23651102319551/50000000000000 : ℝ), (5073885414207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242642473/10000000000 : ℝ)|^131 ≤ (1063750612879/2500000000000 : ℝ)^99
        have hw : |(5242642473/10000000000 : ℝ)|=(5242642473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5679363563/10000000000 : ℝ)|^131 ≤ (23651102319551/50000000000000 : ℝ)^99
        have hw : |(5679363563/10000000000 : ℝ)|=(5679363563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55454819/312500000 : ℝ)|^131 ≤ (5073885414207/50000000000000 : ℝ)^99
        have hw : |(-55454819/312500000 : ℝ)|=(55454819/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s1_7 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4314746789/10000000000 : ℝ)*x 0 + (251312907/500000000 : ℝ)*x 1 + (3704727171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314746789/10000000000 : ℝ)^131 ≤ (16441107791777/50000000000000 : ℝ)^99 := by
    have hnat : (4314746789 : ℕ)^131*50000000000000^99 ≤ 16441107791777^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314746789 10000000000 16441107791777 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251312907/500000000 : ℝ)^131 ≤ (20120902333197/50000000000000 : ℝ)^99 := by
    have hnat : (251312907 : ℕ)^131*50000000000000^99 ≤ 20120902333197^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251312907 500000000 20120902333197 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3704727171/10000000000 : ℝ)^131 ≤ (26875979741271/100000000000000 : ℝ)^99 := by
    have hnat : (3704727171 : ℕ)^131*100000000000000^99 ≤ 26875979741271^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704727171 10000000000 26875979741271 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314746789/10000000000 : ℝ), (251312907/500000000 : ℝ), (3704727171/10000000000 : ℝ)] ![(16441107791777/50000000000000 : ℝ), (20120902333197/50000000000000 : ℝ), (26875979741271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314746789/10000000000 : ℝ)|^131 ≤ (16441107791777/50000000000000 : ℝ)^99
        have hw : |(4314746789/10000000000 : ℝ)|=(4314746789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251312907/500000000 : ℝ)|^131 ≤ (20120902333197/50000000000000 : ℝ)^99
        have hw : |(251312907/500000000 : ℝ)|=(251312907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3704727171/10000000000 : ℝ)|^131 ≤ (26875979741271/100000000000000 : ℝ)^99
        have hw : |(3704727171/10000000000 : ℝ)|=(3704727171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6907/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (307/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (37/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10109/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6907/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (307/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6907/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (307/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6907/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (307/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6907/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (307/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6907/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (307/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6907/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (307/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (307/50000 : ℝ) ^ (8383/2048 : ℝ) ≤ (88388195027/100000000000000000000 : ℝ) := by
    have hpowers : (307/50000 : ℝ)^8383 ≤ (88388195027/100000000000000000000 : ℝ)^2048 := by
      have hnat : (307 : ℕ)^8383*100000000000000000000^2048 ≤ 88388195027^2048*50000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        307 50000 88388195027 100000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (307/50000 : ℝ)) (X := (88388195027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6907/25000 : ℝ) ^ (8383/2048 : ℝ) ≤ (516769744112846771/100000000000000000000 : ℝ) := by
    have hpowers : (6907/25000 : ℝ)^8383 ≤ (516769744112846771/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6907 : ℕ)^8383*100000000000000000000^2048 ≤ 516769744112846771^2048*25000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6907 25000 516769744112846771 100000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6907/25000 : ℝ)) (X := (516769744112846771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000088388195027/50000000000000000000 : ℝ) ≤ (5000000002159359/5000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50000000088388195027/50000000000000000000 : ℝ)^2048 ≤ (5000000002159359/5000000000000000 : ℝ)^8383 := by
      have hnat : (50000000088388195027 : ℕ)^2048*5000000000000000^8383 ≤ 5000000002159359^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000088388195027 50000000000000000000 5000000002159359 5000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000002159359/5000000000000000 : ℝ)) (X := (50000000088388195027/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50258384916250520899/50000000000000000000 : ℝ) ≤ (125157503924017/125000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50258384916250520899/50000000000000000000 : ℝ)^2048 ≤ (125157503924017/125000000000000 : ℝ)^8383 := by
      have hnat : (50258384916250520899 : ℕ)^2048*125000000000000^8383 ≤ 125157503924017^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50258384916250520899 50000000000000000000 125157503924017 125000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125157503924017/125000000000000 : ℝ)) (X := (50258384916250520899/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50516769744112846771/50000000000000000000 : ℝ) ≤ (5012600311762001/5000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50516769744112846771/50000000000000000000 : ℝ)^2048 ≤ (5012600311762001/5000000000000000 : ℝ)^8383 := by
      have hnat : (50516769744112846771 : ℕ)^2048*5000000000000000^8383 ≤ 5012600311762001^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50516769744112846771 50000000000000000000 5012600311762001 5000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012600311762001/5000000000000000 : ℝ)) (X := (50516769744112846771/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(88388195027/100000000000000000000 : ℝ) ≤ ((67531131734118450919/67535000000000000000 : ℝ)+2*(6300154801321/1350700000000000 : ℝ)*(307/50000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (67531131734118450919/67535000000000000000 : ℝ)+2*(6300154801321/1350700000000000 : ℝ)*(307/50000 : ℝ)=(5000000002159359/5000000000000000 : ℝ) by norm_num, show 1+2*(88388195027/100000000000000000000 : ℝ)=(50000000088388195027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(516769744112846771/100000000000000000000 : ℝ)+(88388195027/100000000000000000000 : ℝ) ≤ ((67531131734118450919/67535000000000000000 : ℝ)+(6300154801321/1350700000000000 : ℝ)*((6907/25000 : ℝ)+(307/50000 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (67531131734118450919/67535000000000000000 : ℝ)+(6300154801321/1350700000000000 : ℝ)*((6907/25000 : ℝ)+(307/50000 : ℝ))=(125157503924017/125000000000000 : ℝ) by norm_num, show 1+(516769744112846771/100000000000000000000 : ℝ)+(88388195027/100000000000000000000 : ℝ)=(50258384916250520899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(516769744112846771/100000000000000000000 : ℝ) ≤ ((67531131734118450919/67535000000000000000 : ℝ)+2*(6300154801321/1350700000000000 : ℝ)*(6907/25000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (67531131734118450919/67535000000000000000 : ℝ)+2*(6300154801321/1350700000000000 : ℝ)*(6907/25000 : ℝ)=(5012600311762001/5000000000000000 : ℝ) by norm_num, show 1+2*(516769744112846771/100000000000000000000 : ℝ)=(50516769744112846771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67531131734118450919/67535000000000000000 : ℝ)*(X 1 0+X 2 0)+(6300154801321/1350700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (307/50000 : ℝ)) (hi := (6907/25000 : ℝ)) (c := (67531131734118450919/67535000000000000000 : ℝ)) (alpha := (6300154801321/1350700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67531131734118450919/67535000000000000000 : ℝ)*(X 0 1+X 2 1)+(6300154801321/1350700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (307/50000 : ℝ)) (hi := (6907/25000 : ℝ)) (c := (67531131734118450919/67535000000000000000 : ℝ)) (alpha := (6300154801321/1350700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67531131734118450919/67535000000000000000 : ℝ)*(X 0 2+X 1 2)+(6300154801321/1350700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (307/50000 : ℝ)) (hi := (6907/25000 : ℝ)) (c := (67531131734118450919/67535000000000000000 : ℝ)) (alpha := (6300154801321/1350700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-519379487/2500000000 : ℝ)*X 0 0+(5688599597/10000000000 : ℝ)*X 0 1+(100247399/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5416435561/10000000000 : ℝ)*X 1 0+(-610386871/2500000000 : ℝ)*X 1 1+(626546281/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((270821731/500000000 : ℝ)*X 2 0+(1002474173/2000000000 : ℝ)*X 2 1+(-2441547921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431326167/1000000000 : ℝ)*X 0 0+(1843087133/5000000000 : ℝ)*X 0 1+(2522229091/5000000000 : ℝ)*X 0 2+(431326167/1000000000 : ℝ)*X 1 0+(1843087133/5000000000 : ℝ)*X 1 1+(2522229091/5000000000 : ℝ)*X 1 2+(431326167/1000000000 : ℝ)*X 2 0+(1843087133/5000000000 : ℝ)*X 2 1+(2522229091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2078257867/10000000000 : ℝ)*X 0 0+(2510715537/5000000000 : ℝ)*X 0 1+(2839681181/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5242642591/10000000000 : ℝ)*X 1 0+(-1774555071/10000000000 : ℝ)*X 1 1+(709920357/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5242642473/10000000000 : ℝ)*X 2 0+(5679363563/10000000000 : ℝ)*X 2 1+(-55454819/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4314746789/10000000000 : ℝ)*X 0 0+(251312907/500000000 : ℝ)*X 0 1+(3704727171/10000000000 : ℝ)*X 0 2+(4314746789/10000000000 : ℝ)*X 1 0+(251312907/500000000 : ℝ)*X 1 1+(3704727171/10000000000 : ℝ)*X 1 2+(4314746789/10000000000 : ℝ)*X 2 0+(251312907/500000000 : ℝ)*X 2 1+(3704727171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3225547199650599874865525973/1688375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (460069/3125000000000 : ℝ)*(base16) + (591760581/100000000000000 : ℝ)*(base19) + (203100641/50000000000000 : ℝ)*(base23) + (15336711/50000000000000 : ℝ)*(upper2) + (17479897/12500000000000 : ℝ)*(upper3) + (1107511318400889/100000000000000 : ℝ)*(major0) + (1107511318400889/100000000000000 : ℝ)*(major1) + (1107511318400889/100000000000000 : ℝ)*(major2) + (739396266810043/50000000000000 : ℝ)*(sp0) + (739397402849489/50000000000000 : ℝ)*(sp1) + (739397502990243/50000000000000 : ℝ)*(sp2) + (368112475615191/50000000000000 : ℝ)*(sp3) + (1439280841/50000000000000 : ℝ)*(sp4) + (69053379/3125000000000 : ℝ)*(sp7) + (736227160938509/100000000000000 : ℝ)*(f.failure) + (184849426522721/12500000000000 : ℝ)*(f.sum) + (44541584759481/67535000000000000000000000000 : ℝ)*base66 + (32740595838566083009/6753500000000000000000000000000000 : ℝ)*base68 + (53476114431355083009/6753500000000000000000000000000000 : ℝ)*base70 + (22266540335434083009/6753500000000000000000000000000000 : ℝ)*base72 + (271252329781931/67535000000000000000000000000 : ℝ)*base74 + (7695886715784916991/6753500000000000000000000000000000 : ℝ)*base75 + (32493153744251083009/6753500000000000000000000000000000 : ℝ)*base78 + (34048941803596083009/6753500000000000000000000000000000 : ℝ)*base80 + (211519082793841/67535000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (14805533/2500000000000000000000 : ℝ)*base90 + (14805533/2500000000000000000000 : ℝ)*base92 + (14805533/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49557761017750747761969/67535000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140896591/20000000000000 : ℝ)*(base19) + (507463043/50000000000000 : ℝ)*(base23) + (61393427/50000000000000 : ℝ)*(upper2) + (69845067/50000000000000 : ℝ)*(upper3) + (13975893/20000000000000 : ℝ)*(upper5) + (284576575279007/25000000000000 : ℝ)*(major0) + (284576575279007/25000000000000 : ℝ)*(major1) + (284576575279007/25000000000000 : ℝ)*(major2) + (449358709/12500000000000 : ℝ)*(sp1) + (1731647101/25000000000000 : ℝ)*(sp2) + (1519914201488703/100000000000000 : ℝ)*(sp4) + (379977475534019/25000000000000 : ℝ)*(sp5) + (1519906259974213/100000000000000 : ℝ)*(sp6) + (151339675256613/20000000000000 : ℝ)*(sp7) + (151339675256613/20000000000000 : ℝ)*(f.failure) + (1519914201488703/100000000000000 : ℝ)*(f.sum) + (57894356860137/16883750000000000000000000000 : ℝ)*base65 + (8441477175008842567/1688375000000000000000000000000000 : ℝ)*base68 + (137325917134532433/1688375000000000000000000000000000 : ℝ)*base69 + (503379812991532433/1688375000000000000000000000000000 : ℝ)*base71 + (105550484735743/16883750000000000000000000000 : ℝ)*base74 + (328522452563217567/1688375000000000000000000000000000 : ℝ)*base76 + (6618207529523157433/1688375000000000000000000000000000 : ℝ)*base77 + (9089970796633717567/1688375000000000000000000000000000 : ℝ)*base80 + (139234359344957/67535000000000000000000000000 : ℝ)*base82 + (225419/500000000000000000000 : ℝ)*base89 + (225419/500000000000000000000 : ℝ)*base91 + (225419/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1191_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6907/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (307/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (37/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10109/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1191_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1191_s2_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128161357/10000000000 : ℝ)*x 0 + (5501715853/10000000000 : ℝ)*x 1 + (1291750979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128161357/10000000000 : ℝ)^131 ≤ (12906066648211/100000000000000 : ℝ)^99 := by
    have hnat : (2128161357 : ℕ)^131*100000000000000^99 ≤ 12906066648211^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128161357 10000000000 12906066648211 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501715853/10000000000 : ℝ)^131 ≤ (45354331800393/100000000000000 : ℝ)^99 := by
    have hnat : (5501715853 : ℕ)^131*100000000000000^99 ≤ 45354331800393^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501715853 10000000000 45354331800393 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291750979/2500000000 : ℝ)^131 ≤ (10434900384109/25000000000000 : ℝ)^99 := by
    have hnat : (1291750979 : ℕ)^131*25000000000000^99 ≤ 10434900384109^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291750979 2500000000 10434900384109 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128161357/10000000000 : ℝ), (5501715853/10000000000 : ℝ), (1291750979/2500000000 : ℝ)] ![(12906066648211/100000000000000 : ℝ), (45354331800393/100000000000000 : ℝ), (10434900384109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128161357/10000000000 : ℝ)|^131 ≤ (12906066648211/100000000000000 : ℝ)^99
        have hw : |(-2128161357/10000000000 : ℝ)|=(2128161357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501715853/10000000000 : ℝ)|^131 ≤ (45354331800393/100000000000000 : ℝ)^99
        have hw : |(5501715853/10000000000 : ℝ)|=(5501715853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291750979/2500000000 : ℝ)|^131 ≤ (10434900384109/25000000000000 : ℝ)^99
        have hw : |(1291750979/2500000000 : ℝ)|=(1291750979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s2_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (134294561/250000000 : ℝ)*x 0 + (-287731611/1250000000 : ℝ)*x 1 + (2583503983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134294561/250000000 : ℝ)^131 ≤ (10985604818059/25000000000000 : ℝ)^99 := by
    have hnat : (134294561 : ℕ)^131*25000000000000^99 ≤ 10985604818059^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134294561 250000000 10985604818059 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287731611/1250000000 : ℝ)^131 ≤ (14317935886431/100000000000000 : ℝ)^99 := by
    have hnat : (287731611 : ℕ)^131*100000000000000^99 ≤ 14317935886431^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287731611 1250000000 14317935886431 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583503983/5000000000 : ℝ)^131 ≤ (20869822413871/50000000000000 : ℝ)^99 := by
    have hnat : (2583503983 : ℕ)^131*50000000000000^99 ≤ 20869822413871^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583503983 5000000000 20869822413871 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134294561/250000000 : ℝ), (-287731611/1250000000 : ℝ), (2583503983/5000000000 : ℝ)] ![(10985604818059/25000000000000 : ℝ), (14317935886431/100000000000000 : ℝ), (20869822413871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134294561/250000000 : ℝ)|^131 ≤ (10985604818059/25000000000000 : ℝ)^99
        have hw : |(134294561/250000000 : ℝ)|=(134294561/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-287731611/1250000000 : ℝ)|^131 ≤ (14317935886431/100000000000000 : ℝ)^99
        have hw : |(-287731611/1250000000 : ℝ)|=(287731611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2583503983/5000000000 : ℝ)|^131 ≤ (20869822413871/50000000000000 : ℝ)^99
        have hw : |(2583503983/5000000000 : ℝ)|=(2583503983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s2_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5371784063/10000000000 : ℝ)*x 0 + (2583502843/5000000000 : ℝ)*x 1 + (-1150926857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371784063/10000000000 : ℝ)^131 ≤ (878848736803/2000000000000 : ℝ)^99 := by
    have hnat : (5371784063 : ℕ)^131*2000000000000^99 ≤ 878848736803^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371784063 10000000000 878848736803 2000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2583502843/5000000000 : ℝ)^131 ≤ (41739620456339/100000000000000 : ℝ)^99 := by
    have hnat : (2583502843 : ℕ)^131*100000000000000^99 ≤ 41739620456339^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583502843 5000000000 41739620456339 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1150926857/5000000000 : ℝ)^131 ≤ (447435708907/3125000000000 : ℝ)^99 := by
    have hnat : (1150926857 : ℕ)^131*3125000000000^99 ≤ 447435708907^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150926857 5000000000 447435708907 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371784063/10000000000 : ℝ), (2583502843/5000000000 : ℝ), (-1150926857/5000000000 : ℝ)] ![(878848736803/2000000000000 : ℝ), (41739620456339/100000000000000 : ℝ), (447435708907/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371784063/10000000000 : ℝ)|^131 ≤ (878848736803/2000000000000 : ℝ)^99
        have hw : |(5371784063/10000000000 : ℝ)|=(5371784063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2583502843/5000000000 : ℝ)|^131 ≤ (41739620456339/100000000000000 : ℝ)^99
        have hw : |(2583502843/5000000000 : ℝ)|=(2583502843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1150926857/5000000000 : ℝ)|^131 ≤ (447435708907/3125000000000 : ℝ)^99
        have hw : |(-1150926857/5000000000 : ℝ)|=(1150926857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s2_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2174061663/5000000000 : ℝ)*x 0 + (503088129/1250000000 : ℝ)*x 1 + (117425189/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174061663/5000000000 : ℝ)^131 ≤ (33219211621663/100000000000000 : ℝ)^99 := by
    have hnat : (2174061663 : ℕ)^131*100000000000000^99 ≤ 33219211621663^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174061663 5000000000 33219211621663 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503088129/1250000000 : ℝ)^131 ≤ (14994822593353/50000000000000 : ℝ)^99 := by
    have hnat : (503088129 : ℕ)^131*50000000000000^99 ≤ 14994822593353^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503088129 1250000000 14994822593353 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117425189/250000000 : ℝ)^131 ≤ (1839557158431/5000000000000 : ℝ)^99 := by
    have hnat : (117425189 : ℕ)^131*5000000000000^99 ≤ 1839557158431^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117425189 250000000 1839557158431 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174061663/5000000000 : ℝ), (503088129/1250000000 : ℝ), (117425189/250000000 : ℝ)] ![(33219211621663/100000000000000 : ℝ), (14994822593353/50000000000000 : ℝ), (1839557158431/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174061663/5000000000 : ℝ)|^131 ≤ (33219211621663/100000000000000 : ℝ)^99
        have hw : |(2174061663/5000000000 : ℝ)|=(2174061663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503088129/1250000000 : ℝ)|^131 ≤ (14994822593353/50000000000000 : ℝ)^99
        have hw : |(503088129/1250000000 : ℝ)|=(503088129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117425189/250000000 : ℝ)|^131 ≤ (1839557158431/5000000000000 : ℝ)^99
        have hw : |(117425189/250000000 : ℝ)|=(117425189/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s2_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128250203/10000000000 : ℝ)*x 0 + (5169234921/10000000000 : ℝ)*x 1 + (2749731997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128250203/10000000000 : ℝ)^131 ≤ (3226694902503/25000000000000 : ℝ)^99 := by
    have hnat : (2128250203 : ℕ)^131*25000000000000^99 ≤ 3226694902503^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128250203 10000000000 3226694902503 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5169234921/10000000000 : ℝ)^131 ≤ (20881725440687/50000000000000 : ℝ)^99 := by
    have hnat : (5169234921 : ℕ)^131*50000000000000^99 ≤ 20881725440687^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169234921 10000000000 20881725440687 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2749731997/5000000000 : ℝ)^131 ≤ (45329769492049/100000000000000 : ℝ)^99 := by
    have hnat : (2749731997 : ℕ)^131*100000000000000^99 ≤ 45329769492049^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749731997 5000000000 45329769492049 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128250203/10000000000 : ℝ), (5169234921/10000000000 : ℝ), (2749731997/5000000000 : ℝ)] ![(3226694902503/25000000000000 : ℝ), (20881725440687/50000000000000 : ℝ), (45329769492049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128250203/10000000000 : ℝ)|^131 ≤ (3226694902503/25000000000000 : ℝ)^99
        have hw : |(-2128250203/10000000000 : ℝ)|=(2128250203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5169234921/10000000000 : ℝ)|^131 ≤ (20881725440687/50000000000000 : ℝ)^99
        have hw : |(5169234921/10000000000 : ℝ)|=(5169234921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2749731997/5000000000 : ℝ)|^131 ≤ (45329769492049/100000000000000 : ℝ)^99
        have hw : |(2749731997/5000000000 : ℝ)|=(2749731997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s2_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (33041151/62500000 : ℝ)*x 0 + (-246174409/1250000000 : ℝ)*x 1 + (687433001/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33041151/62500000 : ℝ)^131 ≤ (43022576063913/100000000000000 : ℝ)^99 := by
    have hnat : (33041151 : ℕ)^131*100000000000000^99 ≤ 43022576063913^99*62500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33041151 62500000 43022576063913 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246174409/1250000000 : ℝ)^131 ≤ (1455956785773/12500000000000 : ℝ)^99 := by
    have hnat : (246174409 : ℕ)^131*12500000000000^99 ≤ 1455956785773^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246174409 1250000000 1455956785773 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687433001/1250000000 : ℝ)^131 ≤ (9065953928949/20000000000000 : ℝ)^99 := by
    have hnat : (687433001 : ℕ)^131*20000000000000^99 ≤ 9065953928949^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687433001 1250000000 9065953928949 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33041151/62500000 : ℝ), (-246174409/1250000000 : ℝ), (687433001/1250000000 : ℝ)] ![(43022576063913/100000000000000 : ℝ), (1455956785773/12500000000000 : ℝ), (9065953928949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33041151/62500000 : ℝ)|^131 ≤ (43022576063913/100000000000000 : ℝ)^99
        have hw : |(33041151/62500000 : ℝ)|=(33041151/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246174409/1250000000 : ℝ)|^131 ≤ (1455956785773/12500000000000 : ℝ)^99
        have hw : |(-246174409/1250000000 : ℝ)|=(246174409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(687433001/1250000000 : ℝ)|^131 ≤ (9065953928949/20000000000000 : ℝ)^99
        have hw : |(687433001/1250000000 : ℝ)|=(687433001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s2_6 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2643292161/5000000000 : ℝ)*x 0 + (2749732009/5000000000 : ℝ)*x 1 + (-984697517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643292161/5000000000 : ℝ)^131 ≤ (43022577808419/100000000000000 : ℝ)^99 := by
    have hnat : (2643292161 : ℕ)^131*100000000000000^99 ≤ 43022577808419^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643292161 5000000000 43022577808419 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749732009/5000000000 : ℝ)^131 ≤ (45329769753813/100000000000000 : ℝ)^99 := by
    have hnat : (2749732009 : ℕ)^131*100000000000000^99 ≤ 45329769753813^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749732009 5000000000 45329769753813 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (984697517/5000000000 : ℝ)^131 ≤ (2911913105897/25000000000000 : ℝ)^99 := by
    have hnat : (984697517 : ℕ)^131*25000000000000^99 ≤ 2911913105897^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984697517 5000000000 2911913105897 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643292161/5000000000 : ℝ), (2749732009/5000000000 : ℝ), (-984697517/5000000000 : ℝ)] ![(43022577808419/100000000000000 : ℝ), (45329769753813/100000000000000 : ℝ), (2911913105897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643292161/5000000000 : ℝ)|^131 ≤ (43022577808419/100000000000000 : ℝ)^99
        have hw : |(2643292161/5000000000 : ℝ)|=(2643292161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749732009/5000000000 : ℝ)|^131 ≤ (45329769753813/100000000000000 : ℝ)^99
        have hw : |(2749732009/5000000000 : ℝ)|=(2749732009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-984697517/5000000000 : ℝ)|^131 ≤ (2911913105897/25000000000000 : ℝ)^99
        have hw : |(-984697517/5000000000 : ℝ)|=(984697517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s2_7 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2174151983/5000000000 : ℝ)*x 0 + (1173132257/2500000000 : ℝ)*x 1 + (2014613051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174151983/5000000000 : ℝ)^131 ≤ (16610518894161/50000000000000 : ℝ)^99 := by
    have hnat : (2174151983 : ℕ)^131*50000000000000^99 ≤ 16610518894161^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174151983 5000000000 16610518894161 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1173132257/2500000000 : ℝ)^131 ≤ (18372365767131/50000000000000 : ℝ)^99 := by
    have hnat : (1173132257 : ℕ)^131*50000000000000^99 ≤ 18372365767131^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173132257 2500000000 18372365767131 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014613051/5000000000 : ℝ)^131 ≤ (7508557666033/25000000000000 : ℝ)^99 := by
    have hnat : (2014613051 : ℕ)^131*25000000000000^99 ≤ 7508557666033^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014613051 5000000000 7508557666033 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174151983/5000000000 : ℝ), (1173132257/2500000000 : ℝ), (2014613051/5000000000 : ℝ)] ![(16610518894161/50000000000000 : ℝ), (18372365767131/50000000000000 : ℝ), (7508557666033/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174151983/5000000000 : ℝ)|^131 ≤ (16610518894161/50000000000000 : ℝ)^99
        have hw : |(2174151983/5000000000 : ℝ)|=(2174151983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1173132257/2500000000 : ℝ)|^131 ≤ (18372365767131/50000000000000 : ℝ)^99
        have hw : |(1173132257/2500000000 : ℝ)|=(1173132257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014613051/5000000000 : ℝ)|^131 ≤ (7508557666033/25000000000000 : ℝ)^99
        have hw : |(2014613051/5000000000 : ℝ)|=(2014613051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10109/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (37/625 : ℝ)*pair X i i ≤ pair X i h) :
    (9287/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16361/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10109/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (37/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10109/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (37/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10109/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (37/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10109/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (37/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10109/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (37/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10109/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (37/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (37/625 : ℝ) ^ (8383/2048 : ℝ) ≤ (188721523940617/20000000000000000000 : ℝ) := by
    have hpowers : (37/625 : ℝ)^8383 ≤ (188721523940617/20000000000000000000 : ℝ)^2048 := by
      have hnat : (37 : ℕ)^8383*20000000000000000000^2048 ≤ 188721523940617^2048*625^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37 625 188721523940617 20000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37/625 : ℝ)) (X := (188721523940617/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10109/50000 : ℝ) ^ (8383/2048 : ℝ) ≤ (17993462055640787/12500000000000000000 : ℝ) := by
    have hpowers : (10109/50000 : ℝ)^8383 ≤ (17993462055640787/12500000000000000000 : ℝ)^2048 := by
      have hnat : (10109 : ℕ)^8383*12500000000000000000^2048 ≤ 17993462055640787^2048*50000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10109 50000 17993462055640787 12500000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10109/50000 : ℝ)) (X := (17993462055640787/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000188721523940617/10000000000000000000 : ℝ) ≤ (2000009221016939/2000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (10000188721523940617/10000000000000000000 : ℝ)^2048 ≤ (2000009221016939/2000000000000000 : ℝ)^8383 := by
      have hnat : (10000188721523940617 : ℕ)^2048*2000000000000000^8383 ≤ 2000009221016939^8383*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000188721523940617 10000000000000000000 2000009221016939 2000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000009221016939/2000000000000000 : ℝ)) (X := (10000188721523940617/10000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100144891304064829381/100000000000000000000 : ℝ) ≤ (625221113469103/625000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (100144891304064829381/100000000000000000000 : ℝ)^2048 ≤ (625221113469103/625000000000000 : ℝ)^8383 := by
      have hnat : (100144891304064829381 : ℕ)^2048*625000000000000^8383 ≤ 625221113469103^8383*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100144891304064829381 100000000000000000000 625221113469103 625000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625221113469103/625000000000000 : ℝ)) (X := (100144891304064829381/100000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6267993462055640787/6250000000000000000 : ℝ) ≤ (10007029525926601/10000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (6267993462055640787/6250000000000000000 : ℝ)^2048 ≤ (10007029525926601/10000000000000000 : ℝ)^8383 := by
      have hnat : (6267993462055640787 : ℕ)^2048*10000000000000000^8383 ≤ 10007029525926601^8383*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6267993462055640787 6250000000000000000 10007029525926601 10000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007029525926601/10000000000000000 : ℝ)) (X := (6267993462055640787/6250000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(188721523940617/20000000000000000000 : ℝ) ≤ ((4764643911970562853/4766000000000000000 : ℝ)+2*(1163903473651/476600000000000 : ℝ)*(37/625 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (4764643911970562853/4766000000000000000 : ℝ)+2*(1163903473651/476600000000000 : ℝ)*(37/625 : ℝ)=(2000009221016939/2000000000000000 : ℝ) by norm_num, show 1+2*(188721523940617/20000000000000000000 : ℝ)=(10000188721523940617/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17993462055640787/12500000000000000000 : ℝ)+(188721523940617/20000000000000000000 : ℝ) ≤ ((4764643911970562853/4766000000000000000 : ℝ)+(1163903473651/476600000000000 : ℝ)*((10109/50000 : ℝ)+(37/625 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (4764643911970562853/4766000000000000000 : ℝ)+(1163903473651/476600000000000 : ℝ)*((10109/50000 : ℝ)+(37/625 : ℝ))=(625221113469103/625000000000000 : ℝ) by norm_num, show 1+(17993462055640787/12500000000000000000 : ℝ)+(188721523940617/20000000000000000000 : ℝ)=(100144891304064829381/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17993462055640787/12500000000000000000 : ℝ) ≤ ((4764643911970562853/4766000000000000000 : ℝ)+2*(1163903473651/476600000000000 : ℝ)*(10109/50000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (4764643911970562853/4766000000000000000 : ℝ)+2*(1163903473651/476600000000000 : ℝ)*(10109/50000 : ℝ)=(10007029525926601/10000000000000000 : ℝ) by norm_num, show 1+2*(17993462055640787/12500000000000000000 : ℝ)=(6267993462055640787/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4764643911970562853/4766000000000000000 : ℝ)*(X 1 0+X 2 0)+(1163903473651/476600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (37/625 : ℝ)) (hi := (10109/50000 : ℝ)) (c := (4764643911970562853/4766000000000000000 : ℝ)) (alpha := (1163903473651/476600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4764643911970562853/4766000000000000000 : ℝ)*(X 0 1+X 2 1)+(1163903473651/476600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (37/625 : ℝ)) (hi := (10109/50000 : ℝ)) (c := (4764643911970562853/4766000000000000000 : ℝ)) (alpha := (1163903473651/476600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4764643911970562853/4766000000000000000 : ℝ)*(X 0 2+X 1 2)+(1163903473651/476600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (37/625 : ℝ)) (hi := (10109/50000 : ℝ)) (c := (4764643911970562853/4766000000000000000 : ℝ)) (alpha := (1163903473651/476600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2128161357/10000000000 : ℝ)*X 0 0+(5501715853/10000000000 : ℝ)*X 0 1+(1291750979/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((134294561/250000000 : ℝ)*X 1 0+(-287731611/1250000000 : ℝ)*X 1 1+(2583503983/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5371784063/10000000000 : ℝ)*X 2 0+(2583502843/5000000000 : ℝ)*X 2 1+(-1150926857/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174061663/5000000000 : ℝ)*X 0 0+(503088129/1250000000 : ℝ)*X 0 1+(117425189/250000000 : ℝ)*X 0 2+(2174061663/5000000000 : ℝ)*X 1 0+(503088129/1250000000 : ℝ)*X 1 1+(117425189/250000000 : ℝ)*X 1 2+(2174061663/5000000000 : ℝ)*X 2 0+(503088129/1250000000 : ℝ)*X 2 1+(117425189/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2128250203/10000000000 : ℝ)*X 0 0+(5169234921/10000000000 : ℝ)*X 0 1+(2749731997/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((33041151/62500000 : ℝ)*X 1 0+(-246174409/1250000000 : ℝ)*X 1 1+(687433001/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643292161/5000000000 : ℝ)*X 2 0+(2749732009/5000000000 : ℝ)*X 2 1+(-984697517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174151983/5000000000 : ℝ)*X 0 0+(1173132257/2500000000 : ℝ)*X 0 1+(2014613051/5000000000 : ℝ)*X 0 2+(2174151983/5000000000 : ℝ)*X 1 0+(1173132257/2500000000 : ℝ)*X 1 1+(2014613051/5000000000 : ℝ)*X 1 2+(2174151983/5000000000 : ℝ)*X 2 0+(1173132257/2500000000 : ℝ)*X 2 1+(2014613051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (163596083082195228096592953/119150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (298637669/100000000000000 : ℝ)*(base23) + (50478937/100000000000000 : ℝ)*(upper2) + (20126453/6250000000000 : ℝ)*(upper3) + (16167229/5000000000000 : ℝ)*(upper4) + (1118784716100189/50000000000000 : ℝ)*(major0) + (1118784716100189/50000000000000 : ℝ)*(major1) + (1118784716100189/50000000000000 : ℝ)*(major2) + (93364675664407/3125000000000 : ℝ)*(sp0) + (2987696331047381/100000000000000 : ℝ)*(sp1) + (298768997420289/10000000000000 : ℝ)*(sp2) + (743715703767039/50000000000000 : ℝ)*(sp3) + (26709786357/100000000000000 : ℝ)*(sp4) + (3029103411/50000000000000 : ℝ)*(sp6) + (11080051749/100000000000000 : ℝ)*(sp7) + (1487442487585827/100000000000000 : ℝ)*(f.failure) + (2987696331047381/100000000000000 : ℝ)*(f.sum) + (38520115556253/5957500000000000000000000000 : ℝ)*base66 + (1507160194757030783/238300000000000000000000000000000 : ℝ)*base68 + (150266931865930783/238300000000000000000000000000000 : ℝ)*base70 + (2708690924486530783/238300000000000000000000000000000 : ℝ)*base72 + (20424371608061/11915000000000000000000000000 : ℝ)*base74 + (1372826287579130783/238300000000000000000000000000000 : ℝ)*base76 + (846471056752730783/238300000000000000000000000000000 : ℝ)*base78 + (671484289823130783/238300000000000000000000000000000 : ℝ)*base80 + (41124198846989/11915000000000000000000000000 : ℝ)*base81 + (15392301/2500000000000000000000 : ℝ)*base89 + (15392301/2500000000000000000000 : ℝ)*base91 + (15392301/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84888039222159826162055961/9532000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2085332279/100000000000000 : ℝ)*(base19) + (448230121/20000000000000 : ℝ)*(base23) + (51328663/20000000000000 : ℝ)*(upper3) + (705457/20000000000000 : ℝ)*(lower4) + (185484957/100000000000000 : ℝ)*(upper5) + (90716161724279/4000000000000 : ℝ)*(major0) + (90716161724279/4000000000000 : ℝ)*(major1) + (90716161724279/4000000000000 : ℝ)*(major2) + (20637539291/100000000000000 : ℝ)*(sp1) + (12066871389/50000000000000 : ℝ)*(sp2) + (151410006116829/5000000000000 : ℝ)*(sp4) + (302817739946501/10000000000000 : ℝ)*(sp5) + (757043436860799/25000000000000 : ℝ)*(sp6) + (37690191675613/2500000000000 : ℝ)*(sp7) + (37690191675613/2500000000000 : ℝ)*(f.failure) + (151410006116829/5000000000000 : ℝ)*(f.sum) + (1137172024227/953200000000000000000000000 : ℝ)*base66 + (65010567219462013/19064000000000000000000000000000 : ℝ)*base68 + (36453549667942013/19064000000000000000000000000000 : ℝ)*base70 + (152835769517542013/19064000000000000000000000000000 : ℝ)*base72 + (5053887878233/4766000000000000000000000000 : ℝ)*base73 + (23609211428566013/19064000000000000000000000000000 : ℝ)*base76 + (29857812225353987/19064000000000000000000000000000 : ℝ)*base77 + (71551593304953987/19064000000000000000000000000000 : ℝ)*base79 + (6311904786001/4766000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (352581/62500000000000000000 : ℝ)*base90 + (352581/62500000000000000000 : ℝ)*base92 + (352581/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1191_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10109/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (37/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9287/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16361/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1191_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1191_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9287/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16361/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1191_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1191_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1191_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9287/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16361/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1191_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
