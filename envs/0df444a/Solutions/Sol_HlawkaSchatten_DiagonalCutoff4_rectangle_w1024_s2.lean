-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1024_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:15:15.570244+00:00
-- url     : https://prove2.me/submissions/b1db2a2b-07c8-458c-94f6-3dd8bc4f05a9

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
theorem support_rectangle_w1024_s2_0 (p : ℝ) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202736809/10000000000 : ℝ)*x 0 + (5534442037/10000000000 : ℝ)*x 1 + (2569233037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202736809/10000000000 : ℝ)^8217 ≤ (6665115848527/50000000000000 : ℝ)^6169 := by
    have hnat : (2202736809 : ℕ)^8217*50000000000000^6169 ≤ 6665115848527^6169*10000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202736809 10000000000 6665115848527 50000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5534442037/10000000000 : ℝ)^8217 ≤ (227378219659/500000000000 : ℝ)^6169 := by
    have hnat : (5534442037 : ℕ)^8217*500000000000^6169 ≤ 227378219659^6169*10000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5534442037 10000000000 227378219659 500000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569233037/5000000000 : ℝ)^8217 ≤ (20597062180607/50000000000000 : ℝ)^6169 := by
    have hnat : (2569233037 : ℕ)^8217*50000000000000^6169 ≤ 20597062180607^6169*5000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569233037 5000000000 20597062180607 50000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8217/2048 : ℝ)) 8217 6169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202736809/10000000000 : ℝ), (5534442037/10000000000 : ℝ), (2569233037/5000000000 : ℝ)] ![(6665115848527/50000000000000 : ℝ), (227378219659/500000000000 : ℝ), (20597062180607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202736809/10000000000 : ℝ)|^8217 ≤ (6665115848527/50000000000000 : ℝ)^6169
        have hw : |(-2202736809/10000000000 : ℝ)|=(2202736809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5534442037/10000000000 : ℝ)|^8217 ≤ (227378219659/500000000000 : ℝ)^6169
        have hw : |(5534442037/10000000000 : ℝ)|=(5534442037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569233037/5000000000 : ℝ)|^8217 ≤ (20597062180607/50000000000000 : ℝ)^6169
        have hw : |(2569233037/5000000000 : ℝ)|=(2569233037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1024_s2_1 (p : ℝ) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1075805379/2000000000 : ℝ)*x 0 + (-120480223/500000000 : ℝ)*x 1 + (2569233947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075805379/2000000000 : ℝ)^8217 ≤ (10945662995751/25000000000000 : ℝ)^6169 := by
    have hnat : (1075805379 : ℕ)^8217*25000000000000^6169 ≤ 10945662995751^6169*2000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075805379 2000000000 10945662995751 25000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120480223/500000000 : ℝ)^8217 ≤ (7511602100081/50000000000000 : ℝ)^6169 := by
    have hnat : (120480223 : ℕ)^8217*50000000000000^6169 ≤ 7511602100081^6169*500000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120480223 500000000 7511602100081 50000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569233947/5000000000 : ℝ)^8217 ≤ (1029853594891/2500000000000 : ℝ)^6169 := by
    have hnat : (2569233947 : ℕ)^8217*2500000000000^6169 ≤ 1029853594891^6169*5000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569233947 5000000000 1029853594891 2500000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8217/2048 : ℝ)) 8217 6169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075805379/2000000000 : ℝ), (-120480223/500000000 : ℝ), (2569233947/5000000000 : ℝ)] ![(10945662995751/25000000000000 : ℝ), (7511602100081/50000000000000 : ℝ), (1029853594891/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075805379/2000000000 : ℝ)|^8217 ≤ (10945662995751/25000000000000 : ℝ)^6169
        have hw : |(1075805379/2000000000 : ℝ)|=(1075805379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120480223/500000000 : ℝ)|^8217 ≤ (7511602100081/50000000000000 : ℝ)^6169
        have hw : |(-120480223/500000000 : ℝ)|=(120480223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569233947/5000000000 : ℝ)|^8217 ≤ (1029853594891/2500000000000 : ℝ)^6169
        have hw : |(2569233947/5000000000 : ℝ)|=(2569233947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1024_s2_2 (p : ℝ) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1075805583/2000000000 : ℝ)*x 0 + (2569233217/5000000000 : ℝ)*x 1 + (-2409605007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075805583/2000000000 : ℝ)^8217 ≤ (1751306521661/4000000000000 : ℝ)^6169 := by
    have hnat : (1075805583 : ℕ)^8217*4000000000000^6169 ≤ 1751306521661^6169*2000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075805583 2000000000 1751306521661 4000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569233217/5000000000 : ℝ)^8217 ≤ (20597064102693/50000000000000 : ℝ)^6169 := by
    have hnat : (2569233217 : ℕ)^8217*50000000000000^6169 ≤ 20597064102693^6169*5000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569233217 5000000000 20597064102693 50000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2409605007/10000000000 : ℝ)^8217 ≤ (15023208742743/100000000000000 : ℝ)^6169 := by
    have hnat : (2409605007 : ℕ)^8217*100000000000000^6169 ≤ 15023208742743^6169*10000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409605007 10000000000 15023208742743 100000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8217/2048 : ℝ)) 8217 6169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075805583/2000000000 : ℝ), (2569233217/5000000000 : ℝ), (-2409605007/10000000000 : ℝ)] ![(1751306521661/4000000000000 : ℝ), (20597064102693/50000000000000 : ℝ), (15023208742743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075805583/2000000000 : ℝ)|^8217 ≤ (1751306521661/4000000000000 : ℝ)^6169
        have hw : |(1075805583/2000000000 : ℝ)|=(1075805583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569233217/5000000000 : ℝ)|^8217 ≤ (20597064102693/50000000000000 : ℝ)^6169
        have hw : |(2569233217/5000000000 : ℝ)|=(2569233217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2409605007/10000000000 : ℝ)|^8217 ≤ (15023208742743/100000000000000 : ℝ)^6169
        have hw : |(-2409605007/10000000000 : ℝ)|=(2409605007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1024_s2_3 (p : ℝ) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873599463/2000000000 : ℝ)*x 0 + (2000231489/5000000000 : ℝ)*x 1 + (4770058657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873599463/2000000000 : ℝ)^8217 ≤ (2073683261163/6250000000000 : ℝ)^6169 := by
    have hnat : (873599463 : ℕ)^8217*6250000000000^6169 ≤ 2073683261163^6169*2000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873599463 2000000000 2073683261163 6250000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000231489/5000000000 : ℝ)^8217 ≤ (14756651830653/50000000000000 : ℝ)^6169 := by
    have hnat : (2000231489 : ℕ)^8217*50000000000000^6169 ≤ 14756651830653^6169*5000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000231489 5000000000 14756651830653 50000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770058657/10000000000 : ℝ)^8217 ≤ (37307764140899/100000000000000 : ℝ)^6169 := by
    have hnat : (4770058657 : ℕ)^8217*100000000000000^6169 ≤ 37307764140899^6169*10000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770058657 10000000000 37307764140899 100000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8217/2048 : ℝ)) 8217 6169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873599463/2000000000 : ℝ), (2000231489/5000000000 : ℝ), (4770058657/10000000000 : ℝ)] ![(2073683261163/6250000000000 : ℝ), (14756651830653/50000000000000 : ℝ), (37307764140899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873599463/2000000000 : ℝ)|^8217 ≤ (2073683261163/6250000000000 : ℝ)^6169
        have hw : |(873599463/2000000000 : ℝ)|=(873599463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2000231489/5000000000 : ℝ)|^8217 ≤ (14756651830653/50000000000000 : ℝ)^6169
        have hw : |(2000231489/5000000000 : ℝ)|=(2000231489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770058657/10000000000 : ℝ)|^8217 ≤ (37307764140899/100000000000000 : ℝ)^6169
        have hw : |(4770058657/10000000000 : ℝ)|=(4770058657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1024_s2_4 (p : ℝ) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101438717/5000000000 : ℝ)*x 0 + (2570714071/5000000000 : ℝ)*x 1 + (138286199/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101438717/5000000000 : ℝ)^8217 ≤ (833210327951/6250000000000 : ℝ)^6169 := by
    have hnat : (1101438717 : ℕ)^8217*6250000000000^6169 ≤ 833210327951^6169*5000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101438717 5000000000 833210327951 6250000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570714071/5000000000 : ℝ)^8217 ≤ (20612878552793/50000000000000 : ℝ)^6169 := by
    have hnat : (2570714071 : ℕ)^8217*50000000000000^6169 ≤ 20612878552793^6169*5000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570714071 5000000000 20612878552793 50000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138286199/250000000 : ℝ)^8217 ≤ (22721438812631/50000000000000 : ℝ)^6169 := by
    have hnat : (138286199 : ℕ)^8217*50000000000000^6169 ≤ 22721438812631^6169*250000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138286199 250000000 22721438812631 50000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8217/2048 : ℝ)) 8217 6169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101438717/5000000000 : ℝ), (2570714071/5000000000 : ℝ), (138286199/250000000 : ℝ)] ![(833210327951/6250000000000 : ℝ), (20612878552793/50000000000000 : ℝ), (22721438812631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101438717/5000000000 : ℝ)|^8217 ≤ (833210327951/6250000000000 : ℝ)^6169
        have hw : |(-1101438717/5000000000 : ℝ)|=(1101438717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570714071/5000000000 : ℝ)|^8217 ≤ (20612878552793/50000000000000 : ℝ)^6169
        have hw : |(2570714071/5000000000 : ℝ)|=(2570714071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138286199/250000000 : ℝ)|^8217 ≤ (22721438812631/50000000000000 : ℝ)^6169
        have hw : |(138286199/250000000 : ℝ)|=(138286199/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1024_s2_5 (p : ℝ) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5279379423/10000000000 : ℝ)*x 0 + (-403324821/2000000000 : ℝ)*x 1 + (2765724003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279379423/10000000000 : ℝ)^8217 ≤ (2669102573657/6250000000000 : ℝ)^6169 := by
    have hnat : (5279379423 : ℕ)^8217*6250000000000^6169 ≤ 2669102573657^6169*10000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279379423 10000000000 2669102573657 6250000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403324821/2000000000 : ℝ)^8217 ≤ (5925740337239/50000000000000 : ℝ)^6169 := by
    have hnat : (403324821 : ℕ)^8217*50000000000000^6169 ≤ 5925740337239^6169*2000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403324821 2000000000 5925740337239 50000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2765724003/5000000000 : ℝ)^8217 ≤ (45442878128627/100000000000000 : ℝ)^6169 := by
    have hnat : (2765724003 : ℕ)^8217*100000000000000^6169 ≤ 45442878128627^6169*5000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2765724003 5000000000 45442878128627 100000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8217/2048 : ℝ)) 8217 6169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279379423/10000000000 : ℝ), (-403324821/2000000000 : ℝ), (2765724003/5000000000 : ℝ)] ![(2669102573657/6250000000000 : ℝ), (5925740337239/50000000000000 : ℝ), (45442878128627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279379423/10000000000 : ℝ)|^8217 ≤ (2669102573657/6250000000000 : ℝ)^6169
        have hw : |(5279379423/10000000000 : ℝ)|=(5279379423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-403324821/2000000000 : ℝ)|^8217 ≤ (5925740337239/50000000000000 : ℝ)^6169
        have hw : |(-403324821/2000000000 : ℝ)|=(403324821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2765724003/5000000000 : ℝ)|^8217 ≤ (45442878128627/100000000000000 : ℝ)^6169
        have hw : |(2765724003/5000000000 : ℝ)|=(2765724003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1024_s2_6 (p : ℝ) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (13198449/25000000 : ℝ)*x 0 + (1382861967/2500000000 : ℝ)*x 1 + (-403324811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13198449/25000000 : ℝ)^8217 ≤ (8541128617123/20000000000000 : ℝ)^6169 := by
    have hnat : (13198449 : ℕ)^8217*20000000000000^6169 ≤ 8541128617123^6169*25000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13198449 25000000 8541128617123 20000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382861967/2500000000 : ℝ)^8217 ≤ (45442876618531/100000000000000 : ℝ)^6169 := by
    have hnat : (1382861967 : ℕ)^8217*100000000000000^6169 ≤ 45442876618531^6169*2500000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382861967 2500000000 45442876618531 100000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403324811/2000000000 : ℝ)^8217 ≤ (5925740141541/50000000000000 : ℝ)^6169 := by
    have hnat : (403324811 : ℕ)^8217*50000000000000^6169 ≤ 5925740141541^6169*2000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403324811 2000000000 5925740141541 50000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8217/2048 : ℝ)) 8217 6169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13198449/25000000 : ℝ), (1382861967/2500000000 : ℝ), (-403324811/2000000000 : ℝ)] ![(8541128617123/20000000000000 : ℝ), (45442876618531/100000000000000 : ℝ), (5925740141541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13198449/25000000 : ℝ)|^8217 ≤ (8541128617123/20000000000000 : ℝ)^6169
        have hw : |(13198449/25000000 : ℝ)|=(13198449/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1382861967/2500000000 : ℝ)|^8217 ≤ (45442876618531/100000000000000 : ℝ)^6169
        have hw : |(1382861967/2500000000 : ℝ)|=(1382861967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403324811/2000000000 : ℝ)|^8217 ≤ (5925740141541/50000000000000 : ℝ)^6169
        have hw : |(-403324811/2000000000 : ℝ)|=(403324811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1024_s2_7 (p : ℝ) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184136283/5000000000 : ℝ)*x 0 + (47642993/100000000 : ℝ)*x 1 + (4006282737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184136283/5000000000 : ℝ)^8217 ≤ (33181717094009/100000000000000 : ℝ)^6169 := by
    have hnat : (2184136283 : ℕ)^8217*100000000000000^6169 ≤ 33181717094009^6169*5000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184136283 5000000000 33181717094009 100000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47642993/100000000 : ℝ)^8217 ≤ (7449555323097/20000000000000 : ℝ)^6169 := by
    have hnat : (47642993 : ℕ)^8217*20000000000000^6169 ≤ 7449555323097^6169*100000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47642993 100000000 7449555323097 20000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4006282737/10000000000 : ℝ)^8217 ≤ (1182820251219/4000000000000 : ℝ)^6169 := by
    have hnat : (4006282737 : ℕ)^8217*4000000000000^6169 ≤ 1182820251219^6169*10000000000^8217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006282737 10000000000 1182820251219 4000000000000 8217 6169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8217/2048 : ℝ)) 8217 6169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184136283/5000000000 : ℝ), (47642993/100000000 : ℝ), (4006282737/10000000000 : ℝ)] ![(33181717094009/100000000000000 : ℝ), (7449555323097/20000000000000 : ℝ), (1182820251219/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184136283/5000000000 : ℝ)|^8217 ≤ (33181717094009/100000000000000 : ℝ)^6169
        have hw : |(2184136283/5000000000 : ℝ)|=(2184136283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47642993/100000000 : ℝ)|^8217 ≤ (7449555323097/20000000000000 : ℝ)^6169
        have hw : |(47642993/100000000 : ℝ)|=(47642993/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4006282737/10000000000 : ℝ)|^8217 ≤ (1182820251219/4000000000000 : ℝ)^6169
        have hw : |(4006282737/10000000000 : ℝ)|=(4006282737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1024_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147176677/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2127/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27/160 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4979/100000 : ℝ) ^ (1027/256 : ℝ) ≤ (296667958961869/50000000000000000000 : ℝ) := by
    have hpowers : (4979/100000 : ℝ)^1027 ≤ (296667958961869/50000000000000000000 : ℝ)^256 := by
      have hnat : (4979 : ℕ)^1027*50000000000000000000^256 ≤ 296667958961869^256*100000^1027 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4979 100000 296667958961869 50000000000000000000 1027 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4979/100000 : ℝ)) (X := (296667958961869/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1027 256 (by norm_num) hpowers
    exact h
  have hpowhi : (20981/100000 : ℝ) ^ (1027/256 : ℝ) ≤ (95132167091782757/50000000000000000000 : ℝ) := by
    have hpowers : (20981/100000 : ℝ)^1027 ≤ (95132167091782757/50000000000000000000 : ℝ)^256 := by
      have hnat : (20981 : ℕ)^1027*50000000000000000000^256 ≤ 95132167091782757^256*100000^1027 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20981 100000 95132167091782757 50000000000000000000 1027 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20981/100000 : ℝ)) (X := (95132167091782757/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1027 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000296667958961869/25000000000000000000 : ℝ) ≤ (39062615546889/39062500000000 : ℝ) ^ (1027/256 : ℝ) := by
    have hpowers : (25000296667958961869/25000000000000000000 : ℝ)^256 ≤ (39062615546889/39062500000000 : ℝ)^1027 := by
      have hnat : (25000296667958961869 : ℕ)^256*39062500000000^1027 ≤ 39062615546889^1027*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000296667958961869 25000000000000000000 39062615546889 39062500000000 256 1027 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39062615546889/39062500000000 : ℝ)) (X := (25000296667958961869/25000000000000000000 : ℝ)) (by norm_num) 1027 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25047714417525372313/25000000000000000000 : ℝ) ≤ (2000950819841237/2000000000000000 : ℝ) ^ (1027/256 : ℝ) := by
    have hpowers : (25047714417525372313/25000000000000000000 : ℝ)^256 ≤ (2000950819841237/2000000000000000 : ℝ)^1027 := by
      have hnat : (25047714417525372313 : ℕ)^256*2000000000000000^1027 ≤ 2000950819841237^1027*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25047714417525372313 25000000000000000000 2000950819841237 2000000000000000 256 1027 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000950819841237/2000000000000000 : ℝ)) (X := (25047714417525372313/25000000000000000000 : ℝ)) (by norm_num) 1027 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25095132167091782757/25000000000000000000 : ℝ) ≤ (5004739309204393/5000000000000000 : ℝ) ^ (1027/256 : ℝ) := by
    have hpowers : (25095132167091782757/25000000000000000000 : ℝ)^256 ≤ (5004739309204393/5000000000000000 : ℝ)^1027 := by
      have hnat : (25095132167091782757 : ℕ)^256*5000000000000000^1027 ≤ 5004739309204393^1027*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25095132167091782757 25000000000000000000 5004739309204393 5000000000000000 256 1027 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004739309204393/5000000000000000 : ℝ)) (X := (25095132167091782757/25000000000000000000 : ℝ)) (by norm_num) 1027 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(296667958961869/50000000000000000000 : ℝ) ≤ ((15997342657699785041/16002000000000000000 : ℝ)+2*(4724519202601/1600200000000000 : ℝ)*(4979/100000 : ℝ))^(1027/256 : ℝ) := by
    rw [show (15997342657699785041/16002000000000000000 : ℝ)+2*(4724519202601/1600200000000000 : ℝ)*(4979/100000 : ℝ)=(39062615546889/39062500000000 : ℝ) by norm_num, show 1+2*(296667958961869/50000000000000000000 : ℝ)=(25000296667958961869/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(95132167091782757/50000000000000000000 : ℝ)+(296667958961869/50000000000000000000 : ℝ) ≤ ((15997342657699785041/16002000000000000000 : ℝ)+(4724519202601/1600200000000000 : ℝ)*((20981/100000 : ℝ)+(4979/100000 : ℝ)))^(1027/256 : ℝ) := by
    rw [show (15997342657699785041/16002000000000000000 : ℝ)+(4724519202601/1600200000000000 : ℝ)*((20981/100000 : ℝ)+(4979/100000 : ℝ))=(2000950819841237/2000000000000000 : ℝ) by norm_num, show 1+(95132167091782757/50000000000000000000 : ℝ)+(296667958961869/50000000000000000000 : ℝ)=(25047714417525372313/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(95132167091782757/50000000000000000000 : ℝ) ≤ ((15997342657699785041/16002000000000000000 : ℝ)+2*(4724519202601/1600200000000000 : ℝ)*(20981/100000 : ℝ))^(1027/256 : ℝ) := by
    rw [show (15997342657699785041/16002000000000000000 : ℝ)+2*(4724519202601/1600200000000000 : ℝ)*(20981/100000 : ℝ)=(5004739309204393/5000000000000000 : ℝ) by norm_num, show 1+2*(95132167091782757/50000000000000000000 : ℝ)=(25095132167091782757/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15997342657699785041/16002000000000000000 : ℝ)*(X 1 0+X 2 0)+(4724519202601/1600200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1027/256 : ℝ)) (lo := (4979/100000 : ℝ)) (hi := (20981/100000 : ℝ)) (c := (15997342657699785041/16002000000000000000 : ℝ)) (alpha := (4724519202601/1600200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15997342657699785041/16002000000000000000 : ℝ)*(X 0 1+X 2 1)+(4724519202601/1600200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1027/256 : ℝ)) (lo := (4979/100000 : ℝ)) (hi := (20981/100000 : ℝ)) (c := (15997342657699785041/16002000000000000000 : ℝ)) (alpha := (4724519202601/1600200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15997342657699785041/16002000000000000000 : ℝ)*(X 0 2+X 1 2)+(4724519202601/1600200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1027/256 : ℝ)) (lo := (4979/100000 : ℝ)) (hi := (20981/100000 : ℝ)) (c := (15997342657699785041/16002000000000000000 : ℝ)) (alpha := (4724519202601/1600200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2202736809/10000000000 : ℝ)*X 0 0+(5534442037/10000000000 : ℝ)*X 0 1+(2569233037/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1024_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075805379/2000000000 : ℝ)*X 1 0+(-120480223/500000000 : ℝ)*X 1 1+(2569233947/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1024_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1075805583/2000000000 : ℝ)*X 2 0+(2569233217/5000000000 : ℝ)*X 2 1+(-2409605007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1024_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873599463/2000000000 : ℝ)*X 0 0+(2000231489/5000000000 : ℝ)*X 0 1+(4770058657/10000000000 : ℝ)*X 0 2+(873599463/2000000000 : ℝ)*X 1 0+(2000231489/5000000000 : ℝ)*X 1 1+(4770058657/10000000000 : ℝ)*X 1 2+(873599463/2000000000 : ℝ)*X 2 0+(2000231489/5000000000 : ℝ)*X 2 1+(4770058657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1024_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1101438717/5000000000 : ℝ)*X 0 0+(2570714071/5000000000 : ℝ)*X 0 1+(138286199/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1024_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279379423/10000000000 : ℝ)*X 1 0+(-403324821/2000000000 : ℝ)*X 1 1+(2765724003/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1024_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((13198449/25000000 : ℝ)*X 2 0+(1382861967/2500000000 : ℝ)*X 2 1+(-403324811/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1024_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184136283/5000000000 : ℝ)*X 0 0+(47642993/100000000 : ℝ)*X 0 1+(4006282737/10000000000 : ℝ)*X 0 2+(2184136283/5000000000 : ℝ)*X 1 0+(47642993/100000000 : ℝ)*X 1 1+(4006282737/10000000000 : ℝ)*X 1 2+(2184136283/5000000000 : ℝ)*X 2 0+(47642993/100000000 : ℝ)*X 2 1+(4006282737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1024_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73279465654169003331805617/11112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (650215831/100000000000000 : ℝ)*(base19) + (643113469/50000000000000 : ℝ)*(base23) + (19055949/12500000000000 : ℝ)*(upper2) + (1228661/1562500000000 : ℝ)*(upper3) + (67930409/100000000000000 : ℝ)*(upper4) + (478106132520411/25000000000000 : ℝ)*(major0) + (478106132520411/25000000000000 : ℝ)*(major1) + (478106132520411/25000000000000 : ℝ)*(major2) + (2525423770864109/100000000000000 : ℝ)*(sp0) + (1262720429696867/50000000000000 : ℝ)*(sp1) + (631360055845657/25000000000000 : ℝ)*(sp2) + (324848689796671/25000000000000 : ℝ)*(sp3) + (1108671591/6250000000000 : ℝ)*(sp4) + (1257155611/10000000000000 : ℝ)*(sp7) + (259881466148559/20000000000000 : ℝ)*(f.failure) + (505088301921913/20000000000000 : ℝ)*(f.sum) + (2560992739983/4445000000000000000000000000 : ℝ)*base65 + (65887016300196461/44450000000000000000000000000000 : ℝ)*base68 + (322168982964346461/44450000000000000000000000000000 : ℝ)*base70 + (37102437416953539/44450000000000000000000000000000 : ℝ)*base71 + (6260783990359/2222500000000000000000000000 : ℝ)*base73 + (373400647010846461/44450000000000000000000000000000 : ℝ)*base76 + (547752202053546461/44450000000000000000000000000000 : ℝ)*base78 + (243666381143346461/44450000000000000000000000000000 : ℝ)*base80 + (539411434749/138906250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (21958443/2000000000000000000000 : ℝ)*base89 + (21958443/2000000000000000000000 : ℝ)*base91 + (21958443/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (139993318788627893156153783/66675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66248293/20000000000000 : ℝ)*(base19) + (10734609/2500000000000 : ℝ)*(base23) + (718273/50000000000000 : ℝ)*(upper2) + (28530677/50000000000000 : ℝ)*(upper3) + (7352681/12500000000000 : ℝ)*(upper5) + (970801303046737/50000000000000 : ℝ)*(major0) + (970801303046737/50000000000000 : ℝ)*(major1) + (970801303046737/50000000000000 : ℝ)*(major2) + (326829169/12500000000000 : ℝ)*(sp1) + (3115824367/100000000000000 : ℝ)*(sp2) + (2563972607757811/100000000000000 : ℝ)*(sp4) + (1281984830941497/50000000000000 : ℝ)*(sp5) + (640992265637271/25000000000000 : ℝ)*(sp6) + (164904066805153/12500000000000 : ℝ)*(sp7) + (164904066805153/12500000000000 : ℝ)*(f.failure) + (2563972607757811/100000000000000 : ℝ)*(f.sum) + (52193374943887/40005000000000000000000000000 : ℝ)*base65 + (623813974243456261/266700000000000000000000000000000 : ℝ)*base68 + (700750165980343739/266700000000000000000000000000000 : ℝ)*base69 + (1118314451525743739/266700000000000000000000000000000 : ℝ)*base71 + (108262643551613/40005000000000000000000000000 : ℝ)*base74 + (335319134943943739/266700000000000000000000000000000 : ℝ)*base75 + (1259863688835643739/266700000000000000000000000000000 : ℝ)*base77 + (333576877188943739/266700000000000000000000000000000 : ℝ)*base79 + (10596000320779/20002500000000000000000000000 : ℝ)*base82 + (16581/1250000000000000000000 : ℝ)*base89 + (16581/1250000000000000000000 : ℝ)*base91 + (16581/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1024_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147176677/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2127/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27/160 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1024_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147176677/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2127/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27/160 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1024_s2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
