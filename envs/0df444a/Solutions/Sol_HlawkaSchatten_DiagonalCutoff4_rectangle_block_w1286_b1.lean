-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1286_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:26.089199+00:00
-- url     : https://prove2.me/submissions/a22e767c-b2e8-4a65-8ec5-647819f99e57

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
theorem support_rectangle_w1286_s3_0 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2090920963/10000000000 : ℝ)*x 0 + (5434981269/10000000000 : ℝ)*x 1 + (1044985897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090920963/10000000000 : ℝ)^2123 ≤ (12715419760953/100000000000000 : ℝ)^1611 := by
    have hnat : (2090920963 : ℕ)^2123*100000000000000^1611 ≤ 12715419760953^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090920963 10000000000 12715419760953 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434981269/10000000000 : ℝ)^2123 ≤ (559693196469/1250000000000 : ℝ)^1611 := by
    have hnat : (5434981269 : ℕ)^2123*1250000000000^1611 ≤ 559693196469^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434981269 10000000000 559693196469 1250000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044985897/2000000000 : ℝ)^2123 ≤ (8501824900329/20000000000000 : ℝ)^1611 := by
    have hnat : (1044985897 : ℕ)^2123*20000000000000^1611 ≤ 8501824900329^1611*2000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044985897 2000000000 8501824900329 20000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2090920963/10000000000 : ℝ), (5434981269/10000000000 : ℝ), (1044985897/2000000000 : ℝ)] ![(12715419760953/100000000000000 : ℝ), (559693196469/1250000000000 : ℝ), (8501824900329/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2090920963/10000000000 : ℝ)|^2123 ≤ (12715419760953/100000000000000 : ℝ)^1611
        have hw : |(-2090920963/10000000000 : ℝ)|=(2090920963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434981269/10000000000 : ℝ)|^2123 ≤ (559693196469/1250000000000 : ℝ)^1611
        have hw : |(5434981269/10000000000 : ℝ)|=(5434981269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044985897/2000000000 : ℝ)|^2123 ≤ (8501824900329/20000000000000 : ℝ)^1611
        have hw : |(1044985897/2000000000 : ℝ)|=(1044985897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s3_1 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338695757/2500000000 : ℝ)*x 0 + (-2198442689/10000000000 : ℝ)*x 1 + (1044985911/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338695757/2500000000 : ℝ)^2123 ≤ (4390681882413/10000000000000 : ℝ)^1611 := by
    have hnat : (1338695757 : ℕ)^2123*10000000000000^1611 ≤ 4390681882413^1611*2500000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338695757 2500000000 4390681882413 10000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198442689/10000000000 : ℝ)^2123 ≤ (1358405590243/10000000000000 : ℝ)^1611 := by
    have hnat : (2198442689 : ℕ)^2123*10000000000000^1611 ≤ 1358405590243^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198442689 10000000000 1358405590243 10000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044985911/2000000000 : ℝ)^2123 ≤ (42509125252151/100000000000000 : ℝ)^1611 := by
    have hnat : (1044985911 : ℕ)^2123*100000000000000^1611 ≤ 42509125252151^1611*2000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044985911 2000000000 42509125252151 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338695757/2500000000 : ℝ), (-2198442689/10000000000 : ℝ), (1044985911/2000000000 : ℝ)] ![(4390681882413/10000000000000 : ℝ), (1358405590243/10000000000000 : ℝ), (42509125252151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338695757/2500000000 : ℝ)|^2123 ≤ (4390681882413/10000000000000 : ℝ)^1611
        have hw : |(1338695757/2500000000 : ℝ)|=(1338695757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198442689/10000000000 : ℝ)|^2123 ≤ (1358405590243/10000000000000 : ℝ)^1611
        have hw : |(-2198442689/10000000000 : ℝ)|=(2198442689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044985911/2000000000 : ℝ)|^2123 ≤ (42509125252151/100000000000000 : ℝ)^1611
        have hw : |(1044985911/2000000000 : ℝ)|=(1044985911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s3_2 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53547831/100000000 : ℝ)*x 0 + (2612464603/5000000000 : ℝ)*x 1 + (-1099221527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53547831/100000000 : ℝ)^2123 ≤ (21953409801063/50000000000000 : ℝ)^1611 := by
    have hnat : (53547831 : ℕ)^2123*50000000000000^1611 ≤ 21953409801063^1611*100000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53547831 100000000 21953409801063 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612464603/5000000000 : ℝ)^2123 ≤ (21254560755171/50000000000000 : ℝ)^1611 := by
    have hnat : (2612464603 : ℕ)^2123*50000000000000^1611 ≤ 21254560755171^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612464603 5000000000 21254560755171 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099221527/5000000000 : ℝ)^2123 ≤ (6792029437259/50000000000000 : ℝ)^1611 := by
    have hnat : (1099221527 : ℕ)^2123*50000000000000^1611 ≤ 6792029437259^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099221527 5000000000 6792029437259 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53547831/100000000 : ℝ), (2612464603/5000000000 : ℝ), (-1099221527/5000000000 : ℝ)] ![(21953409801063/50000000000000 : ℝ), (21254560755171/50000000000000 : ℝ), (6792029437259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53547831/100000000 : ℝ)|^2123 ≤ (21953409801063/50000000000000 : ℝ)^1611
        have hw : |(53547831/100000000 : ℝ)|=(53547831/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612464603/5000000000 : ℝ)|^2123 ≤ (21254560755171/50000000000000 : ℝ)^1611
        have hw : |(2612464603/5000000000 : ℝ)|=(2612464603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1099221527/5000000000 : ℝ)|^2123 ≤ (6792029437259/50000000000000 : ℝ)^1611
        have hw : |(-1099221527/5000000000 : ℝ)|=(1099221527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s3_3 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4340011073/10000000000 : ℝ)*x 0 + (32263827/78125000 : ℝ)*x 1 + (2280243517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340011073/10000000000 : ℝ)^2123 ≤ (416092601039/1250000000000 : ℝ)^1611 := by
    have hnat : (4340011073 : ℕ)^2123*1250000000000^1611 ≤ 416092601039^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340011073 10000000000 416092601039 1250000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32263827/78125000 : ℝ)^2123 ≤ (31178937799179/100000000000000 : ℝ)^1611 := by
    have hnat : (32263827 : ℕ)^2123*100000000000000^1611 ≤ 31178937799179^1611*78125000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32263827 78125000 31178937799179 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280243517/5000000000 : ℝ)^2123 ≤ (3553365410501/10000000000000 : ℝ)^1611 := by
    have hnat : (2280243517 : ℕ)^2123*10000000000000^1611 ≤ 3553365410501^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280243517 5000000000 3553365410501 10000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340011073/10000000000 : ℝ), (32263827/78125000 : ℝ), (2280243517/5000000000 : ℝ)] ![(416092601039/1250000000000 : ℝ), (31178937799179/100000000000000 : ℝ), (3553365410501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340011073/10000000000 : ℝ)|^2123 ≤ (416092601039/1250000000000 : ℝ)^1611
        have hw : |(4340011073/10000000000 : ℝ)|=(4340011073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32263827/78125000 : ℝ)|^2123 ≤ (31178937799179/100000000000000 : ℝ)^1611
        have hw : |(32263827/78125000 : ℝ)|=(32263827/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2280243517/5000000000 : ℝ)|^2123 ≤ (3553365410501/10000000000000 : ℝ)^1611
        have hw : |(2280243517/5000000000 : ℝ)|=(2280243517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s3_4 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2090943979/10000000000 : ℝ)*x 0 + (5225837949/10000000000 : ℝ)*x 1 + (1358516769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090943979/10000000000 : ℝ)^2123 ≤ (2543120842147/20000000000000 : ℝ)^1611 := by
    have hnat : (2090943979 : ℕ)^2123*20000000000000^1611 ≤ 2543120842147^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090943979 10000000000 2543120842147 20000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225837949/10000000000 : ℝ)^2123 ≤ (42518864881669/100000000000000 : ℝ)^1611 := by
    have hnat : (5225837949 : ℕ)^2123*100000000000000^1611 ≤ 42518864881669^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225837949 10000000000 42518864881669 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358516769/2500000000 : ℝ)^2123 ≤ (22382765448069/50000000000000 : ℝ)^1611 := by
    have hnat : (1358516769 : ℕ)^2123*50000000000000^1611 ≤ 22382765448069^1611*2500000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358516769 2500000000 22382765448069 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2090943979/10000000000 : ℝ), (5225837949/10000000000 : ℝ), (1358516769/2500000000 : ℝ)] ![(2543120842147/20000000000000 : ℝ), (42518864881669/100000000000000 : ℝ), (22382765448069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2090943979/10000000000 : ℝ)|^2123 ≤ (2543120842147/20000000000000 : ℝ)^1611
        have hw : |(-2090943979/10000000000 : ℝ)|=(2090943979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225837949/10000000000 : ℝ)|^2123 ≤ (42518864881669/100000000000000 : ℝ)^1611
        have hw : |(5225837949/10000000000 : ℝ)|=(5225837949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358516769/2500000000 : ℝ)|^2123 ≤ (22382765448069/50000000000000 : ℝ)^1611
        have hw : |(1358516769/2500000000 : ℝ)|=(1358516769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s3_5 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301040897/10000000000 : ℝ)*x 0 + (-1989305009/10000000000 : ℝ)*x 1 + (5434067019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301040897/10000000000 : ℝ)^2123 ≤ (5415879614787/12500000000000 : ℝ)^1611 := by
    have hnat : (5301040897 : ℕ)^2123*12500000000000^1611 ≤ 5415879614787^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301040897 10000000000 5415879614787 12500000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989305009/10000000000 : ℝ)^2123 ≤ (11907432788157/100000000000000 : ℝ)^1611 := by
    have hnat : (1989305009 : ℕ)^2123*100000000000000^1611 ≤ 11907432788157^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989305009 10000000000 11907432788157 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434067019/10000000000 : ℝ)^2123 ≤ (22382765138671/50000000000000 : ℝ)^1611 := by
    have hnat : (5434067019 : ℕ)^2123*50000000000000^1611 ≤ 22382765138671^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434067019 10000000000 22382765138671 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301040897/10000000000 : ℝ), (-1989305009/10000000000 : ℝ), (5434067019/10000000000 : ℝ)] ![(5415879614787/12500000000000 : ℝ), (11907432788157/100000000000000 : ℝ), (22382765138671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301040897/10000000000 : ℝ)|^2123 ≤ (5415879614787/12500000000000 : ℝ)^1611
        have hw : |(5301040897/10000000000 : ℝ)|=(5301040897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989305009/10000000000 : ℝ)|^2123 ≤ (11907432788157/100000000000000 : ℝ)^1611
        have hw : |(-1989305009/10000000000 : ℝ)|=(1989305009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434067019/10000000000 : ℝ)|^2123 ≤ (22382765138671/50000000000000 : ℝ)^1611
        have hw : |(5434067019/10000000000 : ℝ)|=(5434067019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s3_6 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301040913/10000000000 : ℝ)*x 0 + (2717033491/5000000000 : ℝ)*x 1 + (-994652519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301040913/10000000000 : ℝ)^2123 ≤ (4332703709063/10000000000000 : ℝ)^1611 := by
    have hnat : (5301040913 : ℕ)^2123*10000000000000^1611 ≤ 4332703709063^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301040913 10000000000 4332703709063 10000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717033491/5000000000 : ℝ)^2123 ≤ (22382764937833/50000000000000 : ℝ)^1611 := by
    have hnat : (2717033491 : ℕ)^2123*50000000000000^1611 ≤ 22382764937833^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717033491 5000000000 22382764937833 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (994652519/5000000000 : ℝ)^2123 ≤ (11907433016911/100000000000000 : ℝ)^1611 := by
    have hnat : (994652519 : ℕ)^2123*100000000000000^1611 ≤ 11907433016911^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994652519 5000000000 11907433016911 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301040913/10000000000 : ℝ), (2717033491/5000000000 : ℝ), (-994652519/5000000000 : ℝ)] ![(4332703709063/10000000000000 : ℝ), (22382764937833/50000000000000 : ℝ), (11907433016911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301040913/10000000000 : ℝ)|^2123 ≤ (4332703709063/10000000000000 : ℝ)^1611
        have hw : |(5301040913/10000000000 : ℝ)|=(5301040913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717033491/5000000000 : ℝ)|^2123 ≤ (22382764937833/50000000000000 : ℝ)^1611
        have hw : |(2717033491/5000000000 : ℝ)|=(2717033491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-994652519/5000000000 : ℝ)|^2123 ≤ (11907433016911/100000000000000 : ℝ)^1611
        have hw : |(-994652519/5000000000 : ℝ)|=(994652519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s3_7 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4340057931/10000000000 : ℝ)*x 0 + (2279311969/5000000000 : ℝ)*x 1 + (4131644767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340057931/10000000000 : ℝ)^2123 ≤ (33287881701/100000000000 : ℝ)^1611 := by
    have hnat : (4340057931 : ℕ)^2123*100000000000^1611 ≤ 33287881701^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340057931 10000000000 33287881701 100000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279311969/5000000000 : ℝ)^2123 ≤ (35514525198921/100000000000000 : ℝ)^1611 := by
    have hnat : (2279311969 : ℕ)^2123*100000000000000^1611 ≤ 35514525198921^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279311969 5000000000 35514525198921 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131644767/10000000000 : ℝ)^2123 ≤ (31197593084847/100000000000000 : ℝ)^1611 := by
    have hnat : (4131644767 : ℕ)^2123*100000000000000^1611 ≤ 31197593084847^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131644767 10000000000 31197593084847 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340057931/10000000000 : ℝ), (2279311969/5000000000 : ℝ), (4131644767/10000000000 : ℝ)] ![(33287881701/100000000000 : ℝ), (35514525198921/100000000000000 : ℝ), (31197593084847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340057931/10000000000 : ℝ)|^2123 ≤ (33287881701/100000000000 : ℝ)^1611
        have hw : |(4340057931/10000000000 : ℝ)|=(4340057931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2279311969/5000000000 : ℝ)|^2123 ≤ (35514525198921/100000000000000 : ℝ)^1611
        have hw : |(2279311969/5000000000 : ℝ)|=(2279311969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131644767/10000000000 : ℝ)|^2123 ≤ (31197593084847/100000000000000 : ℝ)^1611
        have hw : |(4131644767/10000000000 : ℝ)|=(4131644767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1286_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152526313/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3269/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (473/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10631/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7537/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3269/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (473/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3269/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (473/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3269/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (473/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3269/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (473/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3269/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (473/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3269/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (473/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (473/5000 : ℝ) ^ (4245/1024 : ℝ) ≤ (1136524234488729/20000000000000000000 : ℝ) := by
    have hpowers : (473/5000 : ℝ)^4245 ≤ (1136524234488729/20000000000000000000 : ℝ)^1024 := by
      have hnat : (473 : ℕ)^4245*20000000000000000000^1024 ≤ 1136524234488729^1024*5000^4245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        473 5000 1136524234488729 20000000000000000000 4245 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (473/5000 : ℝ)) (X := (1136524234488729/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3269/20000 : ℝ) ^ (4245/1024 : ℝ) ≤ (27418965502308723/50000000000000000000 : ℝ) := by
    have hpowers : (3269/20000 : ℝ)^4245 ≤ (27418965502308723/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3269 : ℕ)^4245*50000000000000000000^1024 ≤ 27418965502308723^1024*20000^4245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3269 20000 27418965502308723 50000000000000000000 4245 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3269/20000 : ℝ)) (X := (27418965502308723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001136524234488729/10000000000000000000 : ℝ) ≤ (2000054829240911/2000000000000000 : ℝ) ^ (4245/1024 : ℝ) := by
    have hpowers : (10001136524234488729/10000000000000000000 : ℝ)^1024 ≤ (2000054829240911/2000000000000000 : ℝ)^4245 := by
      have hnat : (10001136524234488729 : ℕ)^1024*2000000000000000^4245 ≤ 2000054829240911^4245*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001136524234488729 10000000000000000000 2000054829240911 2000000000000000 1024 4245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000054829240911/2000000000000000 : ℝ)) (X := (10001136524234488729/10000000000000000000 : ℝ)) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060520552177061091/100000000000000000000 : ℝ) ≤ (5000729785877561/5000000000000000 : ℝ) ^ (4245/1024 : ℝ) := by
    have hpowers : (100060520552177061091/100000000000000000000 : ℝ)^1024 ≤ (5000729785877561/5000000000000000 : ℝ)^4245 := by
      have hnat : (100060520552177061091 : ℕ)^1024*5000000000000000^4245 ≤ 5000729785877561^4245*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060520552177061091 100000000000000000000 5000729785877561 5000000000000000 1024 4245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000729785877561/5000000000000000 : ℝ)) (X := (100060520552177061091/100000000000000000000 : ℝ)) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25027418965502308723/25000000000000000000 : ℝ) ≤ (10002644997305689/10000000000000000 : ℝ) ^ (4245/1024 : ℝ) := by
    have hpowers : (25027418965502308723/25000000000000000000 : ℝ)^1024 ≤ (10002644997305689/10000000000000000 : ℝ)^4245 := by
      have hnat : (25027418965502308723 : ℕ)^1024*10000000000000000^4245 ≤ 10002644997305689^4245*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25027418965502308723 25000000000000000000 10002644997305689 10000000000000000 1024 4245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002644997305689/10000000000000000 : ℝ)) (X := (25027418965502308723/25000000000000000000 : ℝ)) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1136524234488729/20000000000000000000 : ℝ) ≤ ((509847846260752841/510000000000000000 : ℝ)+2*(43904650021/25500000000000 : ℝ)*(473/5000 : ℝ))^(4245/1024 : ℝ) := by
    rw [show (509847846260752841/510000000000000000 : ℝ)+2*(43904650021/25500000000000 : ℝ)*(473/5000 : ℝ)=(2000054829240911/2000000000000000 : ℝ) by norm_num, show 1+2*(1136524234488729/20000000000000000000 : ℝ)=(10001136524234488729/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27418965502308723/50000000000000000000 : ℝ)+(1136524234488729/20000000000000000000 : ℝ) ≤ ((509847846260752841/510000000000000000 : ℝ)+(43904650021/25500000000000 : ℝ)*((3269/20000 : ℝ)+(473/5000 : ℝ)))^(4245/1024 : ℝ) := by
    rw [show (509847846260752841/510000000000000000 : ℝ)+(43904650021/25500000000000 : ℝ)*((3269/20000 : ℝ)+(473/5000 : ℝ))=(5000729785877561/5000000000000000 : ℝ) by norm_num, show 1+(27418965502308723/50000000000000000000 : ℝ)+(1136524234488729/20000000000000000000 : ℝ)=(100060520552177061091/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27418965502308723/50000000000000000000 : ℝ) ≤ ((509847846260752841/510000000000000000 : ℝ)+2*(43904650021/25500000000000 : ℝ)*(3269/20000 : ℝ))^(4245/1024 : ℝ) := by
    rw [show (509847846260752841/510000000000000000 : ℝ)+2*(43904650021/25500000000000 : ℝ)*(3269/20000 : ℝ)=(10002644997305689/10000000000000000 : ℝ) by norm_num, show 1+2*(27418965502308723/50000000000000000000 : ℝ)=(25027418965502308723/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (509847846260752841/510000000000000000 : ℝ)*(X 1 0+X 2 0)+(43904650021/25500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4245/1024 : ℝ)) (lo := (473/5000 : ℝ)) (hi := (3269/20000 : ℝ)) (c := (509847846260752841/510000000000000000 : ℝ)) (alpha := (43904650021/25500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (509847846260752841/510000000000000000 : ℝ)*(X 0 1+X 2 1)+(43904650021/25500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4245/1024 : ℝ)) (lo := (473/5000 : ℝ)) (hi := (3269/20000 : ℝ)) (c := (509847846260752841/510000000000000000 : ℝ)) (alpha := (43904650021/25500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (509847846260752841/510000000000000000 : ℝ)*(X 0 2+X 1 2)+(43904650021/25500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4245/1024 : ℝ)) (lo := (473/5000 : ℝ)) (hi := (3269/20000 : ℝ)) (c := (509847846260752841/510000000000000000 : ℝ)) (alpha := (43904650021/25500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2090920963/10000000000 : ℝ)*X 0 0+(5434981269/10000000000 : ℝ)*X 0 1+(1044985897/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338695757/2500000000 : ℝ)*X 1 0+(-2198442689/10000000000 : ℝ)*X 1 1+(1044985911/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53547831/100000000 : ℝ)*X 2 0+(2612464603/5000000000 : ℝ)*X 2 1+(-1099221527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4340011073/10000000000 : ℝ)*X 0 0+(32263827/78125000 : ℝ)*X 0 1+(2280243517/5000000000 : ℝ)*X 0 2+(4340011073/10000000000 : ℝ)*X 1 0+(32263827/78125000 : ℝ)*X 1 1+(2280243517/5000000000 : ℝ)*X 1 2+(4340011073/10000000000 : ℝ)*X 2 0+(32263827/78125000 : ℝ)*X 2 1+(2280243517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2090943979/10000000000 : ℝ)*X 0 0+(5225837949/10000000000 : ℝ)*X 0 1+(1358516769/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301040897/10000000000 : ℝ)*X 1 0+(-1989305009/10000000000 : ℝ)*X 1 1+(5434067019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301040913/10000000000 : ℝ)*X 2 0+(2717033491/5000000000 : ℝ)*X 2 1+(-994652519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4340057931/10000000000 : ℝ)*X 0 0+(2279311969/5000000000 : ℝ)*X 0 1+(4131644767/10000000000 : ℝ)*X 0 2+(4340057931/10000000000 : ℝ)*X 1 0+(2279311969/5000000000 : ℝ)*X 1 1+(4131644767/10000000000 : ℝ)*X 1 2+(4340057931/10000000000 : ℝ)*X 2 0+(2279311969/5000000000 : ℝ)*X 2 1+(4131644767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9464924310121045802237407/1700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1001340173/100000000000000 : ℝ)*(base19) + (225670591/20000000000000 : ℝ)*(base23) + (33307033/100000000000000 : ℝ)*(lower2) + (304269913/100000000000000 : ℝ)*(upper3) + (67042157/100000000000000 : ℝ)*(lower4) + (708248621618727/20000000000000 : ℝ)*(major0) + (708248621618727/20000000000000 : ℝ)*(major1) + (885310777023409/25000000000000 : ℝ)*(major2) + (595093761922427/12500000000000 : ℝ)*(sp0) + (297547437594183/6250000000000 : ℝ)*(sp1) + (2380379437247073/50000000000000 : ℝ)*(sp2) + (2321715689577697/100000000000000 : ℝ)*(sp3) + (2476866921/25000000000000 : ℝ)*(sp4) + (2067635143/20000000000000 : ℝ)*(sp7) + (580431506938353/25000000000000 : ℝ)*(f.failure) + (47607600028471/1000000000000 : ℝ)*(f.sum) + (4561158712591/2550000000000000000000000000 : ℝ)*base65 + (20171047934922593/10200000000000000000000000000000 : ℝ)*base68 + (185472271702679969/12750000000000000000000000000000 : ℝ)*base69 + (88044257256522593/10200000000000000000000000000000 : ℝ)*base72 + (447310587809/2550000000000000000000000000 : ℝ)*base74 + (25739183071320031/12750000000000000000000000000000 : ℝ)*base76 + (356015589415557/200000000000000000000000000000 : ℝ)*base77 + (2591940056984443/200000000000000000000000000000 : ℝ)*base80 + (9449330661/2500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (26382489/2500000000000000000000 : ℝ)*base89 + (26382489/2500000000000000000000 : ℝ)*base91 + (1382489/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28934985894759680507246901/8500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1064377851/100000000000000 : ℝ)*(base19) + (541073621/50000000000000 : ℝ)*(base23) + (22706001/25000000000000 : ℝ)*(upper3) + (1719237/25000000000000 : ℝ)*(lower4) + (11391311/10000000000000 : ℝ)*(upper5) + (3572218571940339/100000000000000 : ℝ)*(major0) + (3572218571940339/100000000000000 : ℝ)*(major1) + (3572218571940339/100000000000000 : ℝ)*(major2) + (8793022719/50000000000000 : ℝ)*(sp1) + (16629392303/100000000000000 : ℝ)*(sp2) + (2401201363580767/50000000000000 : ℝ)*(sp4) + (960476815347649/20000000000000 : ℝ)*(sp5) + (4802385015621989/100000000000000 : ℝ)*(sp6) + (2342034303248607/100000000000000 : ℝ)*(sp7) + (2342034303248607/100000000000000 : ℝ)*(f.failure) + (2401201363580767/50000000000000 : ℝ)*(f.sum) + (652822004151/212500000000000000000000000 : ℝ)*base66 + (36850642495711033/17000000000000000000000000000000 : ℝ)*base67 + (8970030138711033/17000000000000000000000000000000 : ℝ)*base69 + (66775849742288967/17000000000000000000000000000000 : ℝ)*base72 + (1114172010649/212500000000000000000000000 : ℝ)*base73 + (111199408401711033/17000000000000000000000000000000 : ℝ)*base75 + (85243535381711033/17000000000000000000000000000000 : ℝ)*base77 + (118939309954288967/17000000000000000000000000000000 : ℝ)*base80 + (264950402063/106250000000000000000000000 : ℝ)*base82 + (48095991/10000000000000000000000 : ℝ)*base89 + (48095991/10000000000000000000000 : ℝ)*base91 + (48095991/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1286_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152526313/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3269/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (473/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10631/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7537/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1286_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1286_s4_0 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-261613247/1250000000 : ℝ)*x 0 + (1083879209/2000000000 : ℝ)*x 1 + (654901727/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261613247/1250000000 : ℝ)^2123 ≤ (6365664994269/50000000000000 : ℝ)^1611 := by
    have hnat : (261613247 : ℕ)^2123*50000000000000^1611 ≤ 6365664994269^1611*1250000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261613247 1250000000 6365664994269 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083879209/2000000000 : ℝ)^2123 ≤ (44606329322457/100000000000000 : ℝ)^1611 := by
    have hnat : (1083879209 : ℕ)^2123*100000000000000^1611 ≤ 44606329322457^1611*2000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083879209 2000000000 44606329322457 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654901727/1250000000 : ℝ)^2123 ≤ (42662340671003/100000000000000 : ℝ)^1611 := by
    have hnat : (654901727 : ℕ)^2123*100000000000000^1611 ≤ 42662340671003^1611*1250000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654901727 1250000000 42662340671003 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261613247/1250000000 : ℝ), (1083879209/2000000000 : ℝ), (654901727/1250000000 : ℝ)] ![(6365664994269/50000000000000 : ℝ), (44606329322457/100000000000000 : ℝ), (42662340671003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261613247/1250000000 : ℝ)|^2123 ≤ (6365664994269/50000000000000 : ℝ)^1611
        have hw : |(-261613247/1250000000 : ℝ)|=(261613247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083879209/2000000000 : ℝ)|^2123 ≤ (44606329322457/100000000000000 : ℝ)^1611
        have hw : |(1083879209/2000000000 : ℝ)|=(1083879209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654901727/1250000000 : ℝ)|^2123 ≤ (42662340671003/100000000000000 : ℝ)^1611
        have hw : |(654901727/1250000000 : ℝ)|=(654901727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s4_1 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337712041/2500000000 : ℝ)*x 0 + (-546208521/2500000000 : ℝ)*x 1 + (654901721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337712041/2500000000 : ℝ)^2123 ≤ (43864305648171/100000000000000 : ℝ)^1611 := by
    have hnat : (1337712041 : ℕ)^2123*100000000000000^1611 ≤ 43864305648171^1611*2500000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337712041 2500000000 43864305648171 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546208521/2500000000 : ℝ)^2123 ≤ (6736677091789/50000000000000 : ℝ)^1611 := by
    have hnat : (546208521 : ℕ)^2123*50000000000000^1611 ≤ 6736677091789^1611*2500000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546208521 2500000000 6736677091789 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654901721/1250000000 : ℝ)^2123 ≤ (10665585038981/25000000000000 : ℝ)^1611 := by
    have hnat : (654901721 : ℕ)^2123*25000000000000^1611 ≤ 10665585038981^1611*1250000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654901721 1250000000 10665585038981 25000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337712041/2500000000 : ℝ), (-546208521/2500000000 : ℝ), (654901721/1250000000 : ℝ)] ![(43864305648171/100000000000000 : ℝ), (6736677091789/50000000000000 : ℝ), (10665585038981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337712041/2500000000 : ℝ)|^2123 ≤ (43864305648171/100000000000000 : ℝ)^1611
        have hw : |(1337712041/2500000000 : ℝ)|=(1337712041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-546208521/2500000000 : ℝ)|^2123 ≤ (6736677091789/50000000000000 : ℝ)^1611
        have hw : |(-546208521/2500000000 : ℝ)|=(546208521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654901721/1250000000 : ℝ)|^2123 ≤ (10665585038981/25000000000000 : ℝ)^1611
        have hw : |(654901721/1250000000 : ℝ)|=(654901721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s4_2 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350848197/10000000000 : ℝ)*x 0 + (1309803423/2500000000 : ℝ)*x 1 + (-109241707/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350848197/10000000000 : ℝ)^2123 ≤ (43864306004669/100000000000000 : ℝ)^1611 := by
    have hnat : (5350848197 : ℕ)^2123*100000000000000^1611 ≤ 43864306004669^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350848197 10000000000 43864306004669 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309803423/2500000000 : ℝ)^2123 ≤ (42662339340381/100000000000000 : ℝ)^1611 := by
    have hnat : (1309803423 : ℕ)^2123*100000000000000^1611 ≤ 42662339340381^1611*2500000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309803423 2500000000 42662339340381 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109241707/500000000 : ℝ)^2123 ≤ (13473354638671/100000000000000 : ℝ)^1611 := by
    have hnat : (109241707 : ℕ)^2123*100000000000000^1611 ≤ 13473354638671^1611*500000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109241707 500000000 13473354638671 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350848197/10000000000 : ℝ), (1309803423/2500000000 : ℝ), (-109241707/500000000 : ℝ)] ![(43864306004669/100000000000000 : ℝ), (42662339340381/100000000000000 : ℝ), (13473354638671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350848197/10000000000 : ℝ)|^2123 ≤ (43864306004669/100000000000000 : ℝ)^1611
        have hw : |(5350848197/10000000000 : ℝ)|=(5350848197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309803423/2500000000 : ℝ)|^2123 ≤ (42662339340381/100000000000000 : ℝ)^1611
        have hw : |(1309803423/2500000000 : ℝ)|=(1309803423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109241707/500000000 : ℝ)|^2123 ≤ (13473354638671/100000000000000 : ℝ)^1611
        have hw : |(-109241707/500000000 : ℝ)|=(109241707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s4_3 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (542651301/1250000000 : ℝ)*x 0 + (2080121447/5000000000 : ℝ)*x 1 + (4529711547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542651301/1250000000 : ℝ)^2123 ≤ (16649765444819/50000000000000 : ℝ)^1611 := by
    have hnat : (542651301 : ℕ)^2123*50000000000000^1611 ≤ 16649765444819^1611*1250000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542651301 1250000000 16649765444819 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080121447/5000000000 : ℝ)^2123 ≤ (31482476281931/100000000000000 : ℝ)^1611 := by
    have hnat : (2080121447 : ℕ)^2123*100000000000000^1611 ≤ 31482476281931^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080121447 5000000000 31482476281931 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4529711547/10000000000 : ℝ)^2123 ≤ (35217992799569/100000000000000 : ℝ)^1611 := by
    have hnat : (4529711547 : ℕ)^2123*100000000000000^1611 ≤ 35217992799569^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529711547 10000000000 35217992799569 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542651301/1250000000 : ℝ), (2080121447/5000000000 : ℝ), (4529711547/10000000000 : ℝ)] ![(16649765444819/50000000000000 : ℝ), (31482476281931/100000000000000 : ℝ), (35217992799569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542651301/1250000000 : ℝ)|^2123 ≤ (16649765444819/50000000000000 : ℝ)^1611
        have hw : |(542651301/1250000000 : ℝ)|=(542651301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080121447/5000000000 : ℝ)|^2123 ≤ (31482476281931/100000000000000 : ℝ)^1611
        have hw : |(2080121447/5000000000 : ℝ)|=(2080121447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4529711547/10000000000 : ℝ)|^2123 ≤ (35217992799569/100000000000000 : ℝ)^1611
        have hw : |(4529711547/10000000000 : ℝ)|=(4529711547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s4_4 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092920343/10000000000 : ℝ)*x 0 + (1047976613/2000000000 : ℝ)*x 1 + (677340413/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092920343/10000000000 : ℝ)^2123 ≤ (3182861290013/25000000000000 : ℝ)^1611 := by
    have hnat : (2092920343 : ℕ)^2123*25000000000000^1611 ≤ 3182861290013^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092920343 10000000000 3182861290013 25000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047976613/2000000000 : ℝ)^2123 ≤ (4266952240899/10000000000000 : ℝ)^1611 := by
    have hnat : (1047976613 : ℕ)^2123*10000000000000^1611 ≤ 4266952240899^1611*2000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047976613 2000000000 4266952240899 10000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677340413/1250000000 : ℝ)^2123 ≤ (5574879050739/12500000000000 : ℝ)^1611 := by
    have hnat : (677340413 : ℕ)^2123*12500000000000^1611 ≤ 5574879050739^1611*1250000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677340413 1250000000 5574879050739 12500000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092920343/10000000000 : ℝ), (1047976613/2000000000 : ℝ), (677340413/1250000000 : ℝ)] ![(3182861290013/25000000000000 : ℝ), (4266952240899/10000000000000 : ℝ), (5574879050739/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092920343/10000000000 : ℝ)|^2123 ≤ (3182861290013/25000000000000 : ℝ)^1611
        have hw : |(-2092920343/10000000000 : ℝ)|=(2092920343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047976613/2000000000 : ℝ)|^2123 ≤ (4266952240899/10000000000000 : ℝ)^1611
        have hw : |(1047976613/2000000000 : ℝ)|=(1047976613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677340413/1250000000 : ℝ)|^2123 ≤ (5574879050739/12500000000000 : ℝ)^1611
        have hw : |(677340413/1250000000 : ℝ)|=(677340413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s4_5 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530475157/1000000000 : ℝ)*x 0 + (-1002662303/5000000000 : ℝ)*x 1 + (677340423/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530475157/1000000000 : ℝ)^2123 ≤ (21683504339101/50000000000000 : ℝ)^1611 := by
    have hnat : (530475157 : ℕ)^2123*50000000000000^1611 ≤ 21683504339101^1611*1000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530475157 1000000000 21683504339101 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002662303/5000000000 : ℝ)^2123 ≤ (12033958032287/100000000000000 : ℝ)^1611 := by
    have hnat : (1002662303 : ℕ)^2123*100000000000000^1611 ≤ 12033958032287^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002662303 5000000000 12033958032287 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677340423/1250000000 : ℝ)^2123 ≤ (44599033273619/100000000000000 : ℝ)^1611 := by
    have hnat : (677340423 : ℕ)^2123*100000000000000^1611 ≤ 44599033273619^1611*1250000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677340423 1250000000 44599033273619 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530475157/1000000000 : ℝ), (-1002662303/5000000000 : ℝ), (677340423/1250000000 : ℝ)] ![(21683504339101/50000000000000 : ℝ), (12033958032287/100000000000000 : ℝ), (44599033273619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530475157/1000000000 : ℝ)|^2123 ≤ (21683504339101/50000000000000 : ℝ)^1611
        have hw : |(530475157/1000000000 : ℝ)|=(530475157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1002662303/5000000000 : ℝ)|^2123 ≤ (12033958032287/100000000000000 : ℝ)^1611
        have hw : |(-1002662303/5000000000 : ℝ)|=(1002662303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677340423/1250000000 : ℝ)|^2123 ≤ (44599033273619/100000000000000 : ℝ)^1611
        have hw : |(677340423/1250000000 : ℝ)|=(677340423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s4_6 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304751609/10000000000 : ℝ)*x 0 + (1083744663/2000000000 : ℝ)*x 1 + (-250665581/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304751609/10000000000 : ℝ)^2123 ≤ (1084175227459/2500000000000 : ℝ)^1611 := by
    have hnat : (5304751609 : ℕ)^2123*2500000000000^1611 ≤ 1084175227459^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304751609 10000000000 1084175227459 2500000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083744663/2000000000 : ℝ)^2123 ≤ (22299516262611/50000000000000 : ℝ)^1611 := by
    have hnat : (1083744663 : ℕ)^2123*50000000000000^1611 ≤ 22299516262611^1611*2000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083744663 2000000000 22299516262611 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250665581/1250000000 : ℝ)^2123 ≤ (12033958364431/100000000000000 : ℝ)^1611 := by
    have hnat : (250665581 : ℕ)^2123*100000000000000^1611 ≤ 12033958364431^1611*1250000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250665581 1250000000 12033958364431 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304751609/10000000000 : ℝ), (1083744663/2000000000 : ℝ), (-250665581/1250000000 : ℝ)] ![(1084175227459/2500000000000 : ℝ), (22299516262611/50000000000000 : ℝ), (12033958364431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304751609/10000000000 : ℝ)|^2123 ≤ (1084175227459/2500000000000 : ℝ)^1611
        have hw : |(5304751609/10000000000 : ℝ)|=(5304751609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083744663/2000000000 : ℝ)|^2123 ≤ (22299516262611/50000000000000 : ℝ)^1611
        have hw : |(1083744663/2000000000 : ℝ)|=(1083744663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250665581/1250000000 : ℝ)|^2123 ≤ (12033958364431/100000000000000 : ℝ)^1611
        have hw : |(-250665581/1250000000 : ℝ)|=(250665581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s4_7 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (542655011/1250000000 : ℝ)*x 0 + (4528339167/10000000000 : ℝ)*x 1 + (4161622667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542655011/1250000000 : ℝ)^2123 ≤ (33299830906803/100000000000000 : ℝ)^1611 := by
    have hnat : (542655011 : ℕ)^2123*100000000000000^1611 ≤ 33299830906803^1611*1250000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542655011 1250000000 33299830906803 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4528339167/10000000000 : ℝ)^2123 ≤ (7040786452067/20000000000000 : ℝ)^1611 := by
    have hnat : (4528339167 : ℕ)^2123*20000000000000^1611 ≤ 7040786452067^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528339167 10000000000 7040786452067 20000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4161622667/10000000000 : ℝ)^2123 ≤ (31496236812503/100000000000000 : ℝ)^1611 := by
    have hnat : (4161622667 : ℕ)^2123*100000000000000^1611 ≤ 31496236812503^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161622667 10000000000 31496236812503 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542655011/1250000000 : ℝ), (4528339167/10000000000 : ℝ), (4161622667/10000000000 : ℝ)] ![(33299830906803/100000000000000 : ℝ), (7040786452067/20000000000000 : ℝ), (31496236812503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542655011/1250000000 : ℝ)|^2123 ≤ (33299830906803/100000000000000 : ℝ)^1611
        have hw : |(542655011/1250000000 : ℝ)|=(542655011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4528339167/10000000000 : ℝ)|^2123 ≤ (7040786452067/20000000000000 : ℝ)^1611
        have hw : |(4528339167/10000000000 : ℝ)|=(4528339167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4161622667/10000000000 : ℝ)|^2123 ≤ (31496236812503/100000000000000 : ℝ)^1611
        have hw : |(4161622667/10000000000 : ℝ)|=(4161622667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1286_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152526313/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7537/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10631/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1367/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7537/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10631/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7537/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10631/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7537/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10631/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7537/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10631/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7537/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10631/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7537/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10631/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10631/100000 : ℝ) ^ (4245/1024 : ℝ) ≤ (9218396880302503/100000000000000000000 : ℝ) := by
    have hpowers : (10631/100000 : ℝ)^4245 ≤ (9218396880302503/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10631 : ℕ)^4245*100000000000000000000^1024 ≤ 9218396880302503^1024*100000^4245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10631 100000 9218396880302503 100000000000000000000 4245 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10631/100000 : ℝ)) (X := (9218396880302503/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7537/50000 : ℝ) ^ (4245/1024 : ℝ) ≤ (39204856809669829/100000000000000000000 : ℝ) := by
    have hpowers : (7537/50000 : ℝ)^4245 ≤ (39204856809669829/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7537 : ℕ)^4245*100000000000000000000^1024 ≤ 39204856809669829^1024*50000^4245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7537 50000 39204856809669829 100000000000000000000 4245 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7537/50000 : ℝ)) (X := (39204856809669829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009218396880302503/50000000000000000000 : ℝ) ≤ (2500111177599569/2500000000000000 : ℝ) ^ (4245/1024 : ℝ) := by
    have hpowers : (50009218396880302503/50000000000000000000 : ℝ)^1024 ≤ (2500111177599569/2500000000000000 : ℝ)^4245 := by
      have hnat : (50009218396880302503 : ℕ)^1024*2500000000000000^4245 ≤ 2500111177599569^4245*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009218396880302503 50000000000000000000 2500111177599569 2500000000000000 1024 4245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500111177599569/2500000000000000 : ℝ)) (X := (50009218396880302503/50000000000000000000 : ℝ)) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012105813422493083/25000000000000000000 : ℝ) ≤ (10001167875263593/10000000000000000 : ℝ) ^ (4245/1024 : ℝ) := by
    have hpowers : (25012105813422493083/25000000000000000000 : ℝ)^1024 ≤ (10001167875263593/10000000000000000 : ℝ)^4245 := by
      have hnat : (25012105813422493083 : ℕ)^1024*10000000000000000^4245 ≤ 10001167875263593^4245*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012105813422493083 25000000000000000000 10001167875263593 10000000000000000 1024 4245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001167875263593/10000000000000000 : ℝ)) (X := (25012105813422493083/25000000000000000000 : ℝ)) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039204856809669829/50000000000000000000 : ℝ) ≤ (1000189104012891/1000000000000000 : ℝ) ^ (4245/1024 : ℝ) := by
    have hpowers : (50039204856809669829/50000000000000000000 : ℝ)^1024 ≤ (1000189104012891/1000000000000000 : ℝ)^4245 := by
      have hnat : (50039204856809669829 : ℕ)^1024*1000000000000000^4245 ≤ 1000189104012891^4245*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039204856809669829 50000000000000000000 1000189104012891 1000000000000000 1024 4245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000189104012891/1000000000000000 : ℝ)) (X := (50039204856809669829/50000000000000000000 : ℝ)) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9218396880302503/100000000000000000000 : ℝ) ≤ ((22208299958466585107/22215000000000000000 : ℝ)+2*(723164865317/444300000000000 : ℝ)*(10631/100000 : ℝ))^(4245/1024 : ℝ) := by
    rw [show (22208299958466585107/22215000000000000000 : ℝ)+2*(723164865317/444300000000000 : ℝ)*(10631/100000 : ℝ)=(2500111177599569/2500000000000000 : ℝ) by norm_num, show 1+2*(9218396880302503/100000000000000000000 : ℝ)=(50009218396880302503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39204856809669829/100000000000000000000 : ℝ)+(9218396880302503/100000000000000000000 : ℝ) ≤ ((22208299958466585107/22215000000000000000 : ℝ)+(723164865317/444300000000000 : ℝ)*((7537/50000 : ℝ)+(10631/100000 : ℝ)))^(4245/1024 : ℝ) := by
    rw [show (22208299958466585107/22215000000000000000 : ℝ)+(723164865317/444300000000000 : ℝ)*((7537/50000 : ℝ)+(10631/100000 : ℝ))=(10001167875263593/10000000000000000 : ℝ) by norm_num, show 1+(39204856809669829/100000000000000000000 : ℝ)+(9218396880302503/100000000000000000000 : ℝ)=(25012105813422493083/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39204856809669829/100000000000000000000 : ℝ) ≤ ((22208299958466585107/22215000000000000000 : ℝ)+2*(723164865317/444300000000000 : ℝ)*(7537/50000 : ℝ))^(4245/1024 : ℝ) := by
    rw [show (22208299958466585107/22215000000000000000 : ℝ)+2*(723164865317/444300000000000 : ℝ)*(7537/50000 : ℝ)=(1000189104012891/1000000000000000 : ℝ) by norm_num, show 1+2*(39204856809669829/100000000000000000000 : ℝ)=(50039204856809669829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22208299958466585107/22215000000000000000 : ℝ)*(X 1 0+X 2 0)+(723164865317/444300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4245/1024 : ℝ)) (lo := (10631/100000 : ℝ)) (hi := (7537/50000 : ℝ)) (c := (22208299958466585107/22215000000000000000 : ℝ)) (alpha := (723164865317/444300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22208299958466585107/22215000000000000000 : ℝ)*(X 0 1+X 2 1)+(723164865317/444300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4245/1024 : ℝ)) (lo := (10631/100000 : ℝ)) (hi := (7537/50000 : ℝ)) (c := (22208299958466585107/22215000000000000000 : ℝ)) (alpha := (723164865317/444300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22208299958466585107/22215000000000000000 : ℝ)*(X 0 2+X 1 2)+(723164865317/444300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4245/1024 : ℝ)) (lo := (10631/100000 : ℝ)) (hi := (7537/50000 : ℝ)) (c := (22208299958466585107/22215000000000000000 : ℝ)) (alpha := (723164865317/444300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-261613247/1250000000 : ℝ)*X 0 0+(1083879209/2000000000 : ℝ)*X 0 1+(654901727/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337712041/2500000000 : ℝ)*X 1 0+(-546208521/2500000000 : ℝ)*X 1 1+(654901721/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350848197/10000000000 : ℝ)*X 2 0+(1309803423/2500000000 : ℝ)*X 2 1+(-109241707/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((542651301/1250000000 : ℝ)*X 0 0+(2080121447/5000000000 : ℝ)*X 0 1+(4529711547/10000000000 : ℝ)*X 0 2+(542651301/1250000000 : ℝ)*X 1 0+(2080121447/5000000000 : ℝ)*X 1 1+(4529711547/10000000000 : ℝ)*X 1 2+(542651301/1250000000 : ℝ)*X 2 0+(2080121447/5000000000 : ℝ)*X 2 1+(4529711547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2092920343/10000000000 : ℝ)*X 0 0+(1047976613/2000000000 : ℝ)*X 0 1+(677340413/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530475157/1000000000 : ℝ)*X 1 0+(-1002662303/5000000000 : ℝ)*X 1 1+(677340423/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304751609/10000000000 : ℝ)*X 2 0+(1083744663/2000000000 : ℝ)*X 2 1+(-250665581/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542655011/1250000000 : ℝ)*X 0 0+(4528339167/10000000000 : ℝ)*X 0 1+(4161622667/10000000000 : ℝ)*X 0 2+(542655011/1250000000 : ℝ)*X 1 0+(4528339167/10000000000 : ℝ)*X 1 1+(4161622667/10000000000 : ℝ)*X 1 2+(542655011/1250000000 : ℝ)*X 2 0+(4528339167/10000000000 : ℝ)*X 2 1+(4161622667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47407072869779376368337/7405000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372375933/25000000000000 : ℝ)*(base19) + (94572341/6250000000000 : ℝ)*(base23) + (5658217/100000000000000 : ℝ)*(lower2) + (206301741/100000000000000 : ℝ)*(upper3) + (70045953/50000000000000 : ℝ)*(upper5) + (4128305114721651/100000000000000 : ℝ)*(major0) + (4128305114721651/100000000000000 : ℝ)*(major1) + (1032076278680413/25000000000000 : ℝ)*(major2) + (1109993035937321/20000000000000 : ℝ)*(sp0) + (2774995108434493/50000000000000 : ℝ)*(sp1) + (2774995096607631/50000000000000 : ℝ)*(sp2) + (2706603335125277/100000000000000 : ℝ)*(sp3) + (26526686113/100000000000000 : ℝ)*(sp4) + (14974544119/100000000000000 : ℝ)*(sp7) + (676654577417349/25000000000000 : ℝ)*(f.failure) + (2774995853186359/50000000000000 : ℝ)*(f.sum) + (169408009448981/44430000000000000000000000000 : ℝ)*base65 + (3943009056950248343/2221500000000000000000000000000000 : ℝ)*base68 + (1021190077881496691/555375000000000000000000000000000 : ℝ)*base69 + (15941697176963251657/2221500000000000000000000000000000 : ℝ)*base71 + (193236067931359/44430000000000000000000000000 : ℝ)*base74 + (1995044447204503309/555375000000000000000000000000000 : ℝ)*base76 + (10055339432622532781/740500000000000000000000000000000 : ℝ)*base78 + (5621045779900967219/740500000000000000000000000000000 : ℝ)*base79 + (9021911747071/7405000000000000000000000000 : ℝ)*base82 + (30204237/2500000000000000000000 : ℝ)*base89 + (30204237/2500000000000000000000 : ℝ)*base91 + (5204237/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2692318762879500217499691351/370250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1086491677/100000000000000 : ℝ)*(base19) + (1268697987/100000000000000 : ℝ)*(base23) + (27241023/20000000000000 : ℝ)*(upper3) + (17860651/25000000000000 : ℝ)*(lower4) + (164255149/100000000000000 : ℝ)*(upper5) + (4159242081961569/100000000000000 : ℝ)*(major0) + (4159242081961569/100000000000000 : ℝ)*(major1) + (4159242081961569/100000000000000 : ℝ)*(major2) + (5658184889/25000000000000 : ℝ)*(sp1) + (23371658231/100000000000000 : ℝ)*(sp2) + (5591582575692757/100000000000000 : ℝ)*(sp4) + (5591558856461523/100000000000000 : ℝ)*(sp5) + (5591557935336539/100000000000000 : ℝ)*(sp6) + (272690134584291/10000000000000 : ℝ)*(sp7) + (272690134584291/10000000000000 : ℝ)*(f.failure) + (5591582575692757/100000000000000 : ℝ)*(f.sum) + (3842881887977/3702500000000000000000000000 : ℝ)*base66 + (2187316603599300961/740500000000000000000000000000000 : ℝ)*base67 + (3810319383617800961/740500000000000000000000000000000 : ℝ)*base69 + (961436478239800961/740500000000000000000000000000000 : ℝ)*base71 + (14716035501951/7405000000000000000000000000 : ℝ)*base73 + (20671614190881800961/740500000000000000000000000000000 : ℝ)*base75 + (93804132647800961/740500000000000000000000000000000 : ℝ)*base77 + (4554735511203300961/740500000000000000000000000000000 : ℝ)*base79 + (26532976655199/7405000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3949083/1000000000000000000000 : ℝ)*base89 + (3949083/1000000000000000000000 : ℝ)*base91 + (3949083/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1286_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152526313/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7537/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10631/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1367/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1286_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1286_s5_0 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2093279337/10000000000 : ℝ)*x 0 + (54162323/100000000 : ℝ)*x 1 + (655266533/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093279337/10000000000 : ℝ)^2123 ≤ (6367161539257/50000000000000 : ℝ)^1611 := by
    have hnat : (2093279337 : ℕ)^2123*50000000000000^1611 ≤ 6367161539257^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093279337 10000000000 6367161539257 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54162323/100000000 : ℝ)^2123 ≤ (8914403224417/20000000000000 : ℝ)^1611 := by
    have hnat : (54162323 : ℕ)^2123*20000000000000^1611 ≤ 8914403224417^1611*100000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54162323 100000000 8914403224417 20000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655266533/1250000000 : ℝ)^2123 ≤ (213468303951/500000000000 : ℝ)^1611 := by
    have hnat : (655266533 : ℕ)^2123*500000000000^1611 ≤ 213468303951^1611*1250000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655266533 1250000000 213468303951 500000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2093279337/10000000000 : ℝ), (54162323/100000000 : ℝ), (655266533/1250000000 : ℝ)] ![(6367161539257/50000000000000 : ℝ), (8914403224417/20000000000000 : ℝ), (213468303951/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2093279337/10000000000 : ℝ)|^2123 ≤ (6367161539257/50000000000000 : ℝ)^1611
        have hw : |(-2093279337/10000000000 : ℝ)|=(2093279337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54162323/100000000 : ℝ)|^2123 ≤ (8914403224417/20000000000000 : ℝ)^1611
        have hw : |(54162323/100000000 : ℝ)|=(54162323/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655266533/1250000000 : ℝ)|^2123 ≤ (213468303951/500000000000 : ℝ)^1611
        have hw : |(655266533/1250000000 : ℝ)|=(655266533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s5_1 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668755861/1250000000 : ℝ)*x 0 + (-1091022299/5000000000 : ℝ)*x 1 + (2621066127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668755861/1250000000 : ℝ)^2123 ≤ (43855649695261/100000000000000 : ℝ)^1611 := by
    have hnat : (668755861 : ℕ)^2123*100000000000000^1611 ≤ 43855649695261^1611*1250000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668755861 1250000000 43855649695261 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091022299/5000000000 : ℝ)^2123 ≤ (13450689599291/100000000000000 : ℝ)^1611 := by
    have hnat : (1091022299 : ℕ)^2123*100000000000000^1611 ≤ 13450689599291^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091022299 5000000000 13450689599291 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621066127/5000000000 : ℝ)^2123 ≤ (42693660682873/100000000000000 : ℝ)^1611 := by
    have hnat : (2621066127 : ℕ)^2123*100000000000000^1611 ≤ 42693660682873^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621066127 5000000000 42693660682873 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668755861/1250000000 : ℝ), (-1091022299/5000000000 : ℝ), (2621066127/5000000000 : ℝ)] ![(43855649695261/100000000000000 : ℝ), (13450689599291/100000000000000 : ℝ), (42693660682873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668755861/1250000000 : ℝ)|^2123 ≤ (43855649695261/100000000000000 : ℝ)^1611
        have hw : |(668755861/1250000000 : ℝ)|=(668755861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091022299/5000000000 : ℝ)|^2123 ≤ (13450689599291/100000000000000 : ℝ)^1611
        have hw : |(-1091022299/5000000000 : ℝ)|=(1091022299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621066127/5000000000 : ℝ)|^2123 ≤ (42693660682873/100000000000000 : ℝ)^1611
        have hw : |(2621066127/5000000000 : ℝ)|=(2621066127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s5_2 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (342403/640000 : ℝ)*x 0 + (327633267/625000000 : ℝ)*x 1 + (-2182044593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342403/640000 : ℝ)^2123 ≤ (43855649554829/100000000000000 : ℝ)^1611 := by
    have hnat : (342403 : ℕ)^2123*100000000000000^1611 ≤ 43855649554829^1611*640000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342403 640000 43855649554829 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327633267/625000000 : ℝ)^2123 ≤ (21346830438031/50000000000000 : ℝ)^1611 := by
    have hnat : (327633267 : ℕ)^2123*50000000000000^1611 ≤ 21346830438031^1611*625000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327633267 625000000 21346830438031 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182044593/10000000000 : ℝ)^2123 ≤ (6725344779337/50000000000000 : ℝ)^1611 := by
    have hnat : (2182044593 : ℕ)^2123*50000000000000^1611 ≤ 6725344779337^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182044593 10000000000 6725344779337 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(342403/640000 : ℝ), (327633267/625000000 : ℝ), (-2182044593/10000000000 : ℝ)] ![(43855649554829/100000000000000 : ℝ), (21346830438031/50000000000000 : ℝ), (6725344779337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(342403/640000 : ℝ)|^2123 ≤ (43855649554829/100000000000000 : ℝ)^1611
        have hw : |(342403/640000 : ℝ)|=(342403/640000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327633267/625000000 : ℝ)|^2123 ≤ (21346830438031/50000000000000 : ℝ)^1611
        have hw : |(327633267/625000000 : ℝ)|=(327633267/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182044593/10000000000 : ℝ)|^2123 ≤ (6725344779337/50000000000000 : ℝ)^1611
        have hw : |(-2182044593/10000000000 : ℝ)|=(2182044593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s5_3 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4341432049/10000000000 : ℝ)*x 0 + (2083225481/5000000000 : ℝ)*x 1 + (2261723813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341432049/10000000000 : ℝ)^2123 ≤ (33301771340163/100000000000000 : ℝ)^1611 := by
    have hnat : (4341432049 : ℕ)^2123*100000000000000^1611 ≤ 33301771340163^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341432049 10000000000 33301771340163 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083225481/5000000000 : ℝ)^2123 ≤ (15772200501037/50000000000000 : ℝ)^1611 := by
    have hnat : (2083225481 : ℕ)^2123*50000000000000^1611 ≤ 15772200501037^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083225481 5000000000 15772200501037 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261723813/5000000000 : ℝ)^2123 ≤ (4394228454529/12500000000000 : ℝ)^1611 := by
    have hnat : (2261723813 : ℕ)^2123*12500000000000^1611 ≤ 4394228454529^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261723813 5000000000 4394228454529 12500000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341432049/10000000000 : ℝ), (2083225481/5000000000 : ℝ), (2261723813/5000000000 : ℝ)] ![(33301771340163/100000000000000 : ℝ), (15772200501037/50000000000000 : ℝ), (4394228454529/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341432049/10000000000 : ℝ)|^2123 ≤ (33301771340163/100000000000000 : ℝ)^1611
        have hw : |(4341432049/10000000000 : ℝ)|=(4341432049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2083225481/5000000000 : ℝ)|^2123 ≤ (15772200501037/50000000000000 : ℝ)^1611
        have hw : |(2083225481/5000000000 : ℝ)|=(2083225481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261723813/5000000000 : ℝ)|^2123 ≤ (4394228454529/12500000000000 : ℝ)^1611
        have hw : |(2261723813/5000000000 : ℝ)|=(2261723813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s5_4 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-83731697/400000000 : ℝ)*x 0 + (5242757263/10000000000 : ℝ)*x 1 + (5415604059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83731697/400000000 : ℝ)^2123 ≤ (12734428003/100000000000 : ℝ)^1611 := by
    have hnat : (83731697 : ℕ)^2123*100000000000^1611 ≤ 12734428003^1611*400000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83731697 400000000 12734428003 100000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242757263/10000000000 : ℝ)^2123 ≤ (2668773053607/6250000000000 : ℝ)^1611 := by
    have hnat : (5242757263 : ℕ)^2123*6250000000000^1611 ≤ 2668773053607^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242757263 10000000000 2668773053607 6250000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415604059/10000000000 : ℝ)^2123 ≤ (44565203132573/100000000000000 : ℝ)^1611 := by
    have hnat : (5415604059 : ℕ)^2123*100000000000000^1611 ≤ 44565203132573^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415604059 10000000000 44565203132573 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83731697/400000000 : ℝ), (5242757263/10000000000 : ℝ), (5415604059/10000000000 : ℝ)] ![(12734428003/100000000000 : ℝ), (2668773053607/6250000000000 : ℝ), (44565203132573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83731697/400000000 : ℝ)|^2123 ≤ (12734428003/100000000000 : ℝ)^1611
        have hw : |(-83731697/400000000 : ℝ)|=(83731697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242757263/10000000000 : ℝ)|^2123 ≤ (2668773053607/6250000000000 : ℝ)^1611
        have hw : |(5242757263/10000000000 : ℝ)|=(5242757263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415604059/10000000000 : ℝ)|^2123 ≤ (44565203132573/100000000000000 : ℝ)^1611
        have hw : |(5415604059/10000000000 : ℝ)|=(5415604059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s5_5 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305506759/10000000000 : ℝ)*x 0 + (-200857281/1000000000 : ℝ)*x 1 + (2707802029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305506759/10000000000 : ℝ)^2123 ≤ (10843786185523/25000000000000 : ℝ)^1611 := by
    have hnat : (5305506759 : ℕ)^2123*25000000000000^1611 ≤ 10843786185523^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305506759 10000000000 10843786185523 25000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200857281/1000000000 : ℝ)^2123 ≤ (6029826062617/50000000000000 : ℝ)^1611 := by
    have hnat : (200857281 : ℕ)^2123*50000000000000^1611 ≤ 6029826062617^1611*1000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200857281 1000000000 6029826062617 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707802029/5000000000 : ℝ)^2123 ≤ (696331298777/1562500000000 : ℝ)^1611 := by
    have hnat : (2707802029 : ℕ)^2123*1562500000000^1611 ≤ 696331298777^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707802029 5000000000 696331298777 1562500000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305506759/10000000000 : ℝ), (-200857281/1000000000 : ℝ), (2707802029/5000000000 : ℝ)] ![(10843786185523/25000000000000 : ℝ), (6029826062617/50000000000000 : ℝ), (696331298777/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305506759/10000000000 : ℝ)|^2123 ≤ (10843786185523/25000000000000 : ℝ)^1611
        have hw : |(5305506759/10000000000 : ℝ)|=(5305506759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200857281/1000000000 : ℝ)|^2123 ≤ (6029826062617/50000000000000 : ℝ)^1611
        have hw : |(-200857281/1000000000 : ℝ)|=(200857281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707802029/5000000000 : ℝ)|^2123 ≤ (696331298777/1562500000000 : ℝ)^1611
        have hw : |(2707802029/5000000000 : ℝ)|=(2707802029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s5_6 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305506759/10000000000 : ℝ)*x 0 + (2707802029/5000000000 : ℝ)*x 1 + (-2008572809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305506759/10000000000 : ℝ)^2123 ≤ (10843786185523/25000000000000 : ℝ)^1611 := by
    have hnat : (5305506759 : ℕ)^2123*25000000000000^1611 ≤ 10843786185523^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305506759 10000000000 10843786185523 25000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707802029/5000000000 : ℝ)^2123 ≤ (696331298777/1562500000000 : ℝ)^1611 := by
    have hnat : (2707802029 : ℕ)^2123*1562500000000^1611 ≤ 696331298777^1611*5000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707802029 5000000000 696331298777 1562500000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008572809/10000000000 : ℝ)^2123 ≤ (6029826058661/50000000000000 : ℝ)^1611 := by
    have hnat : (2008572809 : ℕ)^2123*50000000000000^1611 ≤ 6029826058661^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008572809 10000000000 6029826058661 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305506759/10000000000 : ℝ), (2707802029/5000000000 : ℝ), (-2008572809/10000000000 : ℝ)] ![(10843786185523/25000000000000 : ℝ), (696331298777/1562500000000 : ℝ), (6029826058661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305506759/10000000000 : ℝ)|^2123 ≤ (10843786185523/25000000000000 : ℝ)^1611
        have hw : |(5305506759/10000000000 : ℝ)|=(5305506759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707802029/5000000000 : ℝ)|^2123 ≤ (696331298777/1562500000000 : ℝ)^1611
        have hw : |(2707802029/5000000000 : ℝ)|=(2707802029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2008572809/10000000000 : ℝ)|^2123 ≤ (6029826058661/50000000000000 : ℝ)^1611
        have hw : |(-2008572809/10000000000 : ℝ)|=(2008572809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1286_s5_7 (p : ℝ) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4341458929/10000000000 : ℝ)*x 0 + (4522166027/10000000000 : ℝ)*x 1 + (1041934783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341458929/10000000000 : ℝ)^2123 ≤ (16651021529101/50000000000000 : ℝ)^1611 := by
    have hnat : (4341458929 : ℕ)^2123*50000000000000^1611 ≤ 16651021529101^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341458929 10000000000 16651021529101 50000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522166027/10000000000 : ℝ)^2123 ≤ (8785175728569/25000000000000 : ℝ)^1611 := by
    have hnat : (4522166027 : ℕ)^2123*25000000000000^1611 ≤ 8785175728569^1611*10000000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522166027 10000000000 8785175728569 25000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041934783/2500000000 : ℝ)^2123 ≤ (31557254016053/100000000000000 : ℝ)^1611 := by
    have hnat : (1041934783 : ℕ)^2123*100000000000000^1611 ≤ 31557254016053^1611*2500000000^2123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041934783 2500000000 31557254016053 100000000000000 2123 1611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2123/512 : ℝ)) 2123 1611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341458929/10000000000 : ℝ), (4522166027/10000000000 : ℝ), (1041934783/2500000000 : ℝ)] ![(16651021529101/50000000000000 : ℝ), (8785175728569/25000000000000 : ℝ), (31557254016053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341458929/10000000000 : ℝ)|^2123 ≤ (16651021529101/50000000000000 : ℝ)^1611
        have hw : |(4341458929/10000000000 : ℝ)|=(4341458929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522166027/10000000000 : ℝ)|^2123 ≤ (8785175728569/25000000000000 : ℝ)^1611
        have hw : |(4522166027/10000000000 : ℝ)|=(4522166027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041934783/2500000000 : ℝ)|^2123 ≤ (31557254016053/100000000000000 : ℝ)^1611
        have hw : |(1041934783/2500000000 : ℝ)|=(1041934783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1286_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152526313/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1367/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5499/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14683/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1367/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1367/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1367/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1367/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1367/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1367/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1367/12500 : ℝ) ^ (4245/1024 : ℝ) ≤ (10365264987708723/100000000000000000000 : ℝ) := by
    have hpowers : (1367/12500 : ℝ)^4245 ≤ (10365264987708723/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1367 : ℕ)^4245*100000000000000000000^1024 ≤ 10365264987708723^1024*12500^4245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1367 12500 10365264987708723 100000000000000000000 4245 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1367/12500 : ℝ)) (X := (10365264987708723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (4245/1024 : ℝ) ≤ (179088940657217/500000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^4245 ≤ (179088940657217/500000000000000000 : ℝ)^1024 := by
      have hnat : (14749 : ℕ)^4245*500000000000000000^1024 ≤ 179088940657217^1024*100000^4245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 179088940657217 500000000000000000 4245 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (179088940657217/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010365264987708723/50000000000000000000 : ℝ) ≤ (1250062504102859/1250000000000000 : ℝ) ^ (4245/1024 : ℝ) := by
    have hpowers : (50010365264987708723/50000000000000000000 : ℝ)^1024 ≤ (1250062504102859/1250000000000000 : ℝ)^4245 := by
      have hnat : (50010365264987708723 : ℕ)^1024*1250000000000000^4245 ≤ 1250062504102859^4245*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010365264987708723 50000000000000000000 1250062504102859 1250000000000000 1024 4245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250062504102859/1250000000000000 : ℝ)) (X := (50010365264987708723/50000000000000000000 : ℝ)) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046183053119152123/100000000000000000000 : ℝ) ≤ (10001113855419859/10000000000000000 : ℝ) ^ (4245/1024 : ℝ) := by
    have hpowers : (100046183053119152123/100000000000000000000 : ℝ)^1024 ≤ (10001113855419859/10000000000000000 : ℝ)^4245 := by
      have hnat : (100046183053119152123 : ℕ)^1024*10000000000000000^4245 ≤ 10001113855419859^4245*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046183053119152123 100000000000000000000 10001113855419859 10000000000000000 1024 4245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001113855419859/10000000000000000 : ℝ)) (X := (100046183053119152123/100000000000000000000 : ℝ)) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (250179088940657217/250000000000000000 : ℝ) ≤ (5000863839008423/5000000000000000 : ℝ) ^ (4245/1024 : ℝ) := by
    have hpowers : (250179088940657217/250000000000000000 : ℝ)^1024 ≤ (5000863839008423/5000000000000000 : ℝ)^4245 := by
      have hnat : (250179088940657217 : ℕ)^1024*5000000000000000^4245 ≤ 5000863839008423^4245*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250179088940657217 250000000000000000 5000863839008423 5000000000000000 1024 4245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000863839008423/5000000000000000 : ℝ)) (X := (250179088940657217/250000000000000000 : ℝ)) (by norm_num) 4245 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10365264987708723/100000000000000000000 : ℝ) ≤ ((1588270045721346303/1588750000000000000 : ℝ)+2*(204607532329/127100000000000 : ℝ)*(1367/12500 : ℝ))^(4245/1024 : ℝ) := by
    rw [show (1588270045721346303/1588750000000000000 : ℝ)+2*(204607532329/127100000000000 : ℝ)*(1367/12500 : ℝ)=(1250062504102859/1250000000000000 : ℝ) by norm_num, show 1+2*(10365264987708723/100000000000000000000 : ℝ)=(50010365264987708723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(179088940657217/500000000000000000 : ℝ)+(10365264987708723/100000000000000000000 : ℝ) ≤ ((1588270045721346303/1588750000000000000 : ℝ)+(204607532329/127100000000000 : ℝ)*((14749/100000 : ℝ)+(1367/12500 : ℝ)))^(4245/1024 : ℝ) := by
    rw [show (1588270045721346303/1588750000000000000 : ℝ)+(204607532329/127100000000000 : ℝ)*((14749/100000 : ℝ)+(1367/12500 : ℝ))=(10001113855419859/10000000000000000 : ℝ) by norm_num, show 1+(179088940657217/500000000000000000 : ℝ)+(10365264987708723/100000000000000000000 : ℝ)=(100046183053119152123/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(179088940657217/500000000000000000 : ℝ) ≤ ((1588270045721346303/1588750000000000000 : ℝ)+2*(204607532329/127100000000000 : ℝ)*(14749/100000 : ℝ))^(4245/1024 : ℝ) := by
    rw [show (1588270045721346303/1588750000000000000 : ℝ)+2*(204607532329/127100000000000 : ℝ)*(14749/100000 : ℝ)=(5000863839008423/5000000000000000 : ℝ) by norm_num, show 1+2*(179088940657217/500000000000000000 : ℝ)=(250179088940657217/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1588270045721346303/1588750000000000000 : ℝ)*(X 1 0+X 2 0)+(204607532329/127100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4245/1024 : ℝ)) (lo := (1367/12500 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (1588270045721346303/1588750000000000000 : ℝ)) (alpha := (204607532329/127100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1588270045721346303/1588750000000000000 : ℝ)*(X 0 1+X 2 1)+(204607532329/127100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4245/1024 : ℝ)) (lo := (1367/12500 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (1588270045721346303/1588750000000000000 : ℝ)) (alpha := (204607532329/127100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1588270045721346303/1588750000000000000 : ℝ)*(X 0 2+X 1 2)+(204607532329/127100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4245/1024 : ℝ)) (lo := (1367/12500 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (1588270045721346303/1588750000000000000 : ℝ)) (alpha := (204607532329/127100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2093279337/10000000000 : ℝ)*X 0 0+(54162323/100000000 : ℝ)*X 0 1+(655266533/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668755861/1250000000 : ℝ)*X 1 0+(-1091022299/5000000000 : ℝ)*X 1 1+(2621066127/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((342403/640000 : ℝ)*X 2 0+(327633267/625000000 : ℝ)*X 2 1+(-2182044593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4341432049/10000000000 : ℝ)*X 0 0+(2083225481/5000000000 : ℝ)*X 0 1+(2261723813/5000000000 : ℝ)*X 0 2+(4341432049/10000000000 : ℝ)*X 1 0+(2083225481/5000000000 : ℝ)*X 1 1+(2261723813/5000000000 : ℝ)*X 1 2+(4341432049/10000000000 : ℝ)*X 2 0+(2083225481/5000000000 : ℝ)*X 2 1+(2261723813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-83731697/400000000 : ℝ)*X 0 0+(5242757263/10000000000 : ℝ)*X 0 1+(5415604059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305506759/10000000000 : ℝ)*X 1 0+(-200857281/1000000000 : ℝ)*X 1 1+(2707802029/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305506759/10000000000 : ℝ)*X 2 0+(2707802029/5000000000 : ℝ)*X 2 1+(-2008572809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341458929/10000000000 : ℝ)*X 0 0+(4522166027/10000000000 : ℝ)*X 0 1+(1041934783/2500000000 : ℝ)*X 0 2+(4341458929/10000000000 : ℝ)*X 1 0+(4522166027/10000000000 : ℝ)*X 1 1+(1041934783/2500000000 : ℝ)*X 1 2+(4341458929/10000000000 : ℝ)*X 2 0+(4522166027/10000000000 : ℝ)*X 2 1+(1041934783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1286_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79721816743790556739607727/7943750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (189353049/10000000000000 : ℝ)*(base19) + (1770327531/100000000000000 : ℝ)*(base23) + (5844709/10000000000000 : ℝ)*(lower2) + (28892323/12500000000000 : ℝ)*(upper3) + (9614911/6250000000000 : ℝ)*(upper5) + (427254351830253/10000000000000 : ℝ)*(major0) + (427254351830253/10000000000000 : ℝ)*(major1) + (427254351830253/10000000000000 : ℝ)*(major2) + (717982983806849/12500000000000 : ℝ)*(sp0) + (5743900256016239/100000000000000 : ℝ)*(sp1) + (2871950189609599/50000000000000 : ℝ)*(sp2) + (280116477052263/10000000000000 : ℝ)*(sp3) + (38279091937/100000000000000 : ℝ)*(sp4) + (494550233/2500000000000 : ℝ)*(sp7) + (56023691050639/2000000000000 : ℝ)*(f.failure) + (5743902149546729/100000000000000 : ℝ)*(f.sum) + (10024312395217/1271000000000000000000000000 : ℝ)*base66 + (51217076024304659/15887500000000000000000000000000 : ℝ)*base67 + (27415821556445341/15887500000000000000000000000000 : ℝ)*base70 + (64995055805957841/15887500000000000000000000000000 : ℝ)*base72 + (2076269671091/317750000000000000000000000 : ℝ)*base74 + (73284057358742159/15887500000000000000000000000000 : ℝ)*base75 + (104086122741932841/15887500000000000000000000000000 : ℝ)*base78 + (141436144295382841/15887500000000000000000000000000 : ℝ)*base80 + (251763231669/158875000000000000000000000 : ℝ)*base82 + (2964007/200000000000000000000 : ℝ)*base89 + (2964007/200000000000000000000 : ℝ)*base91 + (2964007/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (157249144805515549445076279/19859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88000073/6250000000000 : ℝ)*(base19) + (765454731/50000000000000 : ℝ)*(base23) + (160600307/100000000000000 : ℝ)*(upper3) + (55635461/100000000000000 : ℝ)*(lower4) + (32343813/20000000000000 : ℝ)*(upper5) + (1075865679987903/25000000000000 : ℝ)*(major0) + (1075865679987903/25000000000000 : ℝ)*(major1) + (1075865679987903/25000000000000 : ℝ)*(major2) + (27918348721/100000000000000 : ℝ)*(sp1) + (30067793779/100000000000000 : ℝ)*(sp2) + (231418769392723/4000000000000 : ℝ)*(sp4) + (2892719954234093/50000000000000 : ℝ)*(sp5) + (2892718818057417/50000000000000 : ℝ)*(sp6) + (1410727970573711/50000000000000 : ℝ)*(sp7) + (1410727970573711/50000000000000 : ℝ)*(f.failure) + (231418769392723/4000000000000 : ℝ)*(f.sum) + (16056400233483/6355000000000000000000000000 : ℝ)*base65 + (345312438705421141/39718750000000000000000000000000 : ℝ)*base68 + (200947612008858641/39718750000000000000000000000000 : ℝ)*base70 + (473559092843264891/39718750000000000000000000000000 : ℝ)*base72 + (14845400938467/1588750000000000000000000000 : ℝ)*base73 + (420941586719672609/39718750000000000000000000000000 : ℝ)*base75 + (264092502206983641/39718750000000000000000000000000 : ℝ)*base78 + (103473054111202391/39718750000000000000000000000000 : ℝ)*base80 + (30839827730243/6355000000000000000000000000 : ℝ)*base81 + (33557543/5000000000000000000000 : ℝ)*base89 + (33557543/5000000000000000000000 : ℝ)*base91 + (33557543/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1286_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152526313/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1367/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1286_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1286_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152526313/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3269/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (473/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1286_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1286_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1286_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4245/1024 : ℝ) ≤ p) (hpb : p ≤ (2123/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152526313/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3269/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (473/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1286_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
