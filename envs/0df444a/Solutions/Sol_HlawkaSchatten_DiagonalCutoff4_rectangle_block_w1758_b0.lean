-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1758_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:24:52.189901+00:00
-- url     : https://prove2.me/submissions/09e0d64a-edc2-441a-9ea5-8232694eb500

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
theorem support_rectangle_w1758_s0_0 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1139866011/10000000000 : ℝ)*x 0 + (2803276493/5000000000 : ℝ)*x 1 + (4989440541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1139866011/10000000000 : ℝ)^5903 ≤ (1806538255399/25000000000000 : ℝ)^4879 := by
    have hnat : (1139866011 : ℕ)^5903*25000000000000^4879 ≤ 1806538255399^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139866011 10000000000 1806538255399 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2803276493/5000000000 : ℝ)^5903 ≤ (49653797151347/100000000000000 : ℝ)^4879 := by
    have hnat : (2803276493 : ℕ)^5903*100000000000000^4879 ≤ 49653797151347^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803276493 5000000000 49653797151347 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4989440541/10000000000 : ℝ)^5903 ≤ (43120049809419/100000000000000 : ℝ)^4879 := by
    have hnat : (4989440541 : ℕ)^5903*100000000000000^4879 ≤ 43120049809419^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989440541 10000000000 43120049809419 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1139866011/10000000000 : ℝ), (2803276493/5000000000 : ℝ), (4989440541/10000000000 : ℝ)] ![(1806538255399/25000000000000 : ℝ), (49653797151347/100000000000000 : ℝ), (43120049809419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1139866011/10000000000 : ℝ)|^5903 ≤ (1806538255399/25000000000000 : ℝ)^4879
        have hw : |(-1139866011/10000000000 : ℝ)|=(1139866011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2803276493/5000000000 : ℝ)|^5903 ≤ (49653797151347/100000000000000 : ℝ)^4879
        have hw : |(2803276493/5000000000 : ℝ)|=(2803276493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4989440541/10000000000 : ℝ)|^5903 ≤ (43120049809419/100000000000000 : ℝ)^4879
        have hw : |(4989440541/10000000000 : ℝ)|=(4989440541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s0_1 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340663333/2500000000 : ℝ)*x 0 + (-91855479/625000000 : ℝ)*x 1 + (249472059/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340663333/2500000000 : ℝ)^5903 ≤ (47052444372093/100000000000000 : ℝ)^4879 := by
    have hnat : (1340663333 : ℕ)^5903*100000000000000^4879 ≤ 47052444372093^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340663333 2500000000 47052444372093 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91855479/625000000 : ℝ)^5903 ≤ (614218695063/6250000000000 : ℝ)^4879 := by
    have hnat : (91855479 : ℕ)^5903*6250000000000^4879 ≤ 614218695063^4879*625000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91855479 625000000 614218695063 6250000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249472059/500000000 : ℝ)^5903 ≤ (21560028245431/50000000000000 : ℝ)^4879 := by
    have hnat : (249472059 : ℕ)^5903*50000000000000^4879 ≤ 21560028245431^4879*500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249472059 500000000 21560028245431 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340663333/2500000000 : ℝ), (-91855479/625000000 : ℝ), (249472059/500000000 : ℝ)] ![(47052444372093/100000000000000 : ℝ), (614218695063/6250000000000 : ℝ), (21560028245431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340663333/2500000000 : ℝ)|^5903 ≤ (47052444372093/100000000000000 : ℝ)^4879
        have hw : |(1340663333/2500000000 : ℝ)|=(1340663333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91855479/625000000 : ℝ)|^5903 ≤ (614218695063/6250000000000 : ℝ)^4879
        have hw : |(-91855479/625000000 : ℝ)|=(91855479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(249472059/500000000 : ℝ)|^5903 ≤ (21560028245431/50000000000000 : ℝ)^4879
        have hw : |(249472059/500000000 : ℝ)|=(249472059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s0_2 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681328353/5000000000 : ℝ)*x 0 + (7795999/15625000 : ℝ)*x 1 + (-1469685589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681328353/5000000000 : ℝ)^5903 ≤ (47052480189121/100000000000000 : ℝ)^4879 := by
    have hnat : (2681328353 : ℕ)^5903*100000000000000^4879 ≤ 47052480189121^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681328353 5000000000 47052480189121 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7795999/15625000 : ℝ)^5903 ≤ (5390004682597/12500000000000 : ℝ)^4879 := by
    have hnat : (7795999 : ℕ)^5903*12500000000000^4879 ≤ 5390004682597^4879*15625000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7795999 15625000 5390004682597 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1469685589/10000000000 : ℝ)^5903 ≤ (9827482333819/100000000000000 : ℝ)^4879 := by
    have hnat : (1469685589 : ℕ)^5903*100000000000000^4879 ≤ 9827482333819^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469685589 10000000000 9827482333819 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681328353/5000000000 : ℝ), (7795999/15625000 : ℝ), (-1469685589/10000000000 : ℝ)] ![(47052480189121/100000000000000 : ℝ), (5390004682597/12500000000000 : ℝ), (9827482333819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681328353/5000000000 : ℝ)|^5903 ≤ (47052480189121/100000000000000 : ℝ)^4879
        have hw : |(2681328353/5000000000 : ℝ)|=(2681328353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7795999/15625000 : ℝ)|^5903 ≤ (5390004682597/12500000000000 : ℝ)^4879
        have hw : |(7795999/15625000 : ℝ)|=(7795999/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1469685589/10000000000 : ℝ)|^5903 ≤ (9827482333819/100000000000000 : ℝ)^4879
        have hw : |(-1469685589/10000000000 : ℝ)|=(1469685589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s0_3 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (991467089/2500000000 : ℝ)*x 0 + (186942483/625000000 : ℝ)*x 1 + (5084966697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (991467089/2500000000 : ℝ)^5903 ≤ (4082704244469/12500000000000 : ℝ)^4879 := by
    have hnat : (991467089 : ℕ)^5903*12500000000000^4879 ≤ 4082704244469^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991467089 2500000000 4082704244469 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186942483/625000000 : ℝ)^5903 ≤ (45346658723/195312500000 : ℝ)^4879 := by
    have hnat : (186942483 : ℕ)^5903*195312500000^4879 ≤ 45346658723^4879*625000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186942483 625000000 45346658723 195312500000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084966697/10000000000 : ℝ)^5903 ≤ (5515109596657/12500000000000 : ℝ)^4879 := by
    have hnat : (5084966697 : ℕ)^5903*12500000000000^4879 ≤ 5515109596657^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084966697 10000000000 5515109596657 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(991467089/2500000000 : ℝ), (186942483/625000000 : ℝ), (5084966697/10000000000 : ℝ)] ![(4082704244469/12500000000000 : ℝ), (45346658723/195312500000 : ℝ), (5515109596657/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(991467089/2500000000 : ℝ)|^5903 ≤ (4082704244469/12500000000000 : ℝ)^4879
        have hw : |(991467089/2500000000 : ℝ)|=(991467089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186942483/625000000 : ℝ)|^5903 ≤ (45346658723/195312500000 : ℝ)^4879
        have hw : |(186942483/625000000 : ℝ)|=(186942483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084966697/10000000000 : ℝ)|^5903 ≤ (5515109596657/12500000000000 : ℝ)^4879
        have hw : |(5084966697/10000000000 : ℝ)|=(5084966697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s0_4 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-228214669/2000000000 : ℝ)*x 0 + (312810219/625000000 : ℝ)*x 1 + (5590531263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228214669/2000000000 : ℝ)^5903 ≤ (3617707150667/50000000000000 : ℝ)^4879 := by
    have hnat : (228214669 : ℕ)^5903*50000000000000^4879 ≤ 3617707150667^4879*2000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228214669 2000000000 3617707150667 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312810219/625000000 : ℝ)^5903 ≤ (8656482455231/20000000000000 : ℝ)^4879 := by
    have hnat : (312810219 : ℕ)^5903*20000000000000^4879 ≤ 8656482455231^4879*625000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312810219 625000000 8656482455231 20000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5590531263/10000000000 : ℝ)^5903 ≤ (9896434682143/20000000000000 : ℝ)^4879 := by
    have hnat : (5590531263 : ℕ)^5903*20000000000000^4879 ≤ 9896434682143^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590531263 10000000000 9896434682143 20000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-228214669/2000000000 : ℝ), (312810219/625000000 : ℝ), (5590531263/10000000000 : ℝ)] ![(3617707150667/50000000000000 : ℝ), (8656482455231/20000000000000 : ℝ), (9896434682143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-228214669/2000000000 : ℝ)|^5903 ≤ (3617707150667/50000000000000 : ℝ)^4879
        have hw : |(-228214669/2000000000 : ℝ)|=(228214669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312810219/625000000 : ℝ)|^5903 ≤ (8656482455231/20000000000000 : ℝ)^4879
        have hw : |(312810219/625000000 : ℝ)|=(312810219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5590531263/10000000000 : ℝ)|^5903 ≤ (9896434682143/20000000000000 : ℝ)^4879
        have hw : |(5590531263/10000000000 : ℝ)|=(5590531263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s0_5 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039722717/2000000000 : ℝ)*x 0 + (-108574401/1250000000 : ℝ)*x 1 + (5590531271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039722717/2000000000 : ℝ)^5903 ≤ (45316700025517/100000000000000 : ℝ)^4879 := by
    have hnat : (1039722717 : ℕ)^5903*100000000000000^4879 ≤ 45316700025517^4879*2000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039722717 2000000000 45316700025517 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108574401/1250000000 : ℝ)^5903 ≤ (650140808751/12500000000000 : ℝ)^4879 := by
    have hnat : (108574401 : ℕ)^5903*12500000000000^4879 ≤ 650140808751^4879*1250000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108574401 1250000000 650140808751 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5590531271/10000000000 : ℝ)^5903 ≤ (9896434699277/20000000000000 : ℝ)^4879 := by
    have hnat : (5590531271 : ℕ)^5903*20000000000000^4879 ≤ 9896434699277^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590531271 10000000000 9896434699277 20000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039722717/2000000000 : ℝ), (-108574401/1250000000 : ℝ), (5590531271/10000000000 : ℝ)] ![(45316700025517/100000000000000 : ℝ), (650140808751/12500000000000 : ℝ), (9896434699277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039722717/2000000000 : ℝ)|^5903 ≤ (45316700025517/100000000000000 : ℝ)^4879
        have hw : |(1039722717/2000000000 : ℝ)|=(1039722717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108574401/1250000000 : ℝ)|^5903 ≤ (650140808751/12500000000000 : ℝ)^4879
        have hw : |(-108574401/1250000000 : ℝ)|=(108574401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5590531271/10000000000 : ℝ)|^5903 ≤ (9896434699277/20000000000000 : ℝ)^4879
        have hw : |(5590531271/10000000000 : ℝ)|=(5590531271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s0_6 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299653221/2500000000 : ℝ)*x 0 + (698816437/1250000000 : ℝ)*x 1 + (-173719179/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299653221/2500000000 : ℝ)^5903 ≤ (45316692632347/100000000000000 : ℝ)^4879 := by
    have hnat : (1299653221 : ℕ)^5903*100000000000000^4879 ≤ 45316692632347^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299653221 2500000000 45316692632347 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698816437/1250000000 : ℝ)^5903 ≤ (49482175905847/100000000000000 : ℝ)^4879 := by
    have hnat : (698816437 : ℕ)^5903*100000000000000^4879 ≤ 49482175905847^4879*1250000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698816437 1250000000 49482175905847 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173719179/2000000000 : ℝ)^5903 ≤ (1040226289427/20000000000000 : ℝ)^4879 := by
    have hnat : (173719179 : ℕ)^5903*20000000000000^4879 ≤ 1040226289427^4879*2000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173719179 2000000000 1040226289427 20000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299653221/2500000000 : ℝ), (698816437/1250000000 : ℝ), (-173719179/2000000000 : ℝ)] ![(45316692632347/100000000000000 : ℝ), (49482175905847/100000000000000 : ℝ), (1040226289427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299653221/2500000000 : ℝ)|^5903 ≤ (45316692632347/100000000000000 : ℝ)^4879
        have hw : |(1299653221/2500000000 : ℝ)|=(1299653221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(698816437/1250000000 : ℝ)|^5903 ≤ (49482175905847/100000000000000 : ℝ)^4879
        have hw : |(698816437/1250000000 : ℝ)|=(698816437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173719179/2000000000 : ℝ)|^5903 ≤ (1040226289427/20000000000000 : ℝ)^4879
        have hw : |(-173719179/2000000000 : ℝ)|=(173719179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s0_7 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3969966517/10000000000 : ℝ)*x 0 + (503229369/1000000000 : ℝ)*x 1 + (1522721143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3969966517/10000000000 : ℝ)^5903 ≤ (3270247319787/10000000000000 : ℝ)^4879 := by
    have hnat : (3969966517 : ℕ)^5903*10000000000000^4879 ≤ 3270247319787^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3969966517 10000000000 3270247319787 10000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503229369/1000000000 : ℝ)^5903 ≤ (21784264595221/50000000000000 : ℝ)^4879 := by
    have hnat : (503229369 : ℕ)^5903*50000000000000^4879 ≤ 21784264595221^4879*1000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503229369 1000000000 21784264595221 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1522721143/5000000000 : ℝ)^5903 ≤ (5932249399833/25000000000000 : ℝ)^4879 := by
    have hnat : (1522721143 : ℕ)^5903*25000000000000^4879 ≤ 5932249399833^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522721143 5000000000 5932249399833 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3969966517/10000000000 : ℝ), (503229369/1000000000 : ℝ), (1522721143/5000000000 : ℝ)] ![(3270247319787/10000000000000 : ℝ), (21784264595221/50000000000000 : ℝ), (5932249399833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3969966517/10000000000 : ℝ)|^5903 ≤ (3270247319787/10000000000000 : ℝ)^4879
        have hw : |(3969966517/10000000000 : ℝ)|=(3969966517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503229369/1000000000 : ℝ)|^5903 ≤ (21784264595221/50000000000000 : ℝ)^4879
        have hw : |(503229369/1000000000 : ℝ)|=(503229369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1522721143/5000000000 : ℝ)|^5903 ≤ (5932249399833/25000000000000 : ℝ)^4879
        have hw : |(1522721143/5000000000 : ℝ)|=(1522721143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1758_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (7031/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10199/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5887/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5887 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5887*1^1024 ≤ 0^1024*1^5887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5887/1024 : ℝ) ≤ (257752904447667401/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5887 ≤ (257752904447667401/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5887*50000000000000000000^1024 ≤ 257752904447667401^1024*5^5887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 257752904447667401 50000000000000000000 5887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (257752904447667401/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5887 := by
      have hnat : (1 : ℕ)^1024*1^5887 ≤ 1^5887*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50257752904447667401/50000000000000000000 : ℝ) ≤ (2001789561784969/2000000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (50257752904447667401/50000000000000000000 : ℝ)^1024 ≤ (2001789561784969/2000000000000000 : ℝ)^5887 := by
      have hnat : (50257752904447667401 : ℕ)^1024*2000000000000000^5887 ≤ 2001789561784969^5887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50257752904447667401 50000000000000000000 2001789561784969 2000000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001789561784969/2000000000000000 : ℝ)) (X := (50257752904447667401/50000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25257752904447667401/25000000000000000000 : ℝ) ≤ (1001789561784969/1000000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (25257752904447667401/25000000000000000000 : ℝ)^1024 ≤ (1001789561784969/1000000000000000 : ℝ)^5887 := by
      have hnat : (25257752904447667401 : ℕ)^1024*1000000000000000^5887 ≤ 1001789561784969^5887*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25257752904447667401 25000000000000000000 1001789561784969 1000000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001789561784969/1000000000000000 : ℝ)) (X := (25257752904447667401/25000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1789561784969/800000000000000 : ℝ)*(0 : ℝ))^(5887/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1789561784969/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(257752904447667401/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1789561784969/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5887/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1789561784969/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2001789561784969/2000000000000000 : ℝ) by norm_num, show 1+(257752904447667401/50000000000000000000 : ℝ)+(0 : ℝ)=(50257752904447667401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(257752904447667401/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1789561784969/800000000000000 : ℝ)*(2/5 : ℝ))^(5887/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1789561784969/800000000000000 : ℝ)*(2/5 : ℝ)=(1001789561784969/1000000000000000 : ℝ) by norm_num, show 1+2*(257752904447667401/50000000000000000000 : ℝ)=(25257752904447667401/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1789561784969/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1789561784969/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1789561784969/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1789561784969/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1789561784969/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1789561784969/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1139866011/10000000000 : ℝ)*X 0 0+(2803276493/5000000000 : ℝ)*X 0 1+(4989440541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340663333/2500000000 : ℝ)*X 1 0+(-91855479/625000000 : ℝ)*X 1 1+(249472059/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681328353/5000000000 : ℝ)*X 2 0+(7795999/15625000 : ℝ)*X 2 1+(-1469685589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((991467089/2500000000 : ℝ)*X 0 0+(186942483/625000000 : ℝ)*X 0 1+(5084966697/10000000000 : ℝ)*X 0 2+(991467089/2500000000 : ℝ)*X 1 0+(186942483/625000000 : ℝ)*X 1 1+(5084966697/10000000000 : ℝ)*X 1 2+(991467089/2500000000 : ℝ)*X 2 0+(186942483/625000000 : ℝ)*X 2 1+(5084966697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-228214669/2000000000 : ℝ)*X 0 0+(312810219/625000000 : ℝ)*X 0 1+(5590531263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1039722717/2000000000 : ℝ)*X 1 0+(-108574401/1250000000 : ℝ)*X 1 1+(5590531271/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1299653221/2500000000 : ℝ)*X 2 0+(698816437/1250000000 : ℝ)*X 2 1+(-173719179/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3969966517/10000000000 : ℝ)*X 0 0+(503229369/1000000000 : ℝ)*X 0 1+(1522721143/5000000000 : ℝ)*X 0 2+(3969966517/10000000000 : ℝ)*X 1 0+(503229369/1000000000 : ℝ)*X 1 1+(1522721143/5000000000 : ℝ)*X 1 2+(3969966517/10000000000 : ℝ)*X 2 0+(503229369/1000000000 : ℝ)*X 2 1+(1522721143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13447210351212083311071/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (751361483/100000000000000 : ℝ)*(base19) + (262156901/20000000000000 : ℝ)*(base23) + (103436843/50000000000000 : ℝ)*(base24) + (27160803/20000000000000 : ℝ)*(upper4) + (297458427/100000000000000 : ℝ)*(upper5) + (65563865428053/6250000000000 : ℝ)*(major0) + (65563865428053/6250000000000 : ℝ)*(major1) + (65563865428053/6250000000000 : ℝ)*(major2) + (810225536183459/50000000000000 : ℝ)*(sp0) + (202557288355661/12500000000000 : ℝ)*(sp1) + (81022877027429/5000000000000 : ℝ)*(sp2) + (95516532736763/20000000000000 : ℝ)*(sp3) + (7985839853/100000000000000 : ℝ)*(sp4) + (1792510967/100000000000000 : ℝ)*(sp7) + (238792228097391/50000000000000 : ℝ)*(f.failure) + (1620459058206771/100000000000000 : ℝ)*(f.sum) + (656842904643/2500000000000000000000000000 : ℝ)*base66 + (874213285357/5000000000000000000000000000 : ℝ)*base67 + (29352606634643/5000000000000000000000000000 : ℝ)*base70 + (29888322139643/5000000000000000000000000000 : ℝ)*base72 + (11815993040357/2500000000000000000000000000 : ℝ)*base73 + (33512170949643/5000000000000000000000000000 : ℝ)*base76 + (16658711459643/5000000000000000000000000000 : ℝ)*base78 + (8075120414643/5000000000000000000000000000 : ℝ)*base80 + (2703311342857/2500000000000000000000000000 : ℝ)*base81 + (20095701/5000000000000000000000 : ℝ)*base90 + (20095701/5000000000000000000000 : ℝ)*base92 + (20095701/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35363381800387807159563/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1185851513/100000000000000 : ℝ)*(base19) + (65348077/6250000000000 : ℝ)*(base23) + (34251933/50000000000000 : ℝ)*(upper2) + (202312837/100000000000000 : ℝ)*(upper3) + (167042213/100000000000000 : ℝ)*(upper5) + (552762920237791/50000000000000 : ℝ)*(major0) + (552762920237791/50000000000000 : ℝ)*(major1) + (552762920237791/50000000000000 : ℝ)*(major2) + (5356116799/100000000000000 : ℝ)*(sp1) + (2016019037/50000000000000 : ℝ)*(sp2) + (1707742734073319/100000000000000 : ℝ)*(sp4) + (1707736192105007/100000000000000 : ℝ)*(sp5) + (1707737656466013/100000000000000 : ℝ)*(sp6) + (15728400906247/3125000000000 : ℝ)*(sp7) + (15728400906247/3125000000000 : ℝ)*(f.failure) + (1707742734073319/100000000000000 : ℝ)*(f.sum) + (20443243303479/20000000000000000000000000000 : ℝ)*base65 + (292362331876521/40000000000000000000000000000 : ℝ)*base68 + (60827391923479/40000000000000000000000000000 : ℝ)*base69 + (4177540323479/40000000000000000000000000000 : ℝ)*base71 + (41030745796521/20000000000000000000000000000 : ℝ)*base74 + (1808000876521/40000000000000000000000000000 : ℝ)*base76 + (20253885403479/40000000000000000000000000000 : ℝ)*base77 + (15274135643479/40000000000000000000000000000 : ℝ)*base79 + (18723723103479/20000000000000000000000000000 : ℝ)*base81 + (173517/312500000000000000000 : ℝ)*base90 + (173517/312500000000000000000 : ℝ)*base92 + (173517/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1758_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7031/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10199/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1758_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1758_s1_0 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-47130333/400000000 : ℝ)*x 0 + (5488782521/10000000000 : ℝ)*x 1 + (5081423213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47130333/400000000 : ℝ)^5903 ≤ (47010335909/625000000000 : ℝ)^4879 := by
    have hnat : (47130333 : ℕ)^5903*625000000000^4879 ≤ 47010335909^4879*400000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47130333 400000000 47010335909 625000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488782521/10000000000 : ℝ)^5903 ≤ (24197332752373/50000000000000 : ℝ)^4879 := by
    have hnat : (5488782521 : ℕ)^5903*50000000000000^4879 ≤ 24197332752373^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488782521 10000000000 24197332752373 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5081423213/10000000000 : ℝ)^5903 ≤ (44083680734071/100000000000000 : ℝ)^4879 := by
    have hnat : (5081423213 : ℕ)^5903*100000000000000^4879 ≤ 44083680734071^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081423213 10000000000 44083680734071 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47130333/400000000 : ℝ), (5488782521/10000000000 : ℝ), (5081423213/10000000000 : ℝ)] ![(47010335909/625000000000 : ℝ), (24197332752373/50000000000000 : ℝ), (44083680734071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47130333/400000000 : ℝ)|^5903 ≤ (47010335909/625000000000 : ℝ)^4879
        have hw : |(-47130333/400000000 : ℝ)|=(47130333/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488782521/10000000000 : ℝ)|^5903 ≤ (24197332752373/50000000000000 : ℝ)^4879
        have hw : |(5488782521/10000000000 : ℝ)|=(5488782521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5081423213/10000000000 : ℝ)|^5903 ≤ (44083680734071/100000000000000 : ℝ)^4879
        have hw : |(5081423213/10000000000 : ℝ)|=(5081423213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s1_1 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5331367987/10000000000 : ℝ)*x 0 + (-1391155929/10000000000 : ℝ)*x 1 + (5081424091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5331367987/10000000000 : ℝ)^5903 ≤ (11680133846633/25000000000000 : ℝ)^4879 := by
    have hnat : (5331367987 : ℕ)^5903*25000000000000^4879 ≤ 11680133846633^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5331367987 10000000000 11680133846633 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1391155929/10000000000 : ℝ)^5903 ≤ (91957746467/1000000000000 : ℝ)^4879 := by
    have hnat : (1391155929 : ℕ)^5903*1000000000000^4879 ≤ 91957746467^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391155929 10000000000 91957746467 1000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5081424091/10000000000 : ℝ)^5903 ≤ (8816737989957/20000000000000 : ℝ)^4879 := by
    have hnat : (5081424091 : ℕ)^5903*20000000000000^4879 ≤ 8816737989957^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081424091 10000000000 8816737989957 20000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5331367987/10000000000 : ℝ), (-1391155929/10000000000 : ℝ), (5081424091/10000000000 : ℝ)] ![(11680133846633/25000000000000 : ℝ), (91957746467/1000000000000 : ℝ), (8816737989957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5331367987/10000000000 : ℝ)|^5903 ≤ (11680133846633/25000000000000 : ℝ)^4879
        have hw : |(5331367987/10000000000 : ℝ)|=(5331367987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1391155929/10000000000 : ℝ)|^5903 ≤ (91957746467/1000000000000 : ℝ)^4879
        have hw : |(-1391155929/10000000000 : ℝ)|=(1391155929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5081424091/10000000000 : ℝ)|^5903 ≤ (8816737989957/20000000000000 : ℝ)^4879
        have hw : |(5081424091/10000000000 : ℝ)|=(5081424091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s1_2 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5331370231/10000000000 : ℝ)*x 0 + (1270355443/2500000000 : ℝ)*x 1 + (-695577999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5331370231/10000000000 : ℝ)^5903 ≤ (23360279589349/50000000000000 : ℝ)^4879 := by
    have hnat : (5331370231 : ℕ)^5903*50000000000000^4879 ≤ 23360279589349^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5331370231 10000000000 23360279589349 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270355443/2500000000 : ℝ)^5903 ≤ (22041832804483/50000000000000 : ℝ)^4879 := by
    have hnat : (1270355443 : ℕ)^5903*50000000000000^4879 ≤ 22041832804483^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270355443 2500000000 22041832804483 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695577999/5000000000 : ℝ)^5903 ≤ (143683987477/1562500000000 : ℝ)^4879 := by
    have hnat : (695577999 : ℕ)^5903*1562500000000^4879 ≤ 143683987477^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695577999 5000000000 143683987477 1562500000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5331370231/10000000000 : ℝ), (1270355443/2500000000 : ℝ), (-695577999/5000000000 : ℝ)] ![(23360279589349/50000000000000 : ℝ), (22041832804483/50000000000000 : ℝ), (143683987477/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5331370231/10000000000 : ℝ)|^5903 ≤ (23360279589349/50000000000000 : ℝ)^4879
        have hw : |(5331370231/10000000000 : ℝ)|=(5331370231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270355443/2500000000 : ℝ)|^5903 ≤ (22041832804483/50000000000000 : ℝ)^4879
        have hw : |(1270355443/2500000000 : ℝ)|=(1270355443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-695577999/5000000000 : ℝ)|^5903 ≤ (143683987477/1562500000000 : ℝ)^4879
        have hw : |(-695577999/5000000000 : ℝ)|=(695577999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s1_3 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4003991177/10000000000 : ℝ)*x 0 + (3344176819/10000000000 : ℝ)*x 1 + (590795067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4003991177/10000000000 : ℝ)^5903 ≤ (3304187884111/10000000000000 : ℝ)^4879 := by
    have hnat : (4003991177 : ℕ)^5903*10000000000000^4879 ≤ 3304187884111^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003991177 10000000000 3304187884111 10000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3344176819/10000000000 : ℝ)^5903 ≤ (2657342276299/10000000000000 : ℝ)^4879 := by
    have hnat : (3344176819 : ℕ)^5903*10000000000000^4879 ≤ 2657342276299^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3344176819 10000000000 2657342276299 10000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (590795067/1250000000 : ℝ)^5903 ≤ (40384698381659/100000000000000 : ℝ)^4879 := by
    have hnat : (590795067 : ℕ)^5903*100000000000000^4879 ≤ 40384698381659^4879*1250000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590795067 1250000000 40384698381659 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4003991177/10000000000 : ℝ), (3344176819/10000000000 : ℝ), (590795067/1250000000 : ℝ)] ![(3304187884111/10000000000000 : ℝ), (2657342276299/10000000000000 : ℝ), (40384698381659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4003991177/10000000000 : ℝ)|^5903 ≤ (3304187884111/10000000000000 : ℝ)^4879
        have hw : |(4003991177/10000000000 : ℝ)|=(4003991177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3344176819/10000000000 : ℝ)|^5903 ≤ (2657342276299/10000000000000 : ℝ)^4879
        have hw : |(3344176819/10000000000 : ℝ)|=(3344176819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(590795067/1250000000 : ℝ)|^5903 ≤ (40384698381659/100000000000000 : ℝ)^4879
        have hw : |(590795067/1250000000 : ℝ)|=(590795067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s1_4 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1178603377/10000000000 : ℝ)*x 0 + (1017640929/2000000000 : ℝ)*x 1 + (2740929139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178603377/10000000000 : ℝ)^5903 ≤ (1881079710087/25000000000000 : ℝ)^4879 := by
    have hnat : (1178603377 : ℕ)^5903*25000000000000^4879 ≤ 1881079710087^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178603377 10000000000 1881079710087 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017640929/2000000000 : ℝ)^5903 ≤ (22077435175323/50000000000000 : ℝ)^4879 := by
    have hnat : (1017640929 : ℕ)^5903*50000000000000^4879 ≤ 22077435175323^4879*2000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017640929 2000000000 22077435175323 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740929139/5000000000 : ℝ)^5903 ≤ (12080202697787/25000000000000 : ℝ)^4879 := by
    have hnat : (2740929139 : ℕ)^5903*25000000000000^4879 ≤ 12080202697787^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740929139 5000000000 12080202697787 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1178603377/10000000000 : ℝ), (1017640929/2000000000 : ℝ), (2740929139/5000000000 : ℝ)] ![(1881079710087/25000000000000 : ℝ), (22077435175323/50000000000000 : ℝ), (12080202697787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1178603377/10000000000 : ℝ)|^5903 ≤ (1881079710087/25000000000000 : ℝ)^4879
        have hw : |(-1178603377/10000000000 : ℝ)|=(1178603377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1017640929/2000000000 : ℝ)|^5903 ≤ (22077435175323/50000000000000 : ℝ)^4879
        have hw : |(1017640929/2000000000 : ℝ)|=(1017640929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740929139/5000000000 : ℝ)|^5903 ≤ (12080202697787/25000000000000 : ℝ)^4879
        have hw : |(2740929139/5000000000 : ℝ)|=(2740929139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s1_5 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5223632041/10000000000 : ℝ)*x 0 + (-198144241/2000000000 : ℝ)*x 1 + (1370464597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223632041/10000000000 : ℝ)^5903 ≤ (45580692900189/100000000000000 : ℝ)^4879 := by
    have hnat : (5223632041 : ℕ)^5903*100000000000000^4879 ≤ 45580692900189^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223632041 10000000000 45580692900189 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198144241/2000000000 : ℝ)^5903 ≤ (6098495123051/100000000000000 : ℝ)^4879 := by
    have hnat : (198144241 : ℕ)^5903*100000000000000^4879 ≤ 6098495123051^4879*2000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198144241 2000000000 6098495123051 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370464597/2500000000 : ℝ)^5903 ≤ (6040101495533/12500000000000 : ℝ)^4879 := by
    have hnat : (1370464597 : ℕ)^5903*12500000000000^4879 ≤ 6040101495533^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370464597 2500000000 6040101495533 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223632041/10000000000 : ℝ), (-198144241/2000000000 : ℝ), (1370464597/2500000000 : ℝ)] ![(45580692900189/100000000000000 : ℝ), (6098495123051/100000000000000 : ℝ), (6040101495533/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223632041/10000000000 : ℝ)|^5903 ≤ (45580692900189/100000000000000 : ℝ)^4879
        have hw : |(5223632041/10000000000 : ℝ)|=(5223632041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198144241/2000000000 : ℝ)|^5903 ≤ (6098495123051/100000000000000 : ℝ)^4879
        have hw : |(-198144241/2000000000 : ℝ)|=(198144241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370464597/2500000000 : ℝ)|^5903 ≤ (6040101495533/12500000000000 : ℝ)^4879
        have hw : |(1370464597/2500000000 : ℝ)|=(1370464597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s1_6 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5223631749/10000000000 : ℝ)*x 0 + (2740929449/5000000000 : ℝ)*x 1 + (-990720889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223631749/10000000000 : ℝ)^5903 ≤ (11395172454369/25000000000000 : ℝ)^4879 := by
    have hnat : (5223631749 : ℕ)^5903*25000000000000^4879 ≤ 11395172454369^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223631749 10000000000 11395172454369 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2740929449/5000000000 : ℝ)^5903 ≤ (24160408701629/50000000000000 : ℝ)^4879 := by
    have hnat : (2740929449 : ℕ)^5903*50000000000000^4879 ≤ 24160408701629^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740929449 5000000000 24160408701629 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (990720889/10000000000 : ℝ)^5903 ≤ (3049246384813/50000000000000 : ℝ)^4879 := by
    have hnat : (990720889 : ℕ)^5903*50000000000000^4879 ≤ 3049246384813^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990720889 10000000000 3049246384813 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223631749/10000000000 : ℝ), (2740929449/5000000000 : ℝ), (-990720889/10000000000 : ℝ)] ![(11395172454369/25000000000000 : ℝ), (24160408701629/50000000000000 : ℝ), (3049246384813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223631749/10000000000 : ℝ)|^5903 ≤ (11395172454369/25000000000000 : ℝ)^4879
        have hw : |(5223631749/10000000000 : ℝ)|=(5223631749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2740929449/5000000000 : ℝ)|^5903 ≤ (24160408701629/50000000000000 : ℝ)^4879
        have hw : |(2740929449/5000000000 : ℝ)|=(2740929449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-990720889/10000000000 : ℝ)|^5903 ≤ (3049246384813/50000000000000 : ℝ)^4879
        have hw : |(-990720889/10000000000 : ℝ)|=(990720889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s1_7 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (125161303/312500000 : ℝ)*x 0 + (2351676787/5000000000 : ℝ)*x 1 + (1683835371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125161303/312500000 : ℝ)^5903 ≤ (16526782951949/50000000000000 : ℝ)^4879 := by
    have hnat : (125161303 : ℕ)^5903*50000000000000^4879 ≤ 16526782951949^4879*312500000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125161303 312500000 16526782951949 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2351676787/5000000000 : ℝ)^5903 ≤ (40146976561701/100000000000000 : ℝ)^4879 := by
    have hnat : (2351676787 : ℕ)^5903*100000000000000^4879 ≤ 40146976561701^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351676787 5000000000 40146976561701 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1683835371/5000000000 : ℝ)^5903 ≤ (6699864381883/25000000000000 : ℝ)^4879 := by
    have hnat : (1683835371 : ℕ)^5903*25000000000000^4879 ≤ 6699864381883^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683835371 5000000000 6699864381883 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(125161303/312500000 : ℝ), (2351676787/5000000000 : ℝ), (1683835371/5000000000 : ℝ)] ![(16526782951949/50000000000000 : ℝ), (40146976561701/100000000000000 : ℝ), (6699864381883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(125161303/312500000 : ℝ)|^5903 ≤ (16526782951949/50000000000000 : ℝ)^4879
        have hw : |(125161303/312500000 : ℝ)|=(125161303/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2351676787/5000000000 : ℝ)|^5903 ≤ (40146976561701/100000000000000 : ℝ)^4879
        have hw : |(2351676787/5000000000 : ℝ)|=(2351676787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1683835371/5000000000 : ℝ)|^5903 ≤ (6699864381883/25000000000000 : ℝ)^4879
        have hw : |(1683835371/5000000000 : ℝ)|=(1683835371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1758_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10199/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7031/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4547/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1787/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10199/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7031/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10199/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7031/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10199/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7031/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10199/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7031/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10199/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7031/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10199/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7031/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7031/100000 : ℝ) ^ (5887/1024 : ℝ) ≤ (5880500370419/25000000000000000000 : ℝ) := by
    have hpowers : (7031/100000 : ℝ)^5887 ≤ (5880500370419/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7031 : ℕ)^5887*25000000000000000000^1024 ≤ 5880500370419^1024*100000^5887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 100000 5880500370419 25000000000000000000 5887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/100000 : ℝ)) (X := (5880500370419/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10199/50000 : ℝ) ^ (5887/1024 : ℝ) ≤ (5367510009994771/50000000000000000000 : ℝ) := by
    have hpowers : (10199/50000 : ℝ)^5887 ≤ (5367510009994771/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10199 : ℕ)^5887*50000000000000000000^1024 ≤ 5367510009994771^1024*50000^5887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10199 50000 5367510009994771 50000000000000000000 5887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10199/50000 : ℝ)) (X := (5367510009994771/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500005880500370419/12500000000000000000 : ℝ) ≤ (312500025571731/312500000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (12500005880500370419/12500000000000000000 : ℝ)^1024 ≤ (312500025571731/312500000000000 : ℝ)^5887 := by
      have hnat : (12500005880500370419 : ℕ)^1024*312500000000000^5887 ≤ 312500025571731^5887*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500005880500370419 12500000000000000000 312500025571731 312500000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312500025571731/312500000000000 : ℝ)) (X := (12500005880500370419/12500000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50005379271010735609/50000000000000000000 : ℝ) ≤ (5000093564273173/5000000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (50005379271010735609/50000000000000000000 : ℝ)^1024 ≤ (5000093564273173/5000000000000000 : ℝ)^5887 := by
      have hnat : (50005379271010735609 : ℕ)^1024*5000000000000000^5887 ≤ 5000093564273173^5887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005379271010735609 50000000000000000000 5000093564273173 5000000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000093564273173/5000000000000000 : ℝ)) (X := (50005379271010735609/50000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005367510009994771/25000000000000000000 : ℝ) ≤ (100003734387973/100000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (25005367510009994771/25000000000000000000 : ℝ)^1024 ≤ (100003734387973/100000000000000 : ℝ)^5887 := by
      have hnat : (25005367510009994771 : ℕ)^1024*100000000000000^5887 ≤ 100003734387973^5887*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005367510009994771 25000000000000000000 100003734387973 100000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100003734387973/100000000000000 : ℝ)) (X := (25005367510009994771/25000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5880500370419/25000000000000000000 : ℝ) ≤ ((33416847760851397429/33417500000000000000 : ℝ)+2*(93155125477/668350000000000 : ℝ)*(7031/100000 : ℝ))^(5887/1024 : ℝ) := by
    rw [show (33416847760851397429/33417500000000000000 : ℝ)+2*(93155125477/668350000000000 : ℝ)*(7031/100000 : ℝ)=(312500025571731/312500000000000 : ℝ) by norm_num, show 1+2*(5880500370419/25000000000000000000 : ℝ)=(12500005880500370419/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5367510009994771/50000000000000000000 : ℝ)+(5880500370419/25000000000000000000 : ℝ) ≤ ((33416847760851397429/33417500000000000000 : ℝ)+(93155125477/668350000000000 : ℝ)*((10199/50000 : ℝ)+(7031/100000 : ℝ)))^(5887/1024 : ℝ) := by
    rw [show (33416847760851397429/33417500000000000000 : ℝ)+(93155125477/668350000000000 : ℝ)*((10199/50000 : ℝ)+(7031/100000 : ℝ))=(5000093564273173/5000000000000000 : ℝ) by norm_num, show 1+(5367510009994771/50000000000000000000 : ℝ)+(5880500370419/25000000000000000000 : ℝ)=(50005379271010735609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5367510009994771/50000000000000000000 : ℝ) ≤ ((33416847760851397429/33417500000000000000 : ℝ)+2*(93155125477/668350000000000 : ℝ)*(10199/50000 : ℝ))^(5887/1024 : ℝ) := by
    rw [show (33416847760851397429/33417500000000000000 : ℝ)+2*(93155125477/668350000000000 : ℝ)*(10199/50000 : ℝ)=(100003734387973/100000000000000 : ℝ) by norm_num, show 1+2*(5367510009994771/50000000000000000000 : ℝ)=(25005367510009994771/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33416847760851397429/33417500000000000000 : ℝ)*(X 1 0+X 2 0)+(93155125477/668350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (7031/100000 : ℝ)) (hi := (10199/50000 : ℝ)) (c := (33416847760851397429/33417500000000000000 : ℝ)) (alpha := (93155125477/668350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33416847760851397429/33417500000000000000 : ℝ)*(X 0 1+X 2 1)+(93155125477/668350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (7031/100000 : ℝ)) (hi := (10199/50000 : ℝ)) (c := (33416847760851397429/33417500000000000000 : ℝ)) (alpha := (93155125477/668350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33416847760851397429/33417500000000000000 : ℝ)*(X 0 2+X 1 2)+(93155125477/668350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (7031/100000 : ℝ)) (hi := (10199/50000 : ℝ)) (c := (33416847760851397429/33417500000000000000 : ℝ)) (alpha := (93155125477/668350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-47130333/400000000 : ℝ)*X 0 0+(5488782521/10000000000 : ℝ)*X 0 1+(5081423213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5331367987/10000000000 : ℝ)*X 1 0+(-1391155929/10000000000 : ℝ)*X 1 1+(5081424091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5331370231/10000000000 : ℝ)*X 2 0+(1270355443/2500000000 : ℝ)*X 2 1+(-695577999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4003991177/10000000000 : ℝ)*X 0 0+(3344176819/10000000000 : ℝ)*X 0 1+(590795067/1250000000 : ℝ)*X 0 2+(4003991177/10000000000 : ℝ)*X 1 0+(3344176819/10000000000 : ℝ)*X 1 1+(590795067/1250000000 : ℝ)*X 1 2+(4003991177/10000000000 : ℝ)*X 2 0+(3344176819/10000000000 : ℝ)*X 2 1+(590795067/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1178603377/10000000000 : ℝ)*X 0 0+(1017640929/2000000000 : ℝ)*X 0 1+(2740929139/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5223632041/10000000000 : ℝ)*X 1 0+(-198144241/2000000000 : ℝ)*X 1 1+(1370464597/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5223631749/10000000000 : ℝ)*X 2 0+(2740929449/5000000000 : ℝ)*X 2 1+(-990720889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((125161303/312500000 : ℝ)*X 0 0+(2351676787/5000000000 : ℝ)*X 0 1+(1683835371/5000000000 : ℝ)*X 0 2+(125161303/312500000 : ℝ)*X 1 0+(2351676787/5000000000 : ℝ)*X 1 1+(1683835371/5000000000 : ℝ)*X 1 2+(125161303/312500000 : ℝ)*X 2 0+(2351676787/5000000000 : ℝ)*X 2 1+(1683835371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (469739400268635150016025943/208859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174758787/25000000000000 : ℝ)*(base19) + (422335493/25000000000000 : ℝ)*(base23) + (22899779/100000000000000 : ℝ)*(lower2) + (59048271/50000000000000 : ℝ)*(upper3) + (42164671/25000000000000 : ℝ)*(upper5) + (198647023015737/12500000000000 : ℝ)*(major0) + (198647023015737/12500000000000 : ℝ)*(major1) + (198647023015737/12500000000000 : ℝ)*(major2) + (613710666948013/25000000000000 : ℝ)*(sp0) + (2454852988405131/100000000000000 : ℝ)*(sp1) + (2454851998098307/100000000000000 : ℝ)*(sp2) + (361747703333383/50000000000000 : ℝ)*(sp3) + (11019648227/100000000000000 : ℝ)*(sp4) + (799793933/25000000000000 : ℝ)*(sp7) + (723498605842499/100000000000000 : ℝ)*(f.failure) + (2454853687440279/100000000000000 : ℝ)*(f.sum) + (509300069859659/66835000000000000000000000000 : ℝ)*base65 + (1638545342803196423/417718750000000000000000000000000 : ℝ)*base67 + (2344383565072227673/417718750000000000000000000000000 : ℝ)*base69 + (2248404140329008923/417718750000000000000000000000000 : ℝ)*base71 + (286318309114579/66835000000000000000000000000 : ℝ)*base73 + (1503208807065571423/417718750000000000000000000000000 : ℝ)*base75 + (4357316724499633923/417718750000000000000000000000000 : ℝ)*base77 + (1547314524759477673/417718750000000000000000000000000 : ℝ)*base79 + (233560425820947/33417500000000000000000000000 : ℝ)*base81 + (10919089/10000000000000000000000 : ℝ)*base90 + (10919089/10000000000000000000000 : ℝ)*base92 + (10919089/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8734857026861349234527108283/1670875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (686133701/100000000000000 : ℝ)*(base19) + (667060829/100000000000000 : ℝ)*(base23) + (12511041/6250000000000 : ℝ)*(upper3) + (3223077/20000000000000 : ℝ)*(lower4) + (1644491260172891/100000000000000 : ℝ)*(major0) + (1644491260172891/100000000000000 : ℝ)*(major1) + (1644491260172891/100000000000000 : ℝ)*(major2) + (688110753/20000000000000 : ℝ)*(sp1) + (7904839363/100000000000000 : ℝ)*(sp2) + (110820371/100000000000000 : ℝ)*(sp3) + (1270150320865713/50000000000000 : ℝ)*(sp4) + (2540296515043961/100000000000000 : ℝ)*(sp5) + (1270146034915617/50000000000000 : ℝ)*(sp6) + (748681593536837/100000000000000 : ℝ)*(sp7) + (748681704357209/100000000000000 : ℝ)*(f.failure) + (1270150320865713/50000000000000 : ℝ)*(f.sum) + (24093719390819/66835000000000000000000000000 : ℝ)*base65 + (1851286632036502761/3341750000000000000000000000000000 : ℝ)*base68 + (17112852946681747239/3341750000000000000000000000000000 : ℝ)*base69 + (2068323396261997239/3341750000000000000000000000000000 : ℝ)*base71 + (167105048172519/66835000000000000000000000000 : ℝ)*base73 + (28928117887364502761/3341750000000000000000000000000000 : ℝ)*base76 + (14589941974431747239/3341750000000000000000000000000000 : ℝ)*base77 + (4309705364846997239/3341750000000000000000000000000000 : ℝ)*base79 + (24779604858979/4177187500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (80455101/10000000000000000000000 : ℝ)*base89 + (80455101/10000000000000000000000 : ℝ)*base91 + (80455101/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1758_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10199/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7031/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4547/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1787/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1758_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1758_s2_0 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1178975611/10000000000 : ℝ)*x 0 + (2743236601/5000000000 : ℝ)*x 1 + (2541621101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178975611/10000000000 : ℝ)^5903 ≤ (7527194065811/100000000000000 : ℝ)^4879 := by
    have hnat : (1178975611 : ℕ)^5903*100000000000000^4879 ≤ 7527194065811^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178975611 10000000000 7527194065811 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743236601/5000000000 : ℝ)^5903 ≤ (483700318877/1000000000000 : ℝ)^4879 := by
    have hnat : (2743236601 : ℕ)^5903*1000000000000^4879 ≤ 483700318877^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743236601 5000000000 483700318877 1000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541621101/5000000000 : ℝ)^5903 ≤ (1764110961073/4000000000000 : ℝ)^4879 := by
    have hnat : (2541621101 : ℕ)^5903*4000000000000^4879 ≤ 1764110961073^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541621101 5000000000 1764110961073 4000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1178975611/10000000000 : ℝ), (2743236601/5000000000 : ℝ), (2541621101/5000000000 : ℝ)] ![(7527194065811/100000000000000 : ℝ), (483700318877/1000000000000 : ℝ), (1764110961073/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1178975611/10000000000 : ℝ)|^5903 ≤ (7527194065811/100000000000000 : ℝ)^4879
        have hw : |(-1178975611/10000000000 : ℝ)|=(1178975611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743236601/5000000000 : ℝ)|^5903 ≤ (483700318877/1000000000000 : ℝ)^4879
        have hw : |(2743236601/5000000000 : ℝ)|=(2743236601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541621101/5000000000 : ℝ)|^5903 ≤ (1764110961073/4000000000000 : ℝ)^4879
        have hw : |(2541621101/5000000000 : ℝ)|=(2541621101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s2_1 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53307239/100000000 : ℝ)*x 0 + (-1389623357/10000000000 : ℝ)*x 1 + (635405277/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53307239/100000000 : ℝ)^5903 ≤ (11678426624029/25000000000000 : ℝ)^4879 := by
    have hnat : (53307239 : ℕ)^5903*25000000000000^4879 ≤ 11678426624029^4879*100000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53307239 100000000 11678426624029 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389623357/10000000000 : ℝ)^5903 ≤ (9183519313153/100000000000000 : ℝ)^4879 := by
    have hnat : (1389623357 : ℕ)^5903*100000000000000^4879 ≤ 9183519313153^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389623357 10000000000 9183519313153 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635405277/1250000000 : ℝ)^5903 ≤ (5512846771723/12500000000000 : ℝ)^4879 := by
    have hnat : (635405277 : ℕ)^5903*12500000000000^4879 ≤ 5512846771723^4879*1250000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635405277 1250000000 5512846771723 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53307239/100000000 : ℝ), (-1389623357/10000000000 : ℝ), (635405277/1250000000 : ℝ)] ![(11678426624029/25000000000000 : ℝ), (9183519313153/100000000000000 : ℝ), (5512846771723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53307239/100000000 : ℝ)|^5903 ≤ (11678426624029/25000000000000 : ℝ)^4879
        have hw : |(53307239/100000000 : ℝ)|=(53307239/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1389623357/10000000000 : ℝ)|^5903 ≤ (9183519313153/100000000000000 : ℝ)^4879
        have hw : |(-1389623357/10000000000 : ℝ)|=(1389623357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635405277/1250000000 : ℝ)|^5903 ≤ (5512846771723/12500000000000 : ℝ)^4879
        have hw : |(635405277/1250000000 : ℝ)|=(635405277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s2_2 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1332680977/2500000000 : ℝ)*x 0 + (5083242197/10000000000 : ℝ)*x 1 + (-1389623371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1332680977/2500000000 : ℝ)^5903 ≤ (23356853290467/50000000000000 : ℝ)^4879 := by
    have hnat : (1332680977 : ℕ)^5903*50000000000000^4879 ≤ 23356853290467^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332680977 2500000000 23356853290467 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083242197/10000000000 : ℝ)^5903 ≤ (2205138698717/5000000000000 : ℝ)^4879 := by
    have hnat : (5083242197 : ℕ)^5903*5000000000000^4879 ≤ 2205138698717^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083242197 10000000000 2205138698717 5000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389623371/10000000000 : ℝ)^5903 ≤ (2295879856273/25000000000000 : ℝ)^4879 := by
    have hnat : (1389623371 : ℕ)^5903*25000000000000^4879 ≤ 2295879856273^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389623371 10000000000 2295879856273 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1332680977/2500000000 : ℝ), (5083242197/10000000000 : ℝ), (-1389623371/10000000000 : ℝ)] ![(23356853290467/50000000000000 : ℝ), (2205138698717/5000000000000 : ℝ), (2295879856273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1332680977/2500000000 : ℝ)|^5903 ≤ (23356853290467/50000000000000 : ℝ)^4879
        have hw : |(1332680977/2500000000 : ℝ)|=(1332680977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083242197/10000000000 : ℝ)|^5903 ≤ (2205138698717/5000000000000 : ℝ)^4879
        have hw : |(5083242197/10000000000 : ℝ)|=(5083242197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1389623371/10000000000 : ℝ)|^5903 ≤ (2295879856273/25000000000000 : ℝ)^4879
        have hw : |(-1389623371/10000000000 : ℝ)|=(1389623371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s2_3 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (250286259/625000000 : ℝ)*x 0 + (3351138987/10000000000 : ℝ)*x 1 + (4719314597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250286259/625000000 : ℝ)^5903 ≤ (33047759300471/100000000000000 : ℝ)^4879 := by
    have hnat : (250286259 : ℕ)^5903*100000000000000^4879 ≤ 33047759300471^4879*625000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250286259 625000000 33047759300471 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3351138987/10000000000 : ℝ)^5903 ≤ (3330046382751/12500000000000 : ℝ)^4879 := by
    have hnat : (3351138987 : ℕ)^5903*12500000000000^4879 ≤ 3330046382751^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3351138987 10000000000 3330046382751 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4719314597/10000000000 : ℝ)^5903 ≤ (40311869629851/100000000000000 : ℝ)^4879 := by
    have hnat : (4719314597 : ℕ)^5903*100000000000000^4879 ≤ 40311869629851^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4719314597 10000000000 40311869629851 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(250286259/625000000 : ℝ), (3351138987/10000000000 : ℝ), (4719314597/10000000000 : ℝ)] ![(33047759300471/100000000000000 : ℝ), (3330046382751/12500000000000 : ℝ), (40311869629851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(250286259/625000000 : ℝ)|^5903 ≤ (33047759300471/100000000000000 : ℝ)^4879
        have hw : |(250286259/625000000 : ℝ)|=(250286259/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3351138987/10000000000 : ℝ)|^5903 ≤ (3330046382751/12500000000000 : ℝ)^4879
        have hw : |(3351138987/10000000000 : ℝ)|=(3351138987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4719314597/10000000000 : ℝ)|^5903 ≤ (40311869629851/100000000000000 : ℝ)^4879
        have hw : |(4719314597/10000000000 : ℝ)|=(4719314597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s2_4 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-117931061/1000000000 : ℝ)*x 0 + (5089886411/10000000000 : ℝ)*x 1 + (1369922553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117931061/1000000000 : ℝ)^5903 ≤ (7529781842023/100000000000000 : ℝ)^4879 := by
    have hnat : (117931061 : ℕ)^5903*100000000000000^4879 ≤ 7529781842023^4879*1000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117931061 1000000000 7529781842023 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5089886411/10000000000 : ℝ)^5903 ≤ (8834505630499/20000000000000 : ℝ)^4879 := by
    have hnat : (5089886411 : ℕ)^5903*20000000000000^4879 ≤ 8834505630499^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5089886411 10000000000 8834505630499 20000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369922553/2500000000 : ℝ)^5903 ≤ (1207442249793/2500000000000 : ℝ)^4879 := by
    have hnat : (1369922553 : ℕ)^5903*2500000000000^4879 ≤ 1207442249793^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369922553 2500000000 1207442249793 2500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117931061/1000000000 : ℝ), (5089886411/10000000000 : ℝ), (1369922553/2500000000 : ℝ)] ![(7529781842023/100000000000000 : ℝ), (8834505630499/20000000000000 : ℝ), (1207442249793/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117931061/1000000000 : ℝ)|^5903 ≤ (7529781842023/100000000000000 : ℝ)^4879
        have hw : |(-117931061/1000000000 : ℝ)|=(117931061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5089886411/10000000000 : ℝ)|^5903 ≤ (8834505630499/20000000000000 : ℝ)^4879
        have hw : |(5089886411/10000000000 : ℝ)|=(5089886411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369922553/2500000000 : ℝ)|^5903 ≤ (1207442249793/2500000000000 : ℝ)^4879
        have hw : |(1369922553/2500000000 : ℝ)|=(1369922553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s2_5 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224090487/10000000000 : ℝ)*x 0 + (-993175337/10000000000 : ℝ)*x 1 + (1369922553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224090487/10000000000 : ℝ)^5903 ≤ (1139638321707/2500000000000 : ℝ)^4879 := by
    have hnat : (5224090487 : ℕ)^5903*2500000000000^4879 ≤ 1139638321707^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224090487 10000000000 1139638321707 2500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993175337/10000000000 : ℝ)^5903 ≤ (6116777131751/100000000000000 : ℝ)^4879 := by
    have hnat : (993175337 : ℕ)^5903*100000000000000^4879 ≤ 6116777131751^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993175337 10000000000 6116777131751 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369922553/2500000000 : ℝ)^5903 ≤ (1207442249793/2500000000000 : ℝ)^4879 := by
    have hnat : (1369922553 : ℕ)^5903*2500000000000^4879 ≤ 1207442249793^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369922553 2500000000 1207442249793 2500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224090487/10000000000 : ℝ), (-993175337/10000000000 : ℝ), (1369922553/2500000000 : ℝ)] ![(1139638321707/2500000000000 : ℝ), (6116777131751/100000000000000 : ℝ), (1207442249793/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224090487/10000000000 : ℝ)|^5903 ≤ (1139638321707/2500000000000 : ℝ)^4879
        have hw : |(5224090487/10000000000 : ℝ)|=(5224090487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-993175337/10000000000 : ℝ)|^5903 ≤ (6116777131751/100000000000000 : ℝ)^4879
        have hw : |(-993175337/10000000000 : ℝ)|=(993175337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369922553/2500000000 : ℝ)|^5903 ≤ (1207442249793/2500000000000 : ℝ)^4879
        have hw : |(1369922553/2500000000 : ℝ)|=(1369922553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s2_6 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612045243/5000000000 : ℝ)*x 0 + (1369922553/2500000000 : ℝ)*x 1 + (-993175337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612045243/5000000000 : ℝ)^5903 ≤ (22792766428861/50000000000000 : ℝ)^4879 := by
    have hnat : (2612045243 : ℕ)^5903*50000000000000^4879 ≤ 22792766428861^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612045243 5000000000 22792766428861 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369922553/2500000000 : ℝ)^5903 ≤ (1207442249793/2500000000000 : ℝ)^4879 := by
    have hnat : (1369922553 : ℕ)^5903*2500000000000^4879 ≤ 1207442249793^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369922553 2500000000 1207442249793 2500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (993175337/10000000000 : ℝ)^5903 ≤ (6116777131751/100000000000000 : ℝ)^4879 := by
    have hnat : (993175337 : ℕ)^5903*100000000000000^4879 ≤ 6116777131751^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993175337 10000000000 6116777131751 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612045243/5000000000 : ℝ), (1369922553/2500000000 : ℝ), (-993175337/10000000000 : ℝ)] ![(22792766428861/50000000000000 : ℝ), (1207442249793/2500000000000 : ℝ), (6116777131751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612045243/5000000000 : ℝ)|^5903 ≤ (22792766428861/50000000000000 : ℝ)^4879
        have hw : |(2612045243/5000000000 : ℝ)|=(2612045243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369922553/2500000000 : ℝ)|^5903 ≤ (1207442249793/2500000000000 : ℝ)^4879
        have hw : |(1369922553/2500000000 : ℝ)|=(1369922553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-993175337/10000000000 : ℝ)|^5903 ≤ (6116777131751/100000000000000 : ℝ)^4879
        have hw : |(-993175337/10000000000 : ℝ)|=(993175337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s2_7 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (125178649/312500000 : ℝ)*x 0 + (2348385277/5000000000 : ℝ)*x 1 + (3374153873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125178649/312500000 : ℝ)^5903 ≤ (1652955413919/5000000000000 : ℝ)^4879 := by
    have hnat : (125178649 : ℕ)^5903*5000000000000^4879 ≤ 1652955413919^4879*312500000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125178649 312500000 1652955413919 5000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2348385277/5000000000 : ℝ)^5903 ≤ (40079001667613/100000000000000 : ℝ)^4879 := by
    have hnat : (2348385277 : ℕ)^5903*100000000000000^4879 ≤ 40079001667613^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348385277 5000000000 40079001667613 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3374153873/10000000000 : ℝ)^5903 ≤ (26861890041713/100000000000000 : ℝ)^4879 := by
    have hnat : (3374153873 : ℕ)^5903*100000000000000^4879 ≤ 26861890041713^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374153873 10000000000 26861890041713 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(125178649/312500000 : ℝ), (2348385277/5000000000 : ℝ), (3374153873/10000000000 : ℝ)] ![(1652955413919/5000000000000 : ℝ), (40079001667613/100000000000000 : ℝ), (26861890041713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(125178649/312500000 : ℝ)|^5903 ≤ (1652955413919/5000000000000 : ℝ)^4879
        have hw : |(125178649/312500000 : ℝ)|=(125178649/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2348385277/5000000000 : ℝ)|^5903 ≤ (40079001667613/100000000000000 : ℝ)^4879
        have hw : |(2348385277/5000000000 : ℝ)|=(2348385277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3374153873/10000000000 : ℝ)|^5903 ≤ (26861890041713/100000000000000 : ℝ)^4879
        have hw : |(3374153873/10000000000 : ℝ)|=(3374153873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1758_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1787/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4547/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4567/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17821/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1787/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4547/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1787/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4547/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1787/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4547/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1787/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4547/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1787/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4547/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1787/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4547/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4547/50000 : ℝ) ^ (5887/1024 : ℝ) ≤ (103242331274737/100000000000000000000 : ℝ) := by
    have hpowers : (4547/50000 : ℝ)^5887 ≤ (103242331274737/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4547 : ℕ)^5887*100000000000000000000^1024 ≤ 103242331274737^1024*50000^5887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4547 50000 103242331274737 100000000000000000000 5887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4547/50000 : ℝ)) (X := (103242331274737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1787/10000 : ℝ) ^ (5887/1024 : ℝ) ≤ (31356424941879/625000000000000000 : ℝ) := by
    have hpowers : (1787/10000 : ℝ)^5887 ≤ (31356424941879/625000000000000000 : ℝ)^1024 := by
      have hnat : (1787 : ℕ)^5887*625000000000000000^1024 ≤ 31356424941879^1024*10000^5887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1787 10000 31356424941879 625000000000000000 5887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1787/10000 : ℝ)) (X := (31356424941879/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000103242331274737/50000000000000000000 : ℝ) ≤ (10000003591644541/10000000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (50000103242331274737/50000000000000000000 : ℝ)^1024 ≤ (10000003591644541/10000000000000000 : ℝ)^5887 := by
      have hnat : (50000103242331274737 : ℕ)^1024*10000000000000000^5887 ≤ 10000003591644541^5887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000103242331274737 50000000000000000000 10000003591644541 10000000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000003591644541/10000000000000000 : ℝ)) (X := (50000103242331274737/50000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100005120270321975377/100000000000000000000 : ℝ) ≤ (2000017812284457/2000000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (100005120270321975377/100000000000000000000 : ℝ)^1024 ≤ (2000017812284457/2000000000000000 : ℝ)^5887 := by
      have hnat : (100005120270321975377 : ℕ)^1024*2000000000000000^5887 ≤ 2000017812284457^5887*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100005120270321975377 100000000000000000000 2000017812284457 2000000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000017812284457/2000000000000000 : ℝ)) (X := (100005120270321975377/100000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312531356424941879/312500000000000000 : ℝ) ≤ (10000174531200029/10000000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (312531356424941879/312500000000000000 : ℝ)^1024 ≤ (10000174531200029/10000000000000000 : ℝ)^5887 := by
      have hnat : (312531356424941879 : ℕ)^1024*10000000000000000^5887 ≤ 10000174531200029^5887*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312531356424941879 312500000000000000 10000174531200029 10000000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000174531200029/10000000000000000 : ℝ)) (X := (312531356424941879/312500000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(103242331274737/100000000000000000000 : ℝ) ≤ ((10969809624494360493/10970000000000000000 : ℝ)+2*(5341861109/54850000000000 : ℝ)*(4547/50000 : ℝ))^(5887/1024 : ℝ) := by
    rw [show (10969809624494360493/10970000000000000000 : ℝ)+2*(5341861109/54850000000000 : ℝ)*(4547/50000 : ℝ)=(10000003591644541/10000000000000000 : ℝ) by norm_num, show 1+2*(103242331274737/100000000000000000000 : ℝ)=(50000103242331274737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31356424941879/625000000000000000 : ℝ)+(103242331274737/100000000000000000000 : ℝ) ≤ ((10969809624494360493/10970000000000000000 : ℝ)+(5341861109/54850000000000 : ℝ)*((1787/10000 : ℝ)+(4547/50000 : ℝ)))^(5887/1024 : ℝ) := by
    rw [show (10969809624494360493/10970000000000000000 : ℝ)+(5341861109/54850000000000 : ℝ)*((1787/10000 : ℝ)+(4547/50000 : ℝ))=(2000017812284457/2000000000000000 : ℝ) by norm_num, show 1+(31356424941879/625000000000000000 : ℝ)+(103242331274737/100000000000000000000 : ℝ)=(100005120270321975377/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31356424941879/625000000000000000 : ℝ) ≤ ((10969809624494360493/10970000000000000000 : ℝ)+2*(5341861109/54850000000000 : ℝ)*(1787/10000 : ℝ))^(5887/1024 : ℝ) := by
    rw [show (10969809624494360493/10970000000000000000 : ℝ)+2*(5341861109/54850000000000 : ℝ)*(1787/10000 : ℝ)=(10000174531200029/10000000000000000 : ℝ) by norm_num, show 1+2*(31356424941879/625000000000000000 : ℝ)=(312531356424941879/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10969809624494360493/10970000000000000000 : ℝ)*(X 1 0+X 2 0)+(5341861109/54850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (4547/50000 : ℝ)) (hi := (1787/10000 : ℝ)) (c := (10969809624494360493/10970000000000000000 : ℝ)) (alpha := (5341861109/54850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10969809624494360493/10970000000000000000 : ℝ)*(X 0 1+X 2 1)+(5341861109/54850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (4547/50000 : ℝ)) (hi := (1787/10000 : ℝ)) (c := (10969809624494360493/10970000000000000000 : ℝ)) (alpha := (5341861109/54850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10969809624494360493/10970000000000000000 : ℝ)*(X 0 2+X 1 2)+(5341861109/54850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (4547/50000 : ℝ)) (hi := (1787/10000 : ℝ)) (c := (10969809624494360493/10970000000000000000 : ℝ)) (alpha := (5341861109/54850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1178975611/10000000000 : ℝ)*X 0 0+(2743236601/5000000000 : ℝ)*X 0 1+(2541621101/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53307239/100000000 : ℝ)*X 1 0+(-1389623357/10000000000 : ℝ)*X 1 1+(635405277/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1332680977/2500000000 : ℝ)*X 2 0+(5083242197/10000000000 : ℝ)*X 2 1+(-1389623371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((250286259/625000000 : ℝ)*X 0 0+(3351138987/10000000000 : ℝ)*X 0 1+(4719314597/10000000000 : ℝ)*X 0 2+(250286259/625000000 : ℝ)*X 1 0+(3351138987/10000000000 : ℝ)*X 1 1+(4719314597/10000000000 : ℝ)*X 1 2+(250286259/625000000 : ℝ)*X 2 0+(3351138987/10000000000 : ℝ)*X 2 1+(4719314597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-117931061/1000000000 : ℝ)*X 0 0+(5089886411/10000000000 : ℝ)*X 0 1+(1369922553/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5224090487/10000000000 : ℝ)*X 1 0+(-993175337/10000000000 : ℝ)*X 1 1+(1369922553/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2612045243/5000000000 : ℝ)*X 2 0+(1369922553/2500000000 : ℝ)*X 2 1+(-993175337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((125178649/312500000 : ℝ)*X 0 0+(2348385277/5000000000 : ℝ)*X 0 1+(3374153873/10000000000 : ℝ)*X 0 2+(125178649/312500000 : ℝ)*X 1 0+(2348385277/5000000000 : ℝ)*X 1 1+(3374153873/10000000000 : ℝ)*X 1 2+(125178649/312500000 : ℝ)*X 2 0+(2348385277/5000000000 : ℝ)*X 2 1+(3374153873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1202658076000511401268598801/137125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (582901437/50000000000000 : ℝ)*(base19) + (549751623/50000000000000 : ℝ)*(base23) + (3732649/10000000000000 : ℝ)*(lower2) + (212581581/100000000000000 : ℝ)*(upper3) + (155841591/100000000000000 : ℝ)*(upper5) + (401361597283319/25000000000000 : ℝ)*(major0) + (401361597283319/25000000000000 : ℝ)*(major1) + (401361597283319/25000000000000 : ℝ)*(major2) + (619994354449839/25000000000000 : ℝ)*(sp0) + (1239992717866871/50000000000000 : ℝ)*(sp1) + (247998550203337/10000000000000 : ℝ)*(sp2) + (182725723660503/25000000000000 : ℝ)*(sp3) + (459186863/5000000000000 : ℝ)*(sp4) + (747434281/25000000000000 : ℝ)*(sp7) + (356887638857/48828125000 : ℝ)*(f.failure) + (309998325192077/12500000000000 : ℝ)*(f.sum) + (2845656807957/1371250000000000000000000000 : ℝ)*base65 + (832635122370283733/274250000000000000000000000000000 : ℝ)*base68 + (786136346418283733/274250000000000000000000000000000 : ℝ)*base70 + (316699141734283733/274250000000000000000000000000000 : ℝ)*base72 + (2585468561429/2742500000000000000000000000 : ℝ)*base73 + (124173111011716267/274250000000000000000000000000000 : ℝ)*base75 + (901800146385716267/274250000000000000000000000000000 : ℝ)*base77 + (643644543231783733/274250000000000000000000000000000 : ℝ)*base80 + (3038849062679/2742500000000000000000000000 : ℝ)*base81 + (96829/9765625000000000000 : ℝ)*base90 + (96829/9765625000000000000 : ℝ)*base92 + (96829/9765625000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (447596441296538545645958799/54850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1039281389/100000000000000 : ℝ)*(base19) + (1111013753/100000000000000 : ℝ)*(base23) + (36650739/12500000000000 : ℝ)*(lower1) + (17658147/10000000000000 : ℝ)*(upper3) + (16055351/50000000000000 : ℝ)*(lower4) + (34060863/20000000000000 : ℝ)*(upper5) + (332146012778919/20000000000000 : ℝ)*(major0) + (332146012778919/20000000000000 : ℝ)*(major1) + (332146012778919/20000000000000 : ℝ)*(major2) + (105397959/20000000000000 : ℝ)*(sp2) + (2565385168834891/100000000000000 : ℝ)*(sp4) + (1282692064776751/50000000000000 : ℝ)*(sp5) + (1282691765415671/50000000000000 : ℝ)*(sp6) + (756074686941871/100000000000000 : ℝ)*(sp7) + (756074686941871/100000000000000 : ℝ)*(f.failure) + (2565385168834891/100000000000000 : ℝ)*(f.sum) + (1499693134801/274250000000000000000000000 : ℝ)*base66 + (582220476872047067/219400000000000000000000000000000 : ℝ)*base67 + (1860210000396047067/219400000000000000000000000000000 : ℝ)*base69 + (253450527532247067/219400000000000000000000000000000 : ℝ)*base71 + (1387194792711/548500000000000000000000000 : ℝ)*base73 + (1470926055324752933/219400000000000000000000000000000 : ℝ)*base76 + (1232940853331047067/219400000000000000000000000000000 : ℝ)*base77 + (1479777557662847067/219400000000000000000000000000000 : ℝ)*base79 + (1988778182253/548500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (15783019/10000000000000000000000 : ℝ)*base89 + (15783019/10000000000000000000000 : ℝ)*base91 + (15783019/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1758_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1787/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4547/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4567/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17821/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1758_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1758_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4567/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17821/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1758_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1758_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1758_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4567/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17821/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1758_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
