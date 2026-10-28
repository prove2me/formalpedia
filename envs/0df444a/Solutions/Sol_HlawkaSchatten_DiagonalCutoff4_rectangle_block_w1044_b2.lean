-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1044_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:49:58.129931+00:00
-- url     : https://prove2.me/submissions/8a2bb25d-6429-4a95-899e-64b2bee0a1be

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
theorem support_rectangle_w1044_s6_0 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-553648431/2500000000 : ℝ)*x 0 + (33721077/62500000 : ℝ)*x 1 + (328965179/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553648431/2500000000 : ℝ)^8237 ≤ (13447623279783/100000000000000 : ℝ)^6189 := by
    have hnat : (553648431 : ℕ)^8237*100000000000000^6189 ≤ 13447623279783^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553648431 2500000000 13447623279783 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33721077/62500000 : ℝ)^8237 ≤ (43989063239359/100000000000000 : ℝ)^6189 := by
    have hnat : (33721077 : ℕ)^8237*100000000000000^6189 ≤ 43989063239359^6189*62500000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33721077 62500000 43989063239359 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328965179/625000000 : ℝ)^8237 ≤ (5320414181981/12500000000000 : ℝ)^6189 := by
    have hnat : (328965179 : ℕ)^8237*12500000000000^6189 ≤ 5320414181981^6189*625000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328965179 625000000 5320414181981 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553648431/2500000000 : ℝ), (33721077/62500000 : ℝ), (328965179/625000000 : ℝ)] ![(13447623279783/100000000000000 : ℝ), (43989063239359/100000000000000 : ℝ), (5320414181981/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553648431/2500000000 : ℝ)|^8237 ≤ (13447623279783/100000000000000 : ℝ)^6189
        have hw : |(-553648431/2500000000 : ℝ)|=(553648431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33721077/62500000 : ℝ)|^8237 ≤ (43989063239359/100000000000000 : ℝ)^6189
        have hw : |(33721077/62500000 : ℝ)|=(33721077/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328965179/625000000 : ℝ)|^8237 ≤ (5320414181981/12500000000000 : ℝ)^6189
        have hw : |(328965179/625000000 : ℝ)|=(328965179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s6_1 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345182589/10000000000 : ℝ)*x 0 + (-2281545793/10000000000 : ℝ)*x 1 + (5263442841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345182589/10000000000 : ℝ)^8237 ≤ (21722645893221/50000000000000 : ℝ)^6189 := by
    have hnat : (5345182589 : ℕ)^8237*50000000000000^6189 ≤ 21722645893221^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345182589 10000000000 21722645893221 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2281545793/10000000000 : ℝ)^8237 ≤ (3497848749411/25000000000000 : ℝ)^6189 := by
    have hnat : (2281545793 : ℕ)^8237*25000000000000^6189 ≤ 3497848749411^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281545793 10000000000 3497848749411 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263442841/10000000000 : ℝ)^8237 ≤ (42563313208309/100000000000000 : ℝ)^6189 := by
    have hnat : (5263442841 : ℕ)^8237*100000000000000^6189 ≤ 42563313208309^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263442841 10000000000 42563313208309 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345182589/10000000000 : ℝ), (-2281545793/10000000000 : ℝ), (5263442841/10000000000 : ℝ)] ![(21722645893221/50000000000000 : ℝ), (3497848749411/25000000000000 : ℝ), (42563313208309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345182589/10000000000 : ℝ)|^8237 ≤ (21722645893221/50000000000000 : ℝ)^6189
        have hw : |(5345182589/10000000000 : ℝ)|=(5345182589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2281545793/10000000000 : ℝ)|^8237 ≤ (3497848749411/25000000000000 : ℝ)^6189
        have hw : |(-2281545793/10000000000 : ℝ)|=(2281545793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263442841/10000000000 : ℝ)|^8237 ≤ (42563313208309/100000000000000 : ℝ)^6189
        have hw : |(5263442841/10000000000 : ℝ)|=(5263442841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s6_2 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336295609/2500000000 : ℝ)*x 0 + (5263442953/10000000000 : ℝ)*x 1 + (-2281545847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336295609/2500000000 : ℝ)^8237 ≤ (43445290131357/100000000000000 : ℝ)^6189 := by
    have hnat : (1336295609 : ℕ)^8237*100000000000000^6189 ≤ 43445290131357^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336295609 2500000000 43445290131357 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263442953/10000000000 : ℝ)^8237 ≤ (2660207150857/6250000000000 : ℝ)^6189 := by
    have hnat : (5263442953 : ℕ)^8237*6250000000000^6189 ≤ 2660207150857^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263442953 10000000000 2660207150857 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2281545847/10000000000 : ℝ)^8237 ≤ (1748924429797/12500000000000 : ℝ)^6189 := by
    have hnat : (2281545847 : ℕ)^8237*12500000000000^6189 ≤ 1748924429797^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281545847 10000000000 1748924429797 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336295609/2500000000 : ℝ), (5263442953/10000000000 : ℝ), (-2281545847/10000000000 : ℝ)] ![(43445290131357/100000000000000 : ℝ), (2660207150857/6250000000000 : ℝ), (1748924429797/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336295609/2500000000 : ℝ)|^8237 ≤ (43445290131357/100000000000000 : ℝ)^6189
        have hw : |(1336295609/2500000000 : ℝ)|=(1336295609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263442953/10000000000 : ℝ)|^8237 ≤ (2660207150857/6250000000000 : ℝ)^6189
        have hw : |(5263442953/10000000000 : ℝ)|=(5263442953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2281545847/10000000000 : ℝ)|^8237 ≤ (1748924429797/12500000000000 : ℝ)^6189
        have hw : |(-2281545847/10000000000 : ℝ)|=(2281545847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s6_3 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378634133/10000000000 : ℝ)*x 0 + (1062960861/2500000000 : ℝ)*x 1 + (2254639117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378634133/10000000000 : ℝ)^8237 ≤ (3331609938329/10000000000000 : ℝ)^6189 := by
    have hnat : (4378634133 : ℕ)^8237*10000000000000^6189 ≤ 3331609938329^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378634133 10000000000 3331609938329 10000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062960861/2500000000 : ℝ)^8237 ≤ (32038331250509/100000000000000 : ℝ)^6189 := by
    have hnat : (1062960861 : ℕ)^8237*100000000000000^6189 ≤ 32038331250509^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062960861 2500000000 32038331250509 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254639117/5000000000 : ℝ)^8237 ≤ (34645569354801/100000000000000 : ℝ)^6189 := by
    have hnat : (2254639117 : ℕ)^8237*100000000000000^6189 ≤ 34645569354801^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254639117 5000000000 34645569354801 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378634133/10000000000 : ℝ), (1062960861/2500000000 : ℝ), (2254639117/5000000000 : ℝ)] ![(3331609938329/10000000000000 : ℝ), (32038331250509/100000000000000 : ℝ), (34645569354801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378634133/10000000000 : ℝ)|^8237 ≤ (3331609938329/10000000000000 : ℝ)^6189
        have hw : |(4378634133/10000000000 : ℝ)|=(4378634133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062960861/2500000000 : ℝ)|^8237 ≤ (32038331250509/100000000000000 : ℝ)^6189
        have hw : |(1062960861/2500000000 : ℝ)|=(1062960861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254639117/5000000000 : ℝ)|^8237 ≤ (34645569354801/100000000000000 : ℝ)^6189
        have hw : |(2254639117/5000000000 : ℝ)|=(2254639117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s6_4 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107299477/5000000000 : ℝ)*x 0 + (105275523/200000000 : ℝ)*x 1 + (5395037853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107299477/5000000000 : ℝ)^8237 ≤ (1344766554683/10000000000000 : ℝ)^6189 := by
    have hnat : (1107299477 : ℕ)^8237*10000000000000^6189 ≤ 1344766554683^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107299477 5000000000 1344766554683 10000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105275523/200000000 : ℝ)^8237 ≤ (42566900491727/100000000000000 : ℝ)^6189 := by
    have hnat : (105275523 : ℕ)^8237*100000000000000^6189 ≤ 42566900491727^6189*200000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105275523 200000000 42566900491727 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395037853/10000000000 : ℝ)^8237 ≤ (21992716978751/50000000000000 : ℝ)^6189 := by
    have hnat : (5395037853 : ℕ)^8237*50000000000000^6189 ≤ 21992716978751^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395037853 10000000000 21992716978751 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107299477/5000000000 : ℝ), (105275523/200000000 : ℝ), (5395037853/10000000000 : ℝ)] ![(1344766554683/10000000000000 : ℝ), (42566900491727/100000000000000 : ℝ), (21992716978751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107299477/5000000000 : ℝ)|^8237 ≤ (1344766554683/10000000000000 : ℝ)^6189
        have hw : |(-1107299477/5000000000 : ℝ)|=(1107299477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105275523/200000000 : ℝ)|^8237 ≤ (42566900491727/100000000000000 : ℝ)^6189
        have hw : |(105275523/200000000 : ℝ)|=(105275523/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395037853/10000000000 : ℝ)|^8237 ≤ (21992716978751/50000000000000 : ℝ)^6189
        have hw : |(5395037853/10000000000 : ℝ)|=(5395037853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s6_5 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42496087/80000000 : ℝ)*x 0 + (-429990169/2000000000 : ℝ)*x 1 + (5395037853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42496087/80000000 : ℝ)^8237 ≤ (21543412101633/50000000000000 : ℝ)^6189 := by
    have hnat : (42496087 : ℕ)^8237*50000000000000^6189 ≤ 21543412101633^6189*80000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42496087 80000000 21543412101633 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429990169/2000000000 : ℝ)^8237 ≤ (3231935455857/25000000000000 : ℝ)^6189 := by
    have hnat : (429990169 : ℕ)^8237*25000000000000^6189 ≤ 3231935455857^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429990169 2000000000 3231935455857 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395037853/10000000000 : ℝ)^8237 ≤ (21992716978751/50000000000000 : ℝ)^6189 := by
    have hnat : (5395037853 : ℕ)^8237*50000000000000^6189 ≤ 21992716978751^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395037853 10000000000 21992716978751 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42496087/80000000 : ℝ), (-429990169/2000000000 : ℝ), (5395037853/10000000000 : ℝ)] ![(21543412101633/50000000000000 : ℝ), (3231935455857/25000000000000 : ℝ), (21992716978751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42496087/80000000 : ℝ)|^8237 ≤ (21543412101633/50000000000000 : ℝ)^6189
        have hw : |(42496087/80000000 : ℝ)|=(42496087/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429990169/2000000000 : ℝ)|^8237 ≤ (3231935455857/25000000000000 : ℝ)^6189
        have hw : |(-429990169/2000000000 : ℝ)|=(429990169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395037853/10000000000 : ℝ)|^8237 ≤ (21992716978751/50000000000000 : ℝ)^6189
        have hw : |(5395037853/10000000000 : ℝ)|=(5395037853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s6_6 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42496087/80000000 : ℝ)*x 0 + (5395037853/10000000000 : ℝ)*x 1 + (-429990169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42496087/80000000 : ℝ)^8237 ≤ (21543412101633/50000000000000 : ℝ)^6189 := by
    have hnat : (42496087 : ℕ)^8237*50000000000000^6189 ≤ 21543412101633^6189*80000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42496087 80000000 21543412101633 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395037853/10000000000 : ℝ)^8237 ≤ (21992716978751/50000000000000 : ℝ)^6189 := by
    have hnat : (5395037853 : ℕ)^8237*50000000000000^6189 ≤ 21992716978751^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395037853 10000000000 21992716978751 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429990169/2000000000 : ℝ)^8237 ≤ (3231935455857/25000000000000 : ℝ)^6189 := by
    have hnat : (429990169 : ℕ)^8237*25000000000000^6189 ≤ 3231935455857^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429990169 2000000000 3231935455857 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42496087/80000000 : ℝ), (5395037853/10000000000 : ℝ), (-429990169/2000000000 : ℝ)] ![(21543412101633/50000000000000 : ℝ), (21992716978751/50000000000000 : ℝ), (3231935455857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42496087/80000000 : ℝ)|^8237 ≤ (21543412101633/50000000000000 : ℝ)^6189
        have hw : |(42496087/80000000 : ℝ)|=(42496087/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395037853/10000000000 : ℝ)|^8237 ≤ (21992716978751/50000000000000 : ℝ)^6189
        have hw : |(5395037853/10000000000 : ℝ)|=(5395037853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429990169/2000000000 : ℝ)|^8237 ≤ (3231935455857/25000000000000 : ℝ)^6189
        have hw : |(-429990169/2000000000 : ℝ)|=(429990169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s6_7 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378644397/10000000000 : ℝ)*x 0 + (1127156959/2500000000 : ℝ)*x 1 + (4252496221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378644397/10000000000 : ℝ)^8237 ≤ (33316203322853/100000000000000 : ℝ)^6189 := by
    have hnat : (4378644397 : ℕ)^8237*100000000000000^6189 ≤ 33316203322853^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378644397 10000000000 33316203322853 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127156959/2500000000 : ℝ)^8237 ≤ (34638918796801/100000000000000 : ℝ)^6189 := by
    have hnat : (1127156959 : ℕ)^8237*100000000000000^6189 ≤ 34638918796801^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127156959 2500000000 34638918796801 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4252496221/10000000000 : ℝ)^8237 ≤ (16022438934863/50000000000000 : ℝ)^6189 := by
    have hnat : (4252496221 : ℕ)^8237*50000000000000^6189 ≤ 16022438934863^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252496221 10000000000 16022438934863 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378644397/10000000000 : ℝ), (1127156959/2500000000 : ℝ), (4252496221/10000000000 : ℝ)] ![(33316203322853/100000000000000 : ℝ), (34638918796801/100000000000000 : ℝ), (16022438934863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378644397/10000000000 : ℝ)|^8237 ≤ (33316203322853/100000000000000 : ℝ)^6189
        have hw : |(4378644397/10000000000 : ℝ)|=(4378644397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127156959/2500000000 : ℝ)|^8237 ≤ (34638918796801/100000000000000 : ℝ)^6189
        have hw : |(1127156959/2500000000 : ℝ)|=(1127156959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4252496221/10000000000 : ℝ)|^8237 ≤ (16022438934863/50000000000000 : ℝ)^6189
        have hw : |(4252496221/10000000000 : ℝ)|=(4252496221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1044_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1401/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7001/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5581/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5581/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5581/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5581/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5581/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5581/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5581/50000 : ℝ) ^ (2059/512 : ℝ) ≤ (2961688648600323/20000000000000000000 : ℝ) := by
    have hpowers : (5581/50000 : ℝ)^2059 ≤ (2961688648600323/20000000000000000000 : ℝ)^512 := by
      have hnat : (5581 : ℕ)^2059*20000000000000000000^512 ≤ 2961688648600323^512*50000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5581 50000 2961688648600323 20000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5581/50000 : ℝ)) (X := (2961688648600323/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hpowhi : (281/2000 : ℝ) ^ (2059/512 : ℝ) ≤ (37358863454953943/100000000000000000000 : ℝ) := by
    have hpowers : (281/2000 : ℝ)^2059 ≤ (37358863454953943/100000000000000000000 : ℝ)^512 := by
      have hnat : (281 : ℕ)^2059*100000000000000000000^512 ≤ 37358863454953943^512*2000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2000 37358863454953943 100000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2000 : ℝ)) (X := (37358863454953943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002961688648600323/10000000000000000000 : ℝ) ≤ (200014727692109/200000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (10002961688648600323/10000000000000000000 : ℝ)^512 ≤ (200014727692109/200000000000000 : ℝ)^2059 := by
      have hnat : (10002961688648600323 : ℕ)^512*200000000000000^2059 ≤ 200014727692109^2059*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002961688648600323 10000000000000000000 200014727692109 200000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200014727692109/200000000000000 : ℝ)) (X := (10002961688648600323/10000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026083653348977779/50000000000000000000 : ℝ) ≤ (10001296961057621/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (50026083653348977779/50000000000000000000 : ℝ)^512 ≤ (10001296961057621/10000000000000000 : ℝ)^2059 := by
      have hnat : (50026083653348977779 : ℕ)^512*10000000000000000^2059 ≤ 10001296961057621^2059*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026083653348977779 50000000000000000000 10001296961057621 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001296961057621/10000000000000000 : ℝ)) (X := (50026083653348977779/50000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037358863454953943/50000000000000000000 : ℝ) ≤ (312558048047181/312500000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (50037358863454953943/50000000000000000000 : ℝ)^512 ≤ (312558048047181/312500000000000 : ℝ)^2059 := by
      have hnat : (50037358863454953943 : ℕ)^512*312500000000000^2059 ≤ 312558048047181^2059*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037358863454953943 50000000000000000000 312558048047181 312500000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312558048047181/312500000000000 : ℝ)) (X := (50037358863454953943/50000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2961688648600323/20000000000000000000 : ℝ) ≤ ((7217403092505568549/7220000000000000000 : ℝ)+2*(560576452171/288800000000000 : ℝ)*(5581/50000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (7217403092505568549/7220000000000000000 : ℝ)+2*(560576452171/288800000000000 : ℝ)*(5581/50000 : ℝ)=(200014727692109/200000000000000 : ℝ) by norm_num, show 1+2*(2961688648600323/20000000000000000000 : ℝ)=(10002961688648600323/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37358863454953943/100000000000000000000 : ℝ)+(2961688648600323/20000000000000000000 : ℝ) ≤ ((7217403092505568549/7220000000000000000 : ℝ)+(560576452171/288800000000000 : ℝ)*((281/2000 : ℝ)+(5581/50000 : ℝ)))^(2059/512 : ℝ) := by
    rw [show (7217403092505568549/7220000000000000000 : ℝ)+(560576452171/288800000000000 : ℝ)*((281/2000 : ℝ)+(5581/50000 : ℝ))=(10001296961057621/10000000000000000 : ℝ) by norm_num, show 1+(37358863454953943/100000000000000000000 : ℝ)+(2961688648600323/20000000000000000000 : ℝ)=(50026083653348977779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37358863454953943/100000000000000000000 : ℝ) ≤ ((7217403092505568549/7220000000000000000 : ℝ)+2*(560576452171/288800000000000 : ℝ)*(281/2000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (7217403092505568549/7220000000000000000 : ℝ)+2*(560576452171/288800000000000 : ℝ)*(281/2000 : ℝ)=(312558048047181/312500000000000 : ℝ) by norm_num, show 1+2*(37358863454953943/100000000000000000000 : ℝ)=(50037358863454953943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7217403092505568549/7220000000000000000 : ℝ)*(X 1 0+X 2 0)+(560576452171/288800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5581/50000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (7217403092505568549/7220000000000000000 : ℝ)) (alpha := (560576452171/288800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7217403092505568549/7220000000000000000 : ℝ)*(X 0 1+X 2 1)+(560576452171/288800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5581/50000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (7217403092505568549/7220000000000000000 : ℝ)) (alpha := (560576452171/288800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7217403092505568549/7220000000000000000 : ℝ)*(X 0 2+X 1 2)+(560576452171/288800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5581/50000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (7217403092505568549/7220000000000000000 : ℝ)) (alpha := (560576452171/288800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-553648431/2500000000 : ℝ)*X 0 0+(33721077/62500000 : ℝ)*X 0 1+(328965179/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345182589/10000000000 : ℝ)*X 1 0+(-2281545793/10000000000 : ℝ)*X 1 1+(5263442841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336295609/2500000000 : ℝ)*X 2 0+(5263442953/10000000000 : ℝ)*X 2 1+(-2281545847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378634133/10000000000 : ℝ)*X 0 0+(1062960861/2500000000 : ℝ)*X 0 1+(2254639117/5000000000 : ℝ)*X 0 2+(4378634133/10000000000 : ℝ)*X 1 0+(1062960861/2500000000 : ℝ)*X 1 1+(2254639117/5000000000 : ℝ)*X 1 2+(4378634133/10000000000 : ℝ)*X 2 0+(1062960861/2500000000 : ℝ)*X 2 1+(2254639117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1107299477/5000000000 : ℝ)*X 0 0+(105275523/200000000 : ℝ)*X 0 1+(5395037853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42496087/80000000 : ℝ)*X 1 0+(-429990169/2000000000 : ℝ)*X 1 1+(5395037853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42496087/80000000 : ℝ)*X 2 0+(5395037853/10000000000 : ℝ)*X 2 1+(-429990169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378644397/10000000000 : ℝ)*X 0 0+(1127156959/2500000000 : ℝ)*X 0 1+(4252496221/10000000000 : ℝ)*X 0 2+(4378644397/10000000000 : ℝ)*X 1 0+(1127156959/2500000000 : ℝ)*X 1 1+(4252496221/10000000000 : ℝ)*X 1 2+(4378644397/10000000000 : ℝ)*X 2 0+(1127156959/2500000000 : ℝ)*X 2 1+(4252496221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85292778168692751567375951/14440000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1311516633/100000000000000 : ℝ)*(base19) + (1055485333/100000000000000 : ℝ)*(base23) + (652541/3125000000000 : ℝ)*(lower2) + (43047907/20000000000000 : ℝ)*(upper3) + (30021541/50000000000000 : ℝ)*(upper5) + (229287861504389/4000000000000 : ℝ)*(major0) + (229287861504389/4000000000000 : ℝ)*(major1) + (229287861504389/4000000000000 : ℝ)*(major2) + (7579846791033637/100000000000000 : ℝ)*(sp0) + (1894968751127253/25000000000000 : ℝ)*(sp1) + (7579875260540311/100000000000000 : ℝ)*(sp2) + (971124144156667/25000000000000 : ℝ)*(sp3) + (3690624001/12500000000000 : ℝ)*(sp4) + (19985677051/100000000000000 : ℝ)*(sp7) + (97112914057593/2500000000000 : ℝ)*(f.failure) + (1894969079006411/25000000000000 : ℝ)*(f.sum) + (3877241265947/2888000000000000000000000000 : ℝ)*base65 + (512857356286996561/28880000000000000000000000000000 : ℝ)*base67 + (227555576044836561/28880000000000000000000000000000 : ℝ)*base69 + (326697139354916561/28880000000000000000000000000000 : ℝ)*base71 + (19212719264339/2888000000000000000000000000 : ℝ)*base73 + (418241901492836561/28880000000000000000000000000000 : ℝ)*base75 + (130567701306276561/28880000000000000000000000000000 : ℝ)*base77 + (1119463234301156561/28880000000000000000000000000000 : ℝ)*base79 + (24801113473187/2888000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1114343/250000000000000000000 : ℝ)*base90 + (1114343/250000000000000000000 : ℝ)*base92 + (1114343/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62874474913184980361175159/22562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104437029/20000000000000 : ℝ)*(base19) + (567588741/100000000000000 : ℝ)*(base23) + (13975621/25000000000000 : ℝ)*(upper3) + (20637069/100000000000000 : ℝ)*(lower4) + (56766597/100000000000000 : ℝ)*(upper5) + (720163155903203/12500000000000 : ℝ)*(major0) + (720163155903203/12500000000000 : ℝ)*(major1) + (720163155903203/12500000000000 : ℝ)*(major2) + (3506246097/25000000000000 : ℝ)*(sp1) + (376863841/2500000000000 : ℝ)*(sp2) + (1523673569396963/20000000000000 : ℝ)*(sp4) + (7618353299815281/100000000000000 : ℝ)*(sp5) + (3809176102421217/50000000000000 : ℝ)*(sp6) + (976060638644269/25000000000000 : ℝ)*(sp7) + (976060638644269/25000000000000 : ℝ)*(f.failure) + (1523673569396963/20000000000000 : ℝ)*(f.sum) + (4434452013803/1805000000000000000000000000 : ℝ)*base65 + (1082312756031487447/90250000000000000000000000000000 : ℝ)*base67 + (561842612030237447/90250000000000000000000000000000 : ℝ)*base69 + (380222375963237447/90250000000000000000000000000000 : ℝ)*base71 + (4840311127961/902500000000000000000000000 : ℝ)*base74 + (1264258740538737447/90250000000000000000000000000000 : ℝ)*base75 + (2413742352512553/90250000000000000000000000000000 : ℝ)*base78 + (2093113579833487447/90250000000000000000000000000000 : ℝ)*base79 + (8092861528983/1805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (22592019/2500000000000000000000 : ℝ)*base90 + (22592019/2500000000000000000000 : ℝ)*base92 + (22592019/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1044_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1044_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1044_s7_0 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-276829871/1250000000 : ℝ)*x 0 + (2697426321/5000000000 : ℝ)*x 1 + (1315983207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276829871/1250000000 : ℝ)^8237 ≤ (3361997231801/25000000000000 : ℝ)^6189 := by
    have hnat : (276829871 : ℕ)^8237*25000000000000^6189 ≤ 3361997231801^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276829871 1250000000 3361997231801 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697426321/5000000000 : ℝ)^8237 ≤ (21991712137901/50000000000000 : ℝ)^6189 := by
    have hnat : (2697426321 : ℕ)^8237*50000000000000^6189 ≤ 21991712137901^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697426321 5000000000 21991712137901 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315983207/2500000000 : ℝ)^8237 ≤ (42568586785971/100000000000000 : ℝ)^6189 := by
    have hnat : (1315983207 : ℕ)^8237*100000000000000^6189 ≤ 42568586785971^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315983207 2500000000 42568586785971 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276829871/1250000000 : ℝ), (2697426321/5000000000 : ℝ), (1315983207/2500000000 : ℝ)] ![(3361997231801/25000000000000 : ℝ), (21991712137901/50000000000000 : ℝ), (42568586785971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276829871/1250000000 : ℝ)|^8237 ≤ (3361997231801/25000000000000 : ℝ)^6189
        have hw : |(-276829871/1250000000 : ℝ)|=(276829871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697426321/5000000000 : ℝ)|^8237 ≤ (21991712137901/50000000000000 : ℝ)^6189
        have hw : |(2697426321/5000000000 : ℝ)|=(2697426321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315983207/2500000000 : ℝ)|^8237 ≤ (42568586785971/100000000000000 : ℝ)^6189
        have hw : |(1315983207/2500000000 : ℝ)|=(1315983207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s7_1 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345053087/10000000000 : ℝ)*x 0 + (-456214161/2000000000 : ℝ)*x 1 + (1315983297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345053087/10000000000 : ℝ)^8237 ≤ (10860972724549/25000000000000 : ℝ)^6189 := by
    have hnat : (5345053087 : ℕ)^8237*25000000000000^6189 ≤ 10860972724549^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345053087 10000000000 10860972724549 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456214161/2000000000 : ℝ)^8237 ≤ (6993759211779/50000000000000 : ℝ)^6189 := by
    have hnat : (456214161 : ℕ)^8237*50000000000000^6189 ≤ 6993759211779^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456214161 2000000000 6993759211779 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315983297/2500000000 : ℝ)^8237 ≤ (21284295330299/50000000000000 : ℝ)^6189 := by
    have hnat : (1315983297 : ℕ)^8237*50000000000000^6189 ≤ 21284295330299^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315983297 2500000000 21284295330299 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345053087/10000000000 : ℝ), (-456214161/2000000000 : ℝ), (1315983297/2500000000 : ℝ)] ![(10860972724549/25000000000000 : ℝ), (6993759211779/50000000000000 : ℝ), (21284295330299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345053087/10000000000 : ℝ)|^8237 ≤ (10860972724549/25000000000000 : ℝ)^6189
        have hw : |(5345053087/10000000000 : ℝ)|=(5345053087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456214161/2000000000 : ℝ)|^8237 ≤ (6993759211779/50000000000000 : ℝ)^6189
        have hw : |(-456214161/2000000000 : ℝ)|=(456214161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315983297/2500000000 : ℝ)|^8237 ≤ (21284295330299/50000000000000 : ℝ)^6189
        have hw : |(1315983297/2500000000 : ℝ)|=(1315983297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s7_2 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672526617/5000000000 : ℝ)*x 0 + (5263932951/10000000000 : ℝ)*x 1 + (-2281070923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672526617/5000000000 : ℝ)^8237 ≤ (43443892488363/100000000000000 : ℝ)^6189 := by
    have hnat : (2672526617 : ℕ)^8237*100000000000000^6189 ≤ 43443892488363^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672526617 5000000000 43443892488363 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263932951/10000000000 : ℝ)^8237 ≤ (21284294054901/50000000000000 : ℝ)^6189 := by
    have hnat : (5263932951 : ℕ)^8237*50000000000000^6189 ≤ 21284294054901^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263932951 10000000000 21284294054901 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2281070923/10000000000 : ℝ)^8237 ≤ (3496879846643/25000000000000 : ℝ)^6189 := by
    have hnat : (2281070923 : ℕ)^8237*25000000000000^6189 ≤ 3496879846643^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281070923 10000000000 3496879846643 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672526617/5000000000 : ℝ), (5263932951/10000000000 : ℝ), (-2281070923/10000000000 : ℝ)] ![(43443892488363/100000000000000 : ℝ), (21284294054901/50000000000000 : ℝ), (3496879846643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672526617/5000000000 : ℝ)|^8237 ≤ (43443892488363/100000000000000 : ℝ)^6189
        have hw : |(2672526617/5000000000 : ℝ)|=(2672526617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263932951/10000000000 : ℝ)|^8237 ≤ (21284294054901/50000000000000 : ℝ)^6189
        have hw : |(5263932951/10000000000 : ℝ)|=(5263932951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2281070923/10000000000 : ℝ)|^8237 ≤ (3496879846643/25000000000000 : ℝ)^6189
        have hw : |(-2281070923/10000000000 : ℝ)|=(2281070923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s7_3 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378660189/10000000000 : ℝ)*x 0 + (1063206357/2500000000 : ℝ)*x 1 + (450828929/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378660189/10000000000 : ℝ)^8237 ≤ (16658181621247/50000000000000 : ℝ)^6189 := by
    have hnat : (4378660189 : ℕ)^8237*50000000000000^6189 ≤ 16658181621247^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378660189 10000000000 16658181621247 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063206357/2500000000 : ℝ)^8237 ≤ (8012044892967/25000000000000 : ℝ)^6189 := by
    have hnat : (1063206357 : ℕ)^8237*25000000000000^6189 ≤ 8012044892967^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063206357 2500000000 8012044892967 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450828929/1000000000 : ℝ)^8237 ≤ (34635457165461/100000000000000 : ℝ)^6189 := by
    have hnat : (450828929 : ℕ)^8237*100000000000000^6189 ≤ 34635457165461^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450828929 1000000000 34635457165461 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378660189/10000000000 : ℝ), (1063206357/2500000000 : ℝ), (450828929/1000000000 : ℝ)] ![(16658181621247/50000000000000 : ℝ), (8012044892967/25000000000000 : ℝ), (34635457165461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378660189/10000000000 : ℝ)|^8237 ≤ (16658181621247/50000000000000 : ℝ)^6189
        have hw : |(4378660189/10000000000 : ℝ)|=(4378660189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1063206357/2500000000 : ℝ)|^8237 ≤ (8012044892967/25000000000000 : ℝ)^6189
        have hw : |(1063206357/2500000000 : ℝ)|=(1063206357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450828929/1000000000 : ℝ)|^8237 ≤ (34635457165461/100000000000000 : ℝ)^6189
        have hw : |(450828929/1000000000 : ℝ)|=(450828929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s7_4 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2214643907/10000000000 : ℝ)*x 0 + (2632130631/5000000000 : ℝ)*x 1 + (2697261591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2214643907/10000000000 : ℝ)^8237 ≤ (13448028842759/100000000000000 : ℝ)^6189 := by
    have hnat : (2214643907 : ℕ)^8237*100000000000000^6189 ≤ 13448028842759^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214643907 10000000000 13448028842759 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632130631/5000000000 : ℝ)^8237 ≤ (42572121709881/100000000000000 : ℝ)^6189 := by
    have hnat : (2632130631 : ℕ)^8237*100000000000000^6189 ≤ 42572121709881^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632130631 5000000000 42572121709881 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697261591/5000000000 : ℝ)^8237 ≤ (10994962359503/25000000000000 : ℝ)^6189 := by
    have hnat : (2697261591 : ℕ)^8237*25000000000000^6189 ≤ 10994962359503^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697261591 5000000000 10994962359503 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2214643907/10000000000 : ℝ), (2632130631/5000000000 : ℝ), (2697261591/5000000000 : ℝ)] ![(13448028842759/100000000000000 : ℝ), (42572121709881/100000000000000 : ℝ), (10994962359503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2214643907/10000000000 : ℝ)|^8237 ≤ (13448028842759/100000000000000 : ℝ)^6189
        have hw : |(-2214643907/10000000000 : ℝ)|=(2214643907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632130631/5000000000 : ℝ)|^8237 ≤ (42572121709881/100000000000000 : ℝ)^6189
        have hw : |(2632130631/5000000000 : ℝ)|=(2632130631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697261591/5000000000 : ℝ)|^8237 ≤ (10994962359503/25000000000000 : ℝ)^6189
        have hw : |(2697261591/5000000000 : ℝ)|=(2697261591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s7_5 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312135339/10000000000 : ℝ)*x 0 + (-2150480749/10000000000 : ℝ)*x 1 + (2697261591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312135339/10000000000 : ℝ)^8237 ≤ (10772041958207/25000000000000 : ℝ)^6189 := by
    have hnat : (5312135339 : ℕ)^8237*25000000000000^6189 ≤ 10772041958207^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312135339 10000000000 10772041958207 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2150480749/10000000000 : ℝ)^8237 ≤ (808248919969/6250000000000 : ℝ)^6189 := by
    have hnat : (2150480749 : ℕ)^8237*6250000000000^6189 ≤ 808248919969^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150480749 10000000000 808248919969 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697261591/5000000000 : ℝ)^8237 ≤ (10994962359503/25000000000000 : ℝ)^6189 := by
    have hnat : (2697261591 : ℕ)^8237*25000000000000^6189 ≤ 10994962359503^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697261591 5000000000 10994962359503 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312135339/10000000000 : ℝ), (-2150480749/10000000000 : ℝ), (2697261591/5000000000 : ℝ)] ![(10772041958207/25000000000000 : ℝ), (808248919969/6250000000000 : ℝ), (10994962359503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312135339/10000000000 : ℝ)|^8237 ≤ (10772041958207/25000000000000 : ℝ)^6189
        have hw : |(5312135339/10000000000 : ℝ)|=(5312135339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2150480749/10000000000 : ℝ)|^8237 ≤ (808248919969/6250000000000 : ℝ)^6189
        have hw : |(-2150480749/10000000000 : ℝ)|=(2150480749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697261591/5000000000 : ℝ)|^8237 ≤ (10994962359503/25000000000000 : ℝ)^6189
        have hw : |(2697261591/5000000000 : ℝ)|=(2697261591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s7_6 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312135339/10000000000 : ℝ)*x 0 + (2697261591/5000000000 : ℝ)*x 1 + (-2150480749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312135339/10000000000 : ℝ)^8237 ≤ (10772041958207/25000000000000 : ℝ)^6189 := by
    have hnat : (5312135339 : ℕ)^8237*25000000000000^6189 ≤ 10772041958207^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312135339 10000000000 10772041958207 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697261591/5000000000 : ℝ)^8237 ≤ (10994962359503/25000000000000 : ℝ)^6189 := by
    have hnat : (2697261591 : ℕ)^8237*25000000000000^6189 ≤ 10994962359503^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697261591 5000000000 10994962359503 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150480749/10000000000 : ℝ)^8237 ≤ (808248919969/6250000000000 : ℝ)^6189 := by
    have hnat : (2150480749 : ℕ)^8237*6250000000000^6189 ≤ 808248919969^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150480749 10000000000 808248919969 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312135339/10000000000 : ℝ), (2697261591/5000000000 : ℝ), (-2150480749/10000000000 : ℝ)] ![(10772041958207/25000000000000 : ℝ), (10994962359503/25000000000000 : ℝ), (808248919969/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312135339/10000000000 : ℝ)|^8237 ≤ (10772041958207/25000000000000 : ℝ)^6189
        have hw : |(5312135339/10000000000 : ℝ)|=(5312135339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697261591/5000000000 : ℝ)|^8237 ≤ (10994962359503/25000000000000 : ℝ)^6189
        have hw : |(2697261591/5000000000 : ℝ)|=(2697261591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2150480749/10000000000 : ℝ)|^8237 ≤ (808248919969/6250000000000 : ℝ)^6189
        have hw : |(-2150480749/10000000000 : ℝ)|=(2150480749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s7_7 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189335051/5000000000 : ℝ)*x 0 + (2253824473/5000000000 : ℝ)*x 1 + (4253468213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189335051/5000000000 : ℝ)^8237 ≤ (8329115906953/25000000000000 : ℝ)^6189 := by
    have hnat : (2189335051 : ℕ)^8237*25000000000000^6189 ≤ 8329115906953^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189335051 5000000000 8329115906953 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253824473/5000000000 : ℝ)^8237 ≤ (34628909886139/100000000000000 : ℝ)^6189 := by
    have hnat : (2253824473 : ℕ)^8237*100000000000000^6189 ≤ 34628909886139^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253824473 5000000000 34628909886139 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4253468213/10000000000 : ℝ)^8237 ≤ (32054626472647/100000000000000 : ℝ)^6189 := by
    have hnat : (4253468213 : ℕ)^8237*100000000000000^6189 ≤ 32054626472647^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253468213 10000000000 32054626472647 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189335051/5000000000 : ℝ), (2253824473/5000000000 : ℝ), (4253468213/10000000000 : ℝ)] ![(8329115906953/25000000000000 : ℝ), (34628909886139/100000000000000 : ℝ), (32054626472647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189335051/5000000000 : ℝ)|^8237 ≤ (8329115906953/25000000000000 : ℝ)^6189
        have hw : |(2189335051/5000000000 : ℝ)|=(2189335051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253824473/5000000000 : ℝ)|^8237 ≤ (34628909886139/100000000000000 : ℝ)^6189
        have hw : |(2253824473/5000000000 : ℝ)|=(2253824473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4253468213/10000000000 : ℝ)|^8237 ≤ (32054626472647/100000000000000 : ℝ)^6189
        have hw : |(4253468213/10000000000 : ℝ)|=(4253468213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1044_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5609/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1749/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7001/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1401/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7001/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1401/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7001/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1401/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7001/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1401/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7001/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1401/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7001/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1401/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1401/12500 : ℝ) ^ (2059/512 : ℝ) ≤ (7527698202385379/50000000000000000000 : ℝ) := by
    have hpowers : (1401/12500 : ℝ)^2059 ≤ (7527698202385379/50000000000000000000 : ℝ)^512 := by
      have hnat : (1401 : ℕ)^2059*50000000000000000000^512 ≤ 7527698202385379^512*12500^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 12500 7527698202385379 50000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/12500 : ℝ)) (X := (7527698202385379/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7001/50000 : ℝ) ^ (2059/512 : ℝ) ≤ (18424118784298461/50000000000000000000 : ℝ) := by
    have hpowers : (7001/50000 : ℝ)^2059 ≤ (18424118784298461/50000000000000000000 : ℝ)^512 := by
      have hnat : (7001 : ℕ)^2059*50000000000000000000^512 ≤ 18424118784298461^512*50000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7001 50000 18424118784298461 50000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7001/50000 : ℝ)) (X := (18424118784298461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007527698202385379/25000000000000000000 : ℝ) ≤ (10000748663542403/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (25007527698202385379/25000000000000000000 : ℝ)^512 ≤ (10000748663542403/10000000000000000 : ℝ)^2059 := by
      have hnat : (25007527698202385379 : ℕ)^512*10000000000000000^2059 ≤ 10000748663542403^2059*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007527698202385379 25000000000000000000 10000748663542403 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000748663542403/10000000000000000 : ℝ)) (X := (25007527698202385379/25000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (156331099428083387/156250000000000000 : ℝ) ≤ (10001290407017839/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (156331099428083387/156250000000000000 : ℝ)^512 ≤ (10001290407017839/10000000000000000 : ℝ)^2059 := by
      have hnat : (156331099428083387 : ℕ)^512*10000000000000000^2059 ≤ 10001290407017839^2059*156250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156331099428083387 156250000000000000 10001290407017839 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001290407017839/10000000000000000 : ℝ)) (X := (156331099428083387/156250000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018424118784298461/25000000000000000000 : ℝ) ≤ (400073286019731/400000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (25018424118784298461/25000000000000000000 : ℝ)^512 ≤ (400073286019731/400000000000000 : ℝ)^2059 := by
      have hnat : (25018424118784298461 : ℕ)^512*400000000000000^2059 ≤ 400073286019731^2059*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018424118784298461 25000000000000000000 400073286019731 400000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400073286019731/400000000000000 : ℝ)) (X := (25018424118784298461/25000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7527698202385379/50000000000000000000 : ℝ) ≤ ((13964974022096050303/13970000000000000000 : ℝ)+2*(135435868859/69850000000000 : ℝ)*(1401/12500 : ℝ))^(2059/512 : ℝ) := by
    rw [show (13964974022096050303/13970000000000000000 : ℝ)+2*(135435868859/69850000000000 : ℝ)*(1401/12500 : ℝ)=(10000748663542403/10000000000000000 : ℝ) by norm_num, show 1+2*(7527698202385379/50000000000000000000 : ℝ)=(25007527698202385379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18424118784298461/50000000000000000000 : ℝ)+(7527698202385379/50000000000000000000 : ℝ) ≤ ((13964974022096050303/13970000000000000000 : ℝ)+(135435868859/69850000000000 : ℝ)*((7001/50000 : ℝ)+(1401/12500 : ℝ)))^(2059/512 : ℝ) := by
    rw [show (13964974022096050303/13970000000000000000 : ℝ)+(135435868859/69850000000000 : ℝ)*((7001/50000 : ℝ)+(1401/12500 : ℝ))=(10001290407017839/10000000000000000 : ℝ) by norm_num, show 1+(18424118784298461/50000000000000000000 : ℝ)+(7527698202385379/50000000000000000000 : ℝ)=(156331099428083387/156250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18424118784298461/50000000000000000000 : ℝ) ≤ ((13964974022096050303/13970000000000000000 : ℝ)+2*(135435868859/69850000000000 : ℝ)*(7001/50000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (13964974022096050303/13970000000000000000 : ℝ)+2*(135435868859/69850000000000 : ℝ)*(7001/50000 : ℝ)=(400073286019731/400000000000000 : ℝ) by norm_num, show 1+2*(18424118784298461/50000000000000000000 : ℝ)=(25018424118784298461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13964974022096050303/13970000000000000000 : ℝ)*(X 1 0+X 2 0)+(135435868859/69850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (1401/12500 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (13964974022096050303/13970000000000000000 : ℝ)) (alpha := (135435868859/69850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13964974022096050303/13970000000000000000 : ℝ)*(X 0 1+X 2 1)+(135435868859/69850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (1401/12500 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (13964974022096050303/13970000000000000000 : ℝ)) (alpha := (135435868859/69850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13964974022096050303/13970000000000000000 : ℝ)*(X 0 2+X 1 2)+(135435868859/69850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (1401/12500 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (13964974022096050303/13970000000000000000 : ℝ)) (alpha := (135435868859/69850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-276829871/1250000000 : ℝ)*X 0 0+(2697426321/5000000000 : ℝ)*X 0 1+(1315983207/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345053087/10000000000 : ℝ)*X 1 0+(-456214161/2000000000 : ℝ)*X 1 1+(1315983297/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672526617/5000000000 : ℝ)*X 2 0+(5263932951/10000000000 : ℝ)*X 2 1+(-2281070923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378660189/10000000000 : ℝ)*X 0 0+(1063206357/2500000000 : ℝ)*X 0 1+(450828929/1000000000 : ℝ)*X 0 2+(4378660189/10000000000 : ℝ)*X 1 0+(1063206357/2500000000 : ℝ)*X 1 1+(450828929/1000000000 : ℝ)*X 1 2+(4378660189/10000000000 : ℝ)*X 2 0+(1063206357/2500000000 : ℝ)*X 2 1+(450828929/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2214643907/10000000000 : ℝ)*X 0 0+(2632130631/5000000000 : ℝ)*X 0 1+(2697261591/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312135339/10000000000 : ℝ)*X 1 0+(-2150480749/10000000000 : ℝ)*X 1 1+(2697261591/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312135339/10000000000 : ℝ)*X 2 0+(2697261591/5000000000 : ℝ)*X 2 1+(-2150480749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189335051/5000000000 : ℝ)*X 0 0+(2253824473/5000000000 : ℝ)*X 0 1+(4253468213/10000000000 : ℝ)*X 0 2+(2189335051/5000000000 : ℝ)*X 1 0+(2253824473/5000000000 : ℝ)*X 1 1+(4253468213/10000000000 : ℝ)*X 1 2+(2189335051/5000000000 : ℝ)*X 2 0+(2253824473/5000000000 : ℝ)*X 2 1+(4253468213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35278602670244791495488219/3968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (546216939/25000000000000 : ℝ)*(base19) + (1158018207/50000000000000 : ℝ)*(base23) + (193944407/50000000000000 : ℝ)*(upper3) + (8434851/20000000000000 : ℝ)*(upper4) + (93235441/50000000000000 : ℝ)*(upper5) + (361028894986083/6250000000000 : ℝ)*(major0) + (361028894986083/6250000000000 : ℝ)*(major1) + (361028894986083/6250000000000 : ℝ)*(major2) + (7638339759134107/100000000000000 : ℝ)*(sp0) + (954801020768929/12500000000000 : ℝ)*(sp1) + (3819204017491387/50000000000000 : ℝ)*(sp2) + (489309766895541/12500000000000 : ℝ)*(sp3) + (35295942541/50000000000000 : ℝ)*(sp4) + (35857067899/100000000000000 : ℝ)*(sp7) + (3914513992232227/100000000000000 : ℝ)*(f.failure) + (1909602587754797/25000000000000 : ℝ)*(f.sum) + (941138732151/1746250000000000000000000000 : ℝ)*base65 + (230526174227833149/87312500000000000000000000000000 : ℝ)*base67 + (485172546911145649/87312500000000000000000000000000 : ℝ)*base69 + (191987025388708149/87312500000000000000000000000000 : ℝ)*base71 + (19399409461337/3492500000000000000000000000 : ℝ)*base73 + (1662338034079145649/87312500000000000000000000000000 : ℝ)*base75 + (996840588938458149/87312500000000000000000000000000 : ℝ)*base77 + (2390075839308333149/87312500000000000000000000000000 : ℝ)*base79 + (13626365840579/6985000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (156920477/10000000000000000000000 : ℝ)*base90 + (156920477/10000000000000000000000 : ℝ)*base92 + (156920477/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (354703573041831080622356649/31750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1042318929/50000000000000 : ℝ)*(base19) + (141629637/6250000000000 : ℝ)*(base23) + (223655833/100000000000000 : ℝ)*(upper3) + (82523169/100000000000000 : ℝ)*(lower4) + (227583107/100000000000000 : ℝ)*(upper5) + (2902761706505471/50000000000000 : ℝ)*(major0) + (2902761706505471/50000000000000 : ℝ)*(major1) + (2902761706505471/50000000000000 : ℝ)*(major2) + (56391709631/100000000000000 : ℝ)*(sp1) + (12120281341/20000000000000 : ℝ)*(sp2) + (3838419368571443/50000000000000 : ℝ)*(sp4) + (7676780260795397/100000000000000 : ℝ)*(sp5) + (7676775869661989/100000000000000 : ℝ)*(sp6) + (983551929121697/25000000000000 : ℝ)*(sp7) + (983551929121697/25000000000000 : ℝ)*(f.failure) + (3838419368571443/50000000000000 : ℝ)*(f.sum) + (27798374778017/3492500000000000000000000000 : ℝ)*base66 + (5031350079551492287/698500000000000000000000000000000 : ℝ)*base68 + (3946192272477492287/698500000000000000000000000000000 : ℝ)*base70 + (8814999042337492287/698500000000000000000000000000000 : ℝ)*base72 + (2883475997807/873125000000000000000000000 : ℝ)*base73 + (12411180401967507713/698500000000000000000000000000000 : ℝ)*base75 + (2203805096604007713/698500000000000000000000000000000 : ℝ)*base77 + (2403511579269992287/698500000000000000000000000000000 : ℝ)*base80 + (7984402186281/1746250000000000000000000000 : ℝ)*base82 + (19107553/2500000000000000000000 : ℝ)*base89 + (19107553/2500000000000000000000 : ℝ)*base91 + (19107553/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1044_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1044_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1044_s8_0 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2214646701/10000000000 : ℝ)*x 0 + (42146441/78125000 : ℝ)*x 1 + (2632018049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2214646701/10000000000 : ℝ)^8237 ≤ (1681006427883/12500000000000 : ℝ)^6189 := by
    have hnat : (2214646701 : ℕ)^8237*12500000000000^6189 ≤ 1681006427883^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214646701 10000000000 1681006427883 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42146441/78125000 : ℝ)^8237 ≤ (43982250298309/100000000000000 : ℝ)^6189 := by
    have hnat : (42146441 : ℕ)^8237*100000000000000^6189 ≤ 43982250298309^6189*78125000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42146441 78125000 43982250298309 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632018049/5000000000 : ℝ)^8237 ≤ (42569698269583/100000000000000 : ℝ)^6189 := by
    have hnat : (2632018049 : ℕ)^8237*100000000000000^6189 ≤ 42569698269583^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632018049 5000000000 42569698269583 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2214646701/10000000000 : ℝ), (42146441/78125000 : ℝ), (2632018049/5000000000 : ℝ)] ![(1681006427883/12500000000000 : ℝ), (43982250298309/100000000000000 : ℝ), (42569698269583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2214646701/10000000000 : ℝ)|^8237 ≤ (1681006427883/12500000000000 : ℝ)^6189
        have hw : |(-2214646701/10000000000 : ℝ)|=(2214646701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42146441/78125000 : ℝ)|^8237 ≤ (43982250298309/100000000000000 : ℝ)^6189
        have hw : |(42146441/78125000 : ℝ)|=(42146441/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632018049/5000000000 : ℝ)|^8237 ≤ (42569698269583/100000000000000 : ℝ)^6189
        have hw : |(2632018049/5000000000 : ℝ)|=(2632018049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s8_1 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336256669/2500000000 : ℝ)*x 0 + (-456194019/2000000000 : ℝ)*x 1 + (2632018049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336256669/2500000000 : ℝ)^8237 ≤ (43443605198509/100000000000000 : ℝ)^6189 := by
    have hnat : (1336256669 : ℕ)^8237*100000000000000^6189 ≤ 43443605198509^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336256669 2500000000 43443605198509 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456194019/2000000000 : ℝ)^8237 ≤ (2797339304359/20000000000000 : ℝ)^6189 := by
    have hnat : (456194019 : ℕ)^8237*20000000000000^6189 ≤ 2797339304359^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456194019 2000000000 2797339304359 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632018049/5000000000 : ℝ)^8237 ≤ (42569698269583/100000000000000 : ℝ)^6189 := by
    have hnat : (2632018049 : ℕ)^8237*100000000000000^6189 ≤ 42569698269583^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632018049 5000000000 42569698269583 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336256669/2500000000 : ℝ), (-456194019/2000000000 : ℝ), (2632018049/5000000000 : ℝ)] ![(43443605198509/100000000000000 : ℝ), (2797339304359/20000000000000 : ℝ), (42569698269583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336256669/2500000000 : ℝ)|^8237 ≤ (43443605198509/100000000000000 : ℝ)^6189
        have hw : |(1336256669/2500000000 : ℝ)|=(1336256669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456194019/2000000000 : ℝ)|^8237 ≤ (2797339304359/20000000000000 : ℝ)^6189
        have hw : |(-456194019/2000000000 : ℝ)|=(456194019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632018049/5000000000 : ℝ)|^8237 ≤ (42569698269583/100000000000000 : ℝ)^6189
        have hw : |(2632018049/5000000000 : ℝ)|=(2632018049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s8_2 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534502667/1000000000 : ℝ)*x 0 + (52640361/100000000 : ℝ)*x 1 + (-2280970101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534502667/1000000000 : ℝ)^8237 ≤ (10860901283401/25000000000000 : ℝ)^6189 := by
    have hnat : (534502667 : ℕ)^8237*25000000000000^6189 ≤ 10860901283401^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534502667 1000000000 10860901283401 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52640361/100000000 : ℝ)^8237 ≤ (42569698291109/100000000000000 : ℝ)^6189 := by
    have hnat : (52640361 : ℕ)^8237*100000000000000^6189 ≤ 42569698291109^6189*100000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52640361 100000000 42569698291109 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280970101/10000000000 : ℝ)^8237 ≤ (13986696570761/100000000000000 : ℝ)^6189 := by
    have hnat : (2280970101 : ℕ)^8237*100000000000000^6189 ≤ 13986696570761^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280970101 10000000000 13986696570761 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534502667/1000000000 : ℝ), (52640361/100000000 : ℝ), (-2280970101/10000000000 : ℝ)] ![(10860901283401/25000000000000 : ℝ), (42569698291109/100000000000000 : ℝ), (13986696570761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534502667/1000000000 : ℝ)|^8237 ≤ (10860901283401/25000000000000 : ℝ)^6189
        have hw : |(534502667/1000000000 : ℝ)|=(534502667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52640361/100000000 : ℝ)|^8237 ≤ (42569698291109/100000000000000 : ℝ)^6189
        have hw : |(52640361/100000000 : ℝ)|=(52640361/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2280970101/10000000000 : ℝ)|^8237 ≤ (13986696570761/100000000000000 : ℝ)^6189
        have hw : |(-2280970101/10000000000 : ℝ)|=(2280970101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s8_3 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378665453/10000000000 : ℝ)*x 0 + (4253030787/10000000000 : ℝ)*x 1 + (4508082641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378665453/10000000000 : ℝ)^8237 ≤ (33316416549083/100000000000000 : ℝ)^6189 := by
    have hnat : (4378665453 : ℕ)^8237*100000000000000^6189 ≤ 33316416549083^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378665453 10000000000 33316416549083 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253030787/10000000000 : ℝ)^8237 ≤ (16025119606611/50000000000000 : ℝ)^6189 := by
    have hnat : (4253030787 : ℕ)^8237*50000000000000^6189 ≤ 16025119606611^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253030787 10000000000 16025119606611 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508082641/10000000000 : ℝ)^8237 ≤ (6926668844527/20000000000000 : ℝ)^6189 := by
    have hnat : (4508082641 : ℕ)^8237*20000000000000^6189 ≤ 6926668844527^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508082641 10000000000 6926668844527 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378665453/10000000000 : ℝ), (4253030787/10000000000 : ℝ), (4508082641/10000000000 : ℝ)] ![(33316416549083/100000000000000 : ℝ), (16025119606611/50000000000000 : ℝ), (6926668844527/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378665453/10000000000 : ℝ)|^8237 ≤ (33316416549083/100000000000000 : ℝ)^6189
        have hw : |(4378665453/10000000000 : ℝ)|=(4378665453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253030787/10000000000 : ℝ)|^8237 ≤ (16025119606611/50000000000000 : ℝ)^6189
        have hw : |(4253030787/10000000000 : ℝ)|=(4253030787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508082641/10000000000 : ℝ)|^8237 ≤ (6926668844527/20000000000000 : ℝ)^6189
        have hw : |(4508082641/10000000000 : ℝ)|=(4508082641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s8_4 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2214651797/10000000000 : ℝ)*x 0 + (2632181621/5000000000 : ℝ)*x 1 + (2697208073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2214651797/10000000000 : ℝ)^8237 ≤ (2689618521499/20000000000000 : ℝ)^6189 := by
    have hnat : (2214651797 : ℕ)^8237*20000000000000^6189 ≤ 2689618521499^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214651797 10000000000 2689618521499 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632181621/5000000000 : ℝ)^8237 ≤ (21286609665991/50000000000000 : ℝ)^6189 := by
    have hnat : (2632181621 : ℕ)^8237*50000000000000^6189 ≤ 21286609665991^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632181621 5000000000 21286609665991 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697208073/5000000000 : ℝ)^8237 ≤ (21989344024513/50000000000000 : ℝ)^6189 := by
    have hnat : (2697208073 : ℕ)^8237*50000000000000^6189 ≤ 21989344024513^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697208073 5000000000 21989344024513 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2214651797/10000000000 : ℝ), (2632181621/5000000000 : ℝ), (2697208073/5000000000 : ℝ)] ![(2689618521499/20000000000000 : ℝ), (21286609665991/50000000000000 : ℝ), (21989344024513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2214651797/10000000000 : ℝ)|^8237 ≤ (2689618521499/20000000000000 : ℝ)^6189
        have hw : |(-2214651797/10000000000 : ℝ)|=(2214651797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632181621/5000000000 : ℝ)|^8237 ≤ (21286609665991/50000000000000 : ℝ)^6189
        have hw : |(2632181621/5000000000 : ℝ)|=(2632181621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697208073/5000000000 : ℝ)|^8237 ≤ (21989344024513/50000000000000 : ℝ)^6189
        have hw : |(2697208073/5000000000 : ℝ)|=(2697208073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s8_5 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531216193/1000000000 : ℝ)*x 0 + (-2150590117/10000000000 : ℝ)*x 1 + (2697208027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531216193/1000000000 : ℝ)^8237 ≤ (21544227446357/50000000000000 : ℝ)^6189 := by
    have hnat : (531216193 : ℕ)^8237*50000000000000^6189 ≤ 21544227446357^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531216193 1000000000 21544227446357 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2150590117/10000000000 : ℝ)^8237 ≤ (1293285805001/10000000000000 : ℝ)^6189 := by
    have hnat : (2150590117 : ℕ)^8237*10000000000000^6189 ≤ 1293285805001^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150590117 10000000000 1293285805001 10000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697208027/5000000000 : ℝ)^8237 ≤ (10994671762697/25000000000000 : ℝ)^6189 := by
    have hnat : (2697208027 : ℕ)^8237*25000000000000^6189 ≤ 10994671762697^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697208027 5000000000 10994671762697 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531216193/1000000000 : ℝ), (-2150590117/10000000000 : ℝ), (2697208027/5000000000 : ℝ)] ![(21544227446357/50000000000000 : ℝ), (1293285805001/10000000000000 : ℝ), (10994671762697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531216193/1000000000 : ℝ)|^8237 ≤ (21544227446357/50000000000000 : ℝ)^6189
        have hw : |(531216193/1000000000 : ℝ)|=(531216193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2150590117/10000000000 : ℝ)|^8237 ≤ (1293285805001/10000000000000 : ℝ)^6189
        have hw : |(-2150590117/10000000000 : ℝ)|=(2150590117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697208027/5000000000 : ℝ)|^8237 ≤ (10994671762697/25000000000000 : ℝ)^6189
        have hw : |(2697208027/5000000000 : ℝ)|=(2697208027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s8_6 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328040487/2500000000 : ℝ)*x 0 + (2697208017/5000000000 : ℝ)*x 1 + (-1075295059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328040487/2500000000 : ℝ)^8237 ≤ (43088455087031/100000000000000 : ℝ)^6189 := by
    have hnat : (1328040487 : ℕ)^8237*100000000000000^6189 ≤ 43088455087031^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328040487 2500000000 43088455087031 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697208017/5000000000 : ℝ)^8237 ≤ (43978686833779/100000000000000 : ℝ)^6189 := by
    have hnat : (2697208017 : ℕ)^8237*100000000000000^6189 ≤ 43978686833779^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697208017 5000000000 43978686833779 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075295059/5000000000 : ℝ)^8237 ≤ (6466429029007/50000000000000 : ℝ)^6189 := by
    have hnat : (1075295059 : ℕ)^8237*50000000000000^6189 ≤ 6466429029007^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075295059 5000000000 6466429029007 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328040487/2500000000 : ℝ), (2697208017/5000000000 : ℝ), (-1075295059/5000000000 : ℝ)] ![(43088455087031/100000000000000 : ℝ), (43978686833779/100000000000000 : ℝ), (6466429029007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328040487/2500000000 : ℝ)|^8237 ≤ (43088455087031/100000000000000 : ℝ)^6189
        have hw : |(1328040487/2500000000 : ℝ)|=(1328040487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697208017/5000000000 : ℝ)|^8237 ≤ (43978686833779/100000000000000 : ℝ)^6189
        have hw : |(2697208017/5000000000 : ℝ)|=(2697208017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1075295059/5000000000 : ℝ)|^8237 ≤ (6466429029007/50000000000000 : ℝ)^6189
        have hw : |(-1075295059/5000000000 : ℝ)|=(1075295059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s8_7 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378675231/10000000000 : ℝ)*x 0 + (225372221/500000000 : ℝ)*x 1 + (1063417881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378675231/10000000000 : ℝ)^8237 ≤ (2082282222959/6250000000000 : ℝ)^6189 := by
    have hnat : (4378675231 : ℕ)^8237*6250000000000^6189 ≤ 2082282222959^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378675231 10000000000 2082282222959 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225372221/500000000 : ℝ)^8237 ≤ (34626818748679/100000000000000 : ℝ)^6189 := by
    have hnat : (225372221 : ℕ)^8237*100000000000000^6189 ≤ 34626818748679^6189*500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225372221 500000000 34626818748679 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063417881/2500000000 : ℝ)^8237 ≤ (8014166418867/25000000000000 : ℝ)^6189 := by
    have hnat : (1063417881 : ℕ)^8237*25000000000000^6189 ≤ 8014166418867^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063417881 2500000000 8014166418867 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378675231/10000000000 : ℝ), (225372221/500000000 : ℝ), (1063417881/2500000000 : ℝ)] ![(2082282222959/6250000000000 : ℝ), (34626818748679/100000000000000 : ℝ), (8014166418867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378675231/10000000000 : ℝ)|^8237 ≤ (2082282222959/6250000000000 : ℝ)^6189
        have hw : |(4378675231/10000000000 : ℝ)|=(4378675231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225372221/500000000 : ℝ)|^8237 ≤ (34626818748679/100000000000000 : ℝ)^6189
        have hw : |(225372221/500000000 : ℝ)|=(225372221/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063417881/2500000000 : ℝ)|^8237 ≤ (8014166418867/25000000000000 : ℝ)^6189
        have hw : |(1063417881/2500000000 : ℝ)|=(1063417881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1044_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11221/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13989/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1749/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1749/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1749/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1749/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1749/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1749/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5609/50000 : ℝ) ^ (2059/512 : ℝ) ≤ (7554744374759901/50000000000000000000 : ℝ) := by
    have hpowers : (5609/50000 : ℝ)^2059 ≤ (7554744374759901/50000000000000000000 : ℝ)^512 := by
      have hnat : (5609 : ℕ)^2059*50000000000000000000^512 ≤ 7554744374759901^512*50000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5609 50000 7554744374759901 50000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5609/50000 : ℝ)) (X := (7554744374759901/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1749/12500 : ℝ) ^ (2059/512 : ℝ) ≤ (18371260333666149/50000000000000000000 : ℝ) := by
    have hpowers : (1749/12500 : ℝ)^2059 ≤ (18371260333666149/50000000000000000000 : ℝ)^512 := by
      have hnat : (1749 : ℕ)^2059*50000000000000000000^512 ≤ 18371260333666149^512*12500^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1749 12500 18371260333666149 50000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1749/12500 : ℝ)) (X := (18371260333666149/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007554744374759901/25000000000000000000 : ℝ) ≤ (5000375676550479/5000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (25007554744374759901/25000000000000000000 : ℝ)^512 ≤ (5000375676550479/5000000000000000 : ℝ)^2059 := by
      have hnat : (25007554744374759901 : ℕ)^512*5000000000000000^2059 ≤ 5000375676550479^2059*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007554744374759901 25000000000000000000 5000375676550479 5000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000375676550479/5000000000000000 : ℝ)) (X := (25007554744374759901/25000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000518520094168521/1000000000000000000 : ℝ) ≤ (10001289123799037/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (1000518520094168521/1000000000000000000 : ℝ)^512 ≤ (10001289123799037/10000000000000000 : ℝ)^2059 := by
      have hnat : (1000518520094168521 : ℕ)^512*10000000000000000^2059 ≤ 10001289123799037^2059*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000518520094168521 1000000000000000000 10001289123799037 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001289123799037/10000000000000000 : ℝ)) (X := (1000518520094168521/1000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018371260333666149/25000000000000000000 : ℝ) ≤ (2500456723624279/2500000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (25018371260333666149/25000000000000000000 : ℝ)^512 ≤ (2500456723624279/2500000000000000 : ℝ)^2059 := by
      have hnat : (25018371260333666149 : ℕ)^512*2500000000000000^2059 ≤ 2500456723624279^2059*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018371260333666149 25000000000000000000 2500456723624279 2500000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500456723624279/2500000000000000 : ℝ)) (X := (25018371260333666149/25000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7554744374759901/50000000000000000000 : ℝ) ≤ ((3466252353764994631/3467500000000000000 : ℝ)+2*(537770698079/277400000000000 : ℝ)*(5609/50000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (3466252353764994631/3467500000000000000 : ℝ)+2*(537770698079/277400000000000 : ℝ)*(5609/50000 : ℝ)=(5000375676550479/5000000000000000 : ℝ) by norm_num, show 1+2*(7554744374759901/50000000000000000000 : ℝ)=(25007554744374759901/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18371260333666149/50000000000000000000 : ℝ)+(7554744374759901/50000000000000000000 : ℝ) ≤ ((3466252353764994631/3467500000000000000 : ℝ)+(537770698079/277400000000000 : ℝ)*((1749/12500 : ℝ)+(5609/50000 : ℝ)))^(2059/512 : ℝ) := by
    rw [show (3466252353764994631/3467500000000000000 : ℝ)+(537770698079/277400000000000 : ℝ)*((1749/12500 : ℝ)+(5609/50000 : ℝ))=(10001289123799037/10000000000000000 : ℝ) by norm_num, show 1+(18371260333666149/50000000000000000000 : ℝ)+(7554744374759901/50000000000000000000 : ℝ)=(1000518520094168521/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18371260333666149/50000000000000000000 : ℝ) ≤ ((3466252353764994631/3467500000000000000 : ℝ)+2*(537770698079/277400000000000 : ℝ)*(1749/12500 : ℝ))^(2059/512 : ℝ) := by
    rw [show (3466252353764994631/3467500000000000000 : ℝ)+2*(537770698079/277400000000000 : ℝ)*(1749/12500 : ℝ)=(2500456723624279/2500000000000000 : ℝ) by norm_num, show 1+2*(18371260333666149/50000000000000000000 : ℝ)=(25018371260333666149/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3466252353764994631/3467500000000000000 : ℝ)*(X 1 0+X 2 0)+(537770698079/277400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (1749/12500 : ℝ)) (c := (3466252353764994631/3467500000000000000 : ℝ)) (alpha := (537770698079/277400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3466252353764994631/3467500000000000000 : ℝ)*(X 0 1+X 2 1)+(537770698079/277400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (1749/12500 : ℝ)) (c := (3466252353764994631/3467500000000000000 : ℝ)) (alpha := (537770698079/277400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3466252353764994631/3467500000000000000 : ℝ)*(X 0 2+X 1 2)+(537770698079/277400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (1749/12500 : ℝ)) (c := (3466252353764994631/3467500000000000000 : ℝ)) (alpha := (537770698079/277400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2214646701/10000000000 : ℝ)*X 0 0+(42146441/78125000 : ℝ)*X 0 1+(2632018049/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336256669/2500000000 : ℝ)*X 1 0+(-456194019/2000000000 : ℝ)*X 1 1+(2632018049/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534502667/1000000000 : ℝ)*X 2 0+(52640361/100000000 : ℝ)*X 2 1+(-2280970101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378665453/10000000000 : ℝ)*X 0 0+(4253030787/10000000000 : ℝ)*X 0 1+(4508082641/10000000000 : ℝ)*X 0 2+(4378665453/10000000000 : ℝ)*X 1 0+(4253030787/10000000000 : ℝ)*X 1 1+(4508082641/10000000000 : ℝ)*X 1 2+(4378665453/10000000000 : ℝ)*X 2 0+(4253030787/10000000000 : ℝ)*X 2 1+(4508082641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2214651797/10000000000 : ℝ)*X 0 0+(2632181621/5000000000 : ℝ)*X 0 1+(2697208073/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531216193/1000000000 : ℝ)*X 1 0+(-2150590117/10000000000 : ℝ)*X 1 1+(2697208027/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328040487/2500000000 : ℝ)*X 2 0+(2697208017/5000000000 : ℝ)*X 2 1+(-1075295059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378675231/10000000000 : ℝ)*X 0 0+(225372221/500000000 : ℝ)*X 0 1+(1063417881/2500000000 : ℝ)*X 0 2+(4378675231/10000000000 : ℝ)*X 1 0+(225372221/500000000 : ℝ)*X 1 1+(1063417881/2500000000 : ℝ)*X 1 2+(4378675231/10000000000 : ℝ)*X 2 0+(225372221/500000000 : ℝ)*X 2 1+(1063417881/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (231940281738780193303803513/86687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27603023/5000000000000 : ℝ)*(base19) + (63983933/12500000000000 : ℝ)*(base23) + (8445367/50000000000000 : ℝ)*(lower2) + (17924737/25000000000000 : ℝ)*(upper3) + (37555833/100000000000000 : ℝ)*(upper5) + (2892859487672341/50000000000000 : ℝ)*(major0) + (2892859487672341/50000000000000 : ℝ)*(major1) + (2892859487672341/50000000000000 : ℝ)*(major2) + (478164774470463/6250000000000 : ℝ)*(sp0) + (1530130078689881/20000000000000 : ℝ)*(sp1) + (7650650433638401/100000000000000 : ℝ)*(sp2) + (245048669312609/6250000000000 : ℝ)*(sp3) + (7276991229/50000000000000 : ℝ)*(sp4) + (1025873923/12500000000000 : ℝ)*(sp7) + (3920786915993129/100000000000000 : ℝ)*(f.failure) + (1530130189101973/20000000000000 : ℝ)*(f.sum) + (16258487829569/6935000000000000000000000000 : ℝ)*base65 + (604574258365561329/173375000000000000000000000000000 : ℝ)*base68 + (1191796517931561329/173375000000000000000000000000000 : ℝ)*base70 + (2252805578127438671/173375000000000000000000000000000 : ℝ)*base71 + (3079003907099/433437500000000000000000000 : ℝ)*base73 + (73923208219811329/173375000000000000000000000000000 : ℝ)*base76 + (18376908926311329/173375000000000000000000000000000 : ℝ)*base78 + (772987816914438671/173375000000000000000000000000000 : ℝ)*base79 + (25652168765087/3467500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (36825879/10000000000000000000000 : ℝ)*base90 + (36825879/10000000000000000000000 : ℝ)*base92 + (36825879/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6257031664243540003607919/1354492187500000000000000000000 : ℝ) := by norm_num
    linear_combination (147285129/20000000000000 : ℝ)*(base19) + (16777359/2000000000000 : ℝ)*(base23) + (8531997/25000000000000 : ℝ)*(upper2) + (20802537/50000000000000 : ℝ)*(upper3) + (9560803/25000000000000 : ℝ)*(upper5) + (1453713634315803/25000000000000 : ℝ)*(major0) + (1453713634315803/25000000000000 : ℝ)*(major1) + (1453713634315803/25000000000000 : ℝ)*(major2) + (17396961153/100000000000000 : ℝ)*(sp1) + (19359718621/100000000000000 : ℝ)*(sp2) + (7689177815376459/100000000000000 : ℝ)*(sp4) + (3844579840994831/50000000000000 : ℝ)*(sp5) + (60071543881171/781250000000 : ℝ)*(sp6) + (394053110516773/10000000000000 : ℝ)*(sp7) + (394053110516773/10000000000000 : ℝ)*(f.failure) + (7689177815376459/100000000000000 : ℝ)*(f.sum) + (21257378408329/6935000000000000000000000000 : ℝ)*base65 + (560681862715208807/86687500000000000000000000000000 : ℝ)*base68 + (1172551785669708807/86687500000000000000000000000000 : ℝ)*base70 + (400162102307708807/86687500000000000000000000000000 : ℝ)*base72 + (31405817412411/6935000000000000000000000000 : ℝ)*base74 + (1584545201840708807/86687500000000000000000000000000 : ℝ)*base76 + (1148684288802833807/86687500000000000000000000000000 : ℝ)*base78 + (39996437858666193/86687500000000000000000000000000 : ℝ)*base79 + (64531818575849/6935000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (6421477/1000000000000000000000 : ℝ)*base89 + (6421477/1000000000000000000000 : ℝ)*base91 + (6421477/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1044_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1044_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1044_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1044_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1044_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1044_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1044_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
