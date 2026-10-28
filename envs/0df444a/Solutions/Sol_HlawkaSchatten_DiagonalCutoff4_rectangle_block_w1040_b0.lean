-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1040_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:46:07.155099+00:00
-- url     : https://prove2.me/submissions/a594a494-ccce-409e-8ff0-ff6dde5880a0

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
theorem support_rectangle_w1040_s0_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2743530047/5000000000 : ℝ)*x 0 + (-2691243079/10000000000 : ℝ)*x 1 + (4795144729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2743530047/5000000000 : ℝ)^8233 ≤ (22490490491901/50000000000000 : ℝ)^6185 := by
    have hnat : (2743530047 : ℕ)^8233*50000000000000^6185 ≤ 22490490491901^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743530047 5000000000 22490490491901 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2691243079/10000000000 : ℝ)^8233 ≤ (2178245625051/12500000000000 : ℝ)^6185 := by
    have hnat : (2691243079 : ℕ)^8233*12500000000000^6185 ≤ 2178245625051^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691243079 10000000000 2178245625051 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4795144729/10000000000 : ℝ)^8233 ≤ (18796526999503/50000000000000 : ℝ)^6185 := by
    have hnat : (4795144729 : ℕ)^8233*50000000000000^6185 ≤ 18796526999503^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795144729 10000000000 18796526999503 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2743530047/5000000000 : ℝ), (-2691243079/10000000000 : ℝ), (4795144729/10000000000 : ℝ)] ![(22490490491901/50000000000000 : ℝ), (2178245625051/12500000000000 : ℝ), (18796526999503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2743530047/5000000000 : ℝ)|^8233 ≤ (22490490491901/50000000000000 : ℝ)^6185
        have hw : |(2743530047/5000000000 : ℝ)|=(2743530047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2691243079/10000000000 : ℝ)|^8233 ≤ (2178245625051/12500000000000 : ℝ)^6185
        have hw : |(-2691243079/10000000000 : ℝ)|=(2691243079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4795144729/10000000000 : ℝ)|^8233 ≤ (18796526999503/50000000000000 : ℝ)^6185
        have hw : |(4795144729/10000000000 : ℝ)|=(4795144729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s0_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2745924911/5000000000 : ℝ)*x 0 + (478243361/1000000000 : ℝ)*x 1 + (-337569551/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2745924911/5000000000 : ℝ)^8233 ≤ (45033254440151/100000000000000 : ℝ)^6185 := by
    have hnat : (2745924911 : ℕ)^8233*100000000000000^6185 ≤ 45033254440151^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745924911 5000000000 45033254440151 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478243361/1000000000 : ℝ)^8233 ≤ (37460461996877/100000000000000 : ℝ)^6185 := by
    have hnat : (478243361 : ℕ)^8233*100000000000000^6185 ≤ 37460461996877^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478243361 1000000000 37460461996877 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337569551/1250000000 : ℝ)^8233 ≤ (17506283545231/100000000000000 : ℝ)^6185 := by
    have hnat : (337569551 : ℕ)^8233*100000000000000^6185 ≤ 17506283545231^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337569551 1250000000 17506283545231 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2745924911/5000000000 : ℝ), (478243361/1000000000 : ℝ), (-337569551/1250000000 : ℝ)] ![(45033254440151/100000000000000 : ℝ), (37460461996877/100000000000000 : ℝ), (17506283545231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2745924911/5000000000 : ℝ)|^8233 ≤ (45033254440151/100000000000000 : ℝ)^6185
        have hw : |(2745924911/5000000000 : ℝ)|=(2745924911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(478243361/1000000000 : ℝ)|^8233 ≤ (37460461996877/100000000000000 : ℝ)^6185
        have hw : |(478243361/1000000000 : ℝ)|=(478243361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-337569551/1250000000 : ℝ)|^8233 ≤ (17506283545231/100000000000000 : ℝ)^6185
        have hw : |(-337569551/1250000000 : ℝ)|=(337569551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s0_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1929972317/10000000000 : ℝ)*x 0 + (4801293701/10000000000 : ℝ)*x 1 + (6043168547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1929972317/10000000000 : ℝ)^8233 ≤ (2238773280997/20000000000000 : ℝ)^6185 := by
    have hnat : (1929972317 : ℕ)^8233*20000000000000^6185 ≤ 2238773280997^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929972317 10000000000 2238773280997 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4801293701/10000000000 : ℝ)^8233 ≤ (9414309211691/25000000000000 : ℝ)^6185 := by
    have hnat : (4801293701 : ℕ)^8233*25000000000000^6185 ≤ 9414309211691^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4801293701 10000000000 9414309211691 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6043168547/10000000000 : ℝ)^8233 ≤ (51148896739073/100000000000000 : ℝ)^6185 := by
    have hnat : (6043168547 : ℕ)^8233*100000000000000^6185 ≤ 51148896739073^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6043168547 10000000000 51148896739073 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1929972317/10000000000 : ℝ), (4801293701/10000000000 : ℝ), (6043168547/10000000000 : ℝ)] ![(2238773280997/20000000000000 : ℝ), (9414309211691/25000000000000 : ℝ), (51148896739073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1929972317/10000000000 : ℝ)|^8233 ≤ (2238773280997/20000000000000 : ℝ)^6185
        have hw : |(-1929972317/10000000000 : ℝ)|=(1929972317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4801293701/10000000000 : ℝ)|^8233 ≤ (9414309211691/25000000000000 : ℝ)^6185
        have hw : |(4801293701/10000000000 : ℝ)|=(4801293701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6043168547/10000000000 : ℝ)|^8233 ≤ (51148896739073/100000000000000 : ℝ)^6185
        have hw : |(6043168547/10000000000 : ℝ)|=(6043168547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s0_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1291730323/2500000000 : ℝ)*x 0 + (-702027593/5000000000 : ℝ)*x 1 + (6043168721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1291730323/2500000000 : ℝ)^8233 ≤ (41521794784377/100000000000000 : ℝ)^6185 := by
    have hnat : (1291730323 : ℕ)^8233*100000000000000^6185 ≤ 41521794784377^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291730323 2500000000 41521794784377 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702027593/5000000000 : ℝ)^8233 ≤ (146586130117/2000000000000 : ℝ)^6185 := by
    have hnat : (702027593 : ℕ)^8233*2000000000000^6185 ≤ 146586130117^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702027593 5000000000 146586130117 2000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6043168721/10000000000 : ℝ)^8233 ≤ (6393612337431/12500000000000 : ℝ)^6185 := by
    have hnat : (6043168721 : ℕ)^8233*12500000000000^6185 ≤ 6393612337431^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6043168721 10000000000 6393612337431 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1291730323/2500000000 : ℝ), (-702027593/5000000000 : ℝ), (6043168721/10000000000 : ℝ)] ![(41521794784377/100000000000000 : ℝ), (146586130117/2000000000000 : ℝ), (6393612337431/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1291730323/2500000000 : ℝ)|^8233 ≤ (41521794784377/100000000000000 : ℝ)^6185
        have hw : |(1291730323/2500000000 : ℝ)|=(1291730323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-702027593/5000000000 : ℝ)|^8233 ≤ (146586130117/2000000000000 : ℝ)^6185
        have hw : |(-702027593/5000000000 : ℝ)|=(702027593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6043168721/10000000000 : ℝ)|^8233 ≤ (6393612337431/12500000000000 : ℝ)^6185
        have hw : |(6043168721/10000000000 : ℝ)|=(6043168721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s0_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2583458327/5000000000 : ℝ)*x 0 + (4721229/7812500 : ℝ)*x 1 + (-1404055193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583458327/5000000000 : ℝ)^8233 ≤ (2076087258581/5000000000000 : ℝ)^6185 := by
    have hnat : (2583458327 : ℕ)^8233*5000000000000^6185 ≤ 2076087258581^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583458327 5000000000 2076087258581 5000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4721229/7812500 : ℝ)^8233 ≤ (51148948260897/100000000000000 : ℝ)^6185 := by
    have hnat : (4721229 : ℕ)^8233*100000000000000^6185 ≤ 51148948260897^6185*7812500^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4721229 7812500 51148948260897 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1404055193/10000000000 : ℝ)^8233 ≤ (732930655449/10000000000000 : ℝ)^6185 := by
    have hnat : (1404055193 : ℕ)^8233*10000000000000^6185 ≤ 732930655449^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404055193 10000000000 732930655449 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583458327/5000000000 : ℝ), (4721229/7812500 : ℝ), (-1404055193/10000000000 : ℝ)] ![(2076087258581/5000000000000 : ℝ), (51148948260897/100000000000000 : ℝ), (732930655449/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583458327/5000000000 : ℝ)|^8233 ≤ (2076087258581/5000000000000 : ℝ)^6185
        have hw : |(2583458327/5000000000 : ℝ)|=(2583458327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4721229/7812500 : ℝ)|^8233 ≤ (51148948260897/100000000000000 : ℝ)^6185
        have hw : |(4721229/7812500 : ℝ)|=(4721229/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1404055193/10000000000 : ℝ)|^8233 ≤ (732930655449/10000000000000 : ℝ)^6185
        have hw : |(-1404055193/10000000000 : ℝ)|=(1404055193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s0_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (263749833/625000000 : ℝ)*x 0 + (5615952251/10000000000 : ℝ)*x 1 + (3194600351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263749833/625000000 : ℝ)^8233 ≤ (15856749551109/50000000000000 : ℝ)^6185 := by
    have hnat : (263749833 : ℕ)^8233*50000000000000^6185 ≤ 15856749551109^6185*625000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263749833 625000000 15856749551109 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5615952251/10000000000 : ℝ)^8233 ≤ (2319645215537/5000000000000 : ℝ)^6185 := by
    have hnat : (5615952251 : ℕ)^8233*5000000000000^6185 ≤ 2319645215537^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5615952251 10000000000 2319645215537 5000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3194600351/10000000000 : ℝ)^8233 ≤ (5473399143677/25000000000000 : ℝ)^6185 := by
    have hnat : (3194600351 : ℕ)^8233*25000000000000^6185 ≤ 5473399143677^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194600351 10000000000 5473399143677 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263749833/625000000 : ℝ), (5615952251/10000000000 : ℝ), (3194600351/10000000000 : ℝ)] ![(15856749551109/50000000000000 : ℝ), (2319645215537/5000000000000 : ℝ), (5473399143677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263749833/625000000 : ℝ)|^8233 ≤ (15856749551109/50000000000000 : ℝ)^6185
        have hw : |(263749833/625000000 : ℝ)|=(263749833/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5615952251/10000000000 : ℝ)|^8233 ≤ (2319645215537/5000000000000 : ℝ)^6185
        have hw : |(5615952251/10000000000 : ℝ)|=(5615952251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3194600351/10000000000 : ℝ)|^8233 ≤ (5473399143677/25000000000000 : ℝ)^6185
        have hw : |(3194600351/10000000000 : ℝ)|=(3194600351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (0 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28211/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base43 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
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
  have hpowlo : (0 : ℝ) ^ (1029/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1029 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1029*1^256 ≤ 0^256*1^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1029/256 : ℝ) ≤ (502918596833838791/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1029 ≤ (502918596833838791/20000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1029*20000000000000000000^256 ≤ 502918596833838791^256*5^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 502918596833838791 20000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (502918596833838791/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1029 := by
      have hnat : (1 : ℕ)^256*1^1029 ≤ 1^1029*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20502918596833838791/20000000000000000000 : ℝ) ≤ (10061977012007727/10000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (20502918596833838791/20000000000000000000 : ℝ)^256 ≤ (10061977012007727/10000000000000000 : ℝ)^1029 := by
      have hnat : (20502918596833838791 : ℕ)^256*10000000000000000^1029 ≤ 10061977012007727^1029*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20502918596833838791 20000000000000000000 10061977012007727 10000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061977012007727/10000000000000000 : ℝ)) (X := (20502918596833838791/20000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10502918596833838791/10000000000000000000 : ℝ) ≤ (5061977012007727/5000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (10502918596833838791/10000000000000000000 : ℝ)^256 ≤ (5061977012007727/5000000000000000 : ℝ)^1029 := by
      have hnat : (10502918596833838791 : ℕ)^256*5000000000000000^1029 ≤ 5061977012007727^1029*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10502918596833838791 10000000000000000000 5061977012007727 5000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5061977012007727/5000000000000000 : ℝ)) (X := (10502918596833838791/10000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(61977012007727/4000000000000000 : ℝ)*(0 : ℝ))^(1029/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(61977012007727/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(502918596833838791/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(61977012007727/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (1 : ℝ)+(61977012007727/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10061977012007727/10000000000000000 : ℝ) by norm_num, show 1+(502918596833838791/20000000000000000000 : ℝ)+(0 : ℝ)=(20502918596833838791/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(502918596833838791/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(61977012007727/4000000000000000 : ℝ)*(2/5 : ℝ))^(1029/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(61977012007727/4000000000000000 : ℝ)*(2/5 : ℝ)=(5061977012007727/5000000000000000 : ℝ) by norm_num, show 1+2*(502918596833838791/20000000000000000000 : ℝ)=(10502918596833838791/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(61977012007727/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61977012007727/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(61977012007727/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61977012007727/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(61977012007727/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61977012007727/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2743530047/5000000000 : ℝ)*X 1 0+(-2691243079/10000000000 : ℝ)*X 1 1+(4795144729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s0_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2745924911/5000000000 : ℝ)*X 2 0+(478243361/1000000000 : ℝ)*X 2 1+(-337569551/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s0_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1929972317/10000000000 : ℝ)*X 0 0+(4801293701/10000000000 : ℝ)*X 0 1+(6043168547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s0_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1291730323/2500000000 : ℝ)*X 1 0+(-702027593/5000000000 : ℝ)*X 1 1+(6043168721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s0_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2583458327/5000000000 : ℝ)*X 2 0+(4721229/7812500 : ℝ)*X 2 1+(-1404055193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s0_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((263749833/625000000 : ℝ)*X 0 0+(5615952251/10000000000 : ℝ)*X 0 1+(3194600351/10000000000 : ℝ)*X 0 2+(263749833/625000000 : ℝ)*X 1 0+(5615952251/10000000000 : ℝ)*X 1 1+(3194600351/10000000000 : ℝ)*X 1 2+(263749833/625000000 : ℝ)*X 2 0+(5615952251/10000000000 : ℝ)*X 2 1+(3194600351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s0_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base43) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (452093705444313303024507/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (890639893/100000000000000 : ℝ)*(base19) + (606143853/50000000000000 : ℝ)*(base23) + (34529407/4000000000000 : ℝ)*(base39) + (33863681/25000000000000 : ℝ)*(upper2) + (373773107/100000000000000 : ℝ)*(upper5) + (9517345821877/1562500000000 : ℝ)*(major0) + (9517345821877/1562500000000 : ℝ)*(major1) + (609109269364953/100000000000000 : ℝ)*(major2) + (36700231/1250000000000 : ℝ)*(sp0) + (1008585569/50000000000000 : ℝ)*(sp1) + (805228257928059/100000000000000 : ℝ)*(sp2) + (402612215634843/50000000000000 : ℝ)*(sp3) + (805225891704389/100000000000000 : ℝ)*(sp4) + (103247748334779/25000000000000 : ℝ)*(sp5) + (103247748334779/25000000000000 : ℝ)*(f.failure) + (402614560581617/50000000000000 : ℝ)*(f.sum) + (1561901218180887/400000000000000000000000000000 : ℝ)*base65 + (914022228991831/400000000000000000000000000000 : ℝ)*base67 + (27359747787671/6250000000000000000000000000 : ℝ)*base70 + (167795426991831/400000000000000000000000000000 : ℝ)*base71 + (951013516180887/400000000000000000000000000000 : ℝ)*base73 + (26308018118921/6250000000000000000000000000 : ℝ)*base76 + (45874477831079/6250000000000000000000000000 : ℝ)*base77 + (32531927293579/6250000000000000000000000000 : ℝ)*base79 + (503701034787/390625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (111029/250000000000000000000 : ℝ)*base89 + (111029/250000000000000000000 : ℝ)*base91 + (111029/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1040_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28211/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1040_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1040_s1_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267060407/1250000000 : ℝ)*x 0 + (5729564153/10000000000 : ℝ)*x 1 + (4980322661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267060407/1250000000 : ℝ)^8233 ≤ (12815841241229/100000000000000 : ℝ)^6185 := by
    have hnat : (267060407 : ℕ)^8233*100000000000000^6185 ≤ 12815841241229^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267060407 1250000000 12815841241229 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5729564153/10000000000 : ℝ)^8233 ≤ (47646380493143/100000000000000 : ℝ)^6185 := by
    have hnat : (5729564153 : ℕ)^8233*100000000000000^6185 ≤ 47646380493143^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5729564153 10000000000 47646380493143 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4980322661/10000000000 : ℝ)^8233 ≤ (3953777824631/10000000000000 : ℝ)^6185 := by
    have hnat : (4980322661 : ℕ)^8233*10000000000000^6185 ≤ 3953777824631^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4980322661 10000000000 3953777824631 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267060407/1250000000 : ℝ), (5729564153/10000000000 : ℝ), (4980322661/10000000000 : ℝ)] ![(12815841241229/100000000000000 : ℝ), (47646380493143/100000000000000 : ℝ), (3953777824631/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267060407/1250000000 : ℝ)|^8233 ≤ (12815841241229/100000000000000 : ℝ)^6185
        have hw : |(-267060407/1250000000 : ℝ)|=(267060407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5729564153/10000000000 : ℝ)|^8233 ≤ (47646380493143/100000000000000 : ℝ)^6185
        have hw : |(5729564153/10000000000 : ℝ)|=(5729564153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4980322661/10000000000 : ℝ)|^8233 ≤ (3953777824631/10000000000000 : ℝ)^6185
        have hw : |(4980322661/10000000000 : ℝ)|=(4980322661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s1_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (135618747/250000000 : ℝ)*x 0 + (-2542982157/10000000000 : ℝ)*x 1 + (4980322981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135618747/250000000 : ℝ)^8233 ≤ (5537791052157/12500000000000 : ℝ)^6185 := by
    have hnat : (135618747 : ℕ)^8233*12500000000000^6185 ≤ 5537791052157^6185*250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135618747 250000000 5537791052157 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542982157/10000000000 : ℝ)^8233 ≤ (16159889939981/100000000000000 : ℝ)^6185 := by
    have hnat : (2542982157 : ℕ)^8233*100000000000000^6185 ≤ 16159889939981^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542982157 10000000000 16159889939981 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4980322981/10000000000 : ℝ)^8233 ≤ (39537781627917/100000000000000 : ℝ)^6185 := by
    have hnat : (4980322981 : ℕ)^8233*100000000000000^6185 ≤ 39537781627917^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4980322981 10000000000 39537781627917 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135618747/250000000 : ℝ), (-2542982157/10000000000 : ℝ), (4980322981/10000000000 : ℝ)] ![(5537791052157/12500000000000 : ℝ), (16159889939981/100000000000000 : ℝ), (39537781627917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135618747/250000000 : ℝ)|^8233 ≤ (5537791052157/12500000000000 : ℝ)^6185
        have hw : |(135618747/250000000 : ℝ)|=(135618747/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2542982157/10000000000 : ℝ)|^8233 ≤ (16159889939981/100000000000000 : ℝ)^6185
        have hw : |(-2542982157/10000000000 : ℝ)|=(2542982157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4980322981/10000000000 : ℝ)|^8233 ≤ (39537781627917/100000000000000 : ℝ)^6185
        have hw : |(4980322981/10000000000 : ℝ)|=(4980322981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s1_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (21699001/40000000 : ℝ)*x 0 + (2490161257/5000000000 : ℝ)*x 1 + (-508596453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21699001/40000000 : ℝ)^8233 ≤ (22151166219743/50000000000000 : ℝ)^6185 := by
    have hnat : (21699001 : ℕ)^8233*50000000000000^6185 ≤ 22151166219743^6185*40000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21699001 40000000 22151166219743 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2490161257/5000000000 : ℝ)^8233 ≤ (9884444173221/25000000000000 : ℝ)^6185 := by
    have hnat : (2490161257 : ℕ)^8233*25000000000000^6185 ≤ 9884444173221^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490161257 5000000000 9884444173221 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508596453/2000000000 : ℝ)^8233 ≤ (16159890853541/100000000000000 : ℝ)^6185 := by
    have hnat : (508596453 : ℕ)^8233*100000000000000^6185 ≤ 16159890853541^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508596453 2000000000 16159890853541 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21699001/40000000 : ℝ), (2490161257/5000000000 : ℝ), (-508596453/2000000000 : ℝ)] ![(22151166219743/50000000000000 : ℝ), (9884444173221/25000000000000 : ℝ), (16159890853541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21699001/40000000 : ℝ)|^8233 ≤ (22151166219743/50000000000000 : ℝ)^6185
        have hw : |(21699001/40000000 : ℝ)|=(21699001/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2490161257/5000000000 : ℝ)|^8233 ≤ (9884444173221/25000000000000 : ℝ)^6185
        have hw : |(2490161257/5000000000 : ℝ)|=(2490161257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508596453/2000000000 : ℝ)|^8233 ≤ (16159890853541/100000000000000 : ℝ)^6185
        have hw : |(-508596453/2000000000 : ℝ)|=(508596453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s1_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2162989971/5000000000 : ℝ)*x 0 + (3657718187/10000000000 : ℝ)*x 1 + (2559275313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162989971/5000000000 : ℝ)^8233 ≤ (6555615232893/20000000000000 : ℝ)^6185 := by
    have hnat : (2162989971 : ℕ)^8233*20000000000000^6185 ≤ 6555615232893^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162989971 5000000000 6555615232893 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3657718187/10000000000 : ℝ)^8233 ≤ (13108373614769/50000000000000 : ℝ)^6185 := by
    have hnat : (3657718187 : ℕ)^8233*50000000000000^6185 ≤ 13108373614769^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3657718187 10000000000 13108373614769 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2559275313/5000000000 : ℝ)^8233 ≤ (20502588298189/50000000000000 : ℝ)^6185 := by
    have hnat : (2559275313 : ℕ)^8233*50000000000000^6185 ≤ 20502588298189^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559275313 5000000000 20502588298189 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162989971/5000000000 : ℝ), (3657718187/10000000000 : ℝ), (2559275313/5000000000 : ℝ)] ![(6555615232893/20000000000000 : ℝ), (13108373614769/50000000000000 : ℝ), (20502588298189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162989971/5000000000 : ℝ)|^8233 ≤ (6555615232893/20000000000000 : ℝ)^6185
        have hw : |(2162989971/5000000000 : ℝ)|=(2162989971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3657718187/10000000000 : ℝ)|^8233 ≤ (13108373614769/50000000000000 : ℝ)^6185
        have hw : |(3657718187/10000000000 : ℝ)|=(3657718187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2559275313/5000000000 : ℝ)|^8233 ≤ (20502588298189/50000000000000 : ℝ)^6185
        have hw : |(2559275313/5000000000 : ℝ)|=(2559275313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s1_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-534361523/2500000000 : ℝ)*x 0 + (4990952243/10000000000 : ℝ)*x 1 + (1143743/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534361523/2500000000 : ℝ)^8233 ≤ (3205882475749/25000000000000 : ℝ)^6185 := by
    have hnat : (534361523 : ℕ)^8233*25000000000000^6185 ≤ 3205882475749^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534361523 2500000000 3205882475749 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4990952243/10000000000 : ℝ)^8233 ≤ (39650146269763/100000000000000 : ℝ)^6185 := by
    have hnat : (4990952243 : ℕ)^8233*100000000000000^6185 ≤ 39650146269763^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990952243 10000000000 39650146269763 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143743/2000000 : ℝ)^8233 ≤ (2376316190453/5000000000000 : ℝ)^6185 := by
    have hnat : (1143743 : ℕ)^8233*5000000000000^6185 ≤ 2376316190453^6185*2000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143743 2000000 2376316190453 5000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534361523/2500000000 : ℝ), (4990952243/10000000000 : ℝ), (1143743/2000000 : ℝ)] ![(3205882475749/25000000000000 : ℝ), (39650146269763/100000000000000 : ℝ), (2376316190453/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534361523/2500000000 : ℝ)|^8233 ≤ (3205882475749/25000000000000 : ℝ)^6185
        have hw : |(-534361523/2500000000 : ℝ)|=(534361523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4990952243/10000000000 : ℝ)|^8233 ≤ (39650146269763/100000000000000 : ℝ)^6185
        have hw : |(4990952243/10000000000 : ℝ)|=(4990952243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1143743/2000000 : ℝ)|^8233 ≤ (2376316190453/5000000000000 : ℝ)^6185
        have hw : |(1143743/2000000 : ℝ)|=(1143743/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s1_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5233663479/10000000000 : ℝ)*x 0 + (-225573577/1250000000 : ℝ)*x 1 + (1429679031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5233663479/10000000000 : ℝ)^8233 ≤ (42237259549383/100000000000000 : ℝ)^6185 := by
    have hnat : (5233663479 : ℕ)^8233*100000000000000^6185 ≤ 42237259549383^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233663479 10000000000 42237259549383 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225573577/1250000000 : ℝ)^8233 ≤ (2559101048733/25000000000000 : ℝ)^6185 := by
    have hnat : (225573577 : ℕ)^8233*25000000000000^6185 ≤ 2559101048733^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225573577 1250000000 2559101048733 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1429679031/2500000000 : ℝ)^8233 ≤ (47526336243337/100000000000000 : ℝ)^6185 := by
    have hnat : (1429679031 : ℕ)^8233*100000000000000^6185 ≤ 47526336243337^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429679031 2500000000 47526336243337 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5233663479/10000000000 : ℝ), (-225573577/1250000000 : ℝ), (1429679031/2500000000 : ℝ)] ![(42237259549383/100000000000000 : ℝ), (2559101048733/25000000000000 : ℝ), (47526336243337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5233663479/10000000000 : ℝ)|^8233 ≤ (42237259549383/100000000000000 : ℝ)^6185
        have hw : |(5233663479/10000000000 : ℝ)|=(5233663479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-225573577/1250000000 : ℝ)|^8233 ≤ (2559101048733/25000000000000 : ℝ)^6185
        have hw : |(-225573577/1250000000 : ℝ)|=(225573577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1429679031/2500000000 : ℝ)|^8233 ≤ (47526336243337/100000000000000 : ℝ)^6185
        have hw : |(1429679031/2500000000 : ℝ)|=(1429679031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s1_6 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (654207701/1250000000 : ℝ)*x 0 + (178709943/312500000 : ℝ)*x 1 + (-180458827/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654207701/1250000000 : ℝ)^8233 ≤ (10559309862507/25000000000000 : ℝ)^6185 := by
    have hnat : (654207701 : ℕ)^8233*25000000000000^6185 ≤ 10559309862507^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654207701 1250000000 10559309862507 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178709943/312500000 : ℝ)^8233 ≤ (11881589735909/25000000000000 : ℝ)^6185 := by
    have hnat : (178709943 : ℕ)^8233*25000000000000^6185 ≤ 11881589735909^6185*312500000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178709943 312500000 11881589735909 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180458827/1000000000 : ℝ)^8233 ≤ (2559100395597/25000000000000 : ℝ)^6185 := by
    have hnat : (180458827 : ℕ)^8233*25000000000000^6185 ≤ 2559100395597^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180458827 1000000000 2559100395597 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(654207701/1250000000 : ℝ), (178709943/312500000 : ℝ), (-180458827/1000000000 : ℝ)] ![(10559309862507/25000000000000 : ℝ), (11881589735909/25000000000000 : ℝ), (2559100395597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(654207701/1250000000 : ℝ)|^8233 ≤ (10559309862507/25000000000000 : ℝ)^6185
        have hw : |(654207701/1250000000 : ℝ)|=(654207701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(178709943/312500000 : ℝ)|^8233 ≤ (11881589735909/25000000000000 : ℝ)^6185
        have hw : |(178709943/312500000 : ℝ)|=(178709943/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-180458827/1000000000 : ℝ)|^8233 ≤ (2559100395597/25000000000000 : ℝ)^6185
        have hw : |(-180458827/1000000000 : ℝ)|=(180458827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s1_7 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4327854227/10000000000 : ℝ)*x 0 + (1019564457/2000000000 : ℝ)*x 1 + (459858607/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327854227/10000000000 : ℝ)^8233 ≤ (6559396297897/20000000000000 : ℝ)^6185 := by
    have hnat : (4327854227 : ℕ)^8233*20000000000000^6185 ≤ 6559396297897^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327854227 10000000000 6559396297897 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019564457/2000000000 : ℝ)^8233 ≤ (1019607075357/2500000000000 : ℝ)^6185 := by
    have hnat : (1019564457 : ℕ)^8233*2500000000000^6185 ≤ 1019607075357^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019564457 2000000000 1019607075357 2500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459858607/1250000000 : ℝ)^8233 ≤ (26418735489153/100000000000000 : ℝ)^6185 := by
    have hnat : (459858607 : ℕ)^8233*100000000000000^6185 ≤ 26418735489153^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459858607 1250000000 26418735489153 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327854227/10000000000 : ℝ), (1019564457/2000000000 : ℝ), (459858607/1250000000 : ℝ)] ![(6559396297897/20000000000000 : ℝ), (1019607075357/2500000000000 : ℝ), (26418735489153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327854227/10000000000 : ℝ)|^8233 ≤ (6559396297897/20000000000000 : ℝ)^6185
        have hw : |(4327854227/10000000000 : ℝ)|=(4327854227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1019564457/2000000000 : ℝ)|^8233 ≤ (1019607075357/2500000000000 : ℝ)^6185
        have hw : |(1019564457/2000000000 : ℝ)|=(1019564457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(459858607/1250000000 : ℝ)|^8233 ≤ (26418735489153/100000000000000 : ℝ)^6185
        have hw : |(459858607/1250000000 : ℝ)|=(459858607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2531/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10457/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28211/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28211/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28211/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28211/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28211/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28211/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (0 : ℝ) ^ (1029/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1029 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1029*1^256 ≤ 0^256*1^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (28211/100000 : ℝ) ^ (1029/256 : ℝ) ≤ (617930895437121597/100000000000000000000 : ℝ) := by
    have hpowers : (28211/100000 : ℝ)^1029 ≤ (617930895437121597/100000000000000000000 : ℝ)^256 := by
      have hnat : (28211 : ℕ)^1029*100000000000000000000^256 ≤ 617930895437121597^256*100000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28211 100000 617930895437121597 100000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28211/100000 : ℝ)) (X := (617930895437121597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1029 := by
      have hnat : (1 : ℕ)^256*1^1029 ≤ 1^1029*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100617930895437121597/100000000000000000000 : ℝ) ≤ (10015337654930563/10000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (100617930895437121597/100000000000000000000 : ℝ)^256 ≤ (10015337654930563/10000000000000000 : ℝ)^1029 := by
      have hnat : (100617930895437121597 : ℕ)^256*10000000000000000^1029 ≤ 10015337654930563^1029*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100617930895437121597 100000000000000000000 10015337654930563 10000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015337654930563/10000000000000000 : ℝ)) (X := (100617930895437121597/100000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50617930895437121597/50000000000000000000 : ℝ) ≤ (5015337654930563/5000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50617930895437121597/50000000000000000000 : ℝ)^256 ≤ (5015337654930563/5000000000000000 : ℝ)^1029 := by
      have hnat : (50617930895437121597 : ℕ)^256*5000000000000000^1029 ≤ 5015337654930563^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50617930895437121597 50000000000000000000 5015337654930563 5000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015337654930563/5000000000000000 : ℝ)) (X := (50617930895437121597/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15337654930563/2821100000000000 : ℝ)*(0 : ℝ))^(1029/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(15337654930563/2821100000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(617930895437121597/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15337654930563/2821100000000000 : ℝ)*((28211/100000 : ℝ)+(0 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (1 : ℝ)+(15337654930563/2821100000000000 : ℝ)*((28211/100000 : ℝ)+(0 : ℝ))=(10015337654930563/10000000000000000 : ℝ) by norm_num, show 1+(617930895437121597/100000000000000000000 : ℝ)+(0 : ℝ)=(100617930895437121597/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(617930895437121597/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15337654930563/2821100000000000 : ℝ)*(28211/100000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(15337654930563/2821100000000000 : ℝ)*(28211/100000 : ℝ)=(5015337654930563/5000000000000000 : ℝ) by norm_num, show 1+2*(617930895437121597/100000000000000000000 : ℝ)=(50617930895437121597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15337654930563/2821100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (0 : ℝ)) (hi := (28211/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15337654930563/2821100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15337654930563/2821100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (0 : ℝ)) (hi := (28211/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15337654930563/2821100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15337654930563/2821100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (0 : ℝ)) (hi := (28211/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15337654930563/2821100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-267060407/1250000000 : ℝ)*X 0 0+(5729564153/10000000000 : ℝ)*X 0 1+(4980322661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((135618747/250000000 : ℝ)*X 1 0+(-2542982157/10000000000 : ℝ)*X 1 1+(4980322981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21699001/40000000 : ℝ)*X 2 0+(2490161257/5000000000 : ℝ)*X 2 1+(-508596453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162989971/5000000000 : ℝ)*X 0 0+(3657718187/10000000000 : ℝ)*X 0 1+(2559275313/5000000000 : ℝ)*X 0 2+(2162989971/5000000000 : ℝ)*X 1 0+(3657718187/10000000000 : ℝ)*X 1 1+(2559275313/5000000000 : ℝ)*X 1 2+(2162989971/5000000000 : ℝ)*X 2 0+(3657718187/10000000000 : ℝ)*X 2 1+(2559275313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-534361523/2500000000 : ℝ)*X 0 0+(4990952243/10000000000 : ℝ)*X 0 1+(1143743/2000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5233663479/10000000000 : ℝ)*X 1 0+(-225573577/1250000000 : ℝ)*X 1 1+(1429679031/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((654207701/1250000000 : ℝ)*X 2 0+(178709943/312500000 : ℝ)*X 2 1+(-180458827/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327854227/10000000000 : ℝ)*X 0 0+(1019564457/2000000000 : ℝ)*X 0 1+(459858607/1250000000 : ℝ)*X 0 2+(4327854227/10000000000 : ℝ)*X 1 0+(1019564457/2000000000 : ℝ)*X 1 1+(459858607/1250000000 : ℝ)*X 1 2+(4327854227/10000000000 : ℝ)*X 2 0+(1019564457/2000000000 : ℝ)*X 2 1+(459858607/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101821584306103146020271/70527500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1267533/2500000000000 : ℝ)*(base1) + (69061121/20000000000000 : ℝ)*(base19) + (436339113/100000000000000 : ℝ)*(base23) + (5433853/12500000000000 : ℝ)*(upper3) + (6493567/20000000000000 : ℝ)*(upper5) + (504807395595443/50000000000000 : ℝ)*(major0) + (504807395595443/50000000000000 : ℝ)*(major1) + (504807395595443/50000000000000 : ℝ)*(major2) + (13346850199371/1000000000000 : ℝ)*(sp0) + (667343309541301/50000000000000 : ℝ)*(sp1) + (1334686528049093/100000000000000 : ℝ)*(sp2) + (3422708923249/500000000000 : ℝ)*(sp3) + (1995152427/100000000000000 : ℝ)*(sp4) + (734518617/100000000000000 : ℝ)*(sp7) + (684542569869737/100000000000000 : ℝ)*(f.failure) + (667343482194103/50000000000000 : ℝ)*(f.sum) + (542753016071193/141055000000000000000000000000 : ℝ)*base65 + (47713333809421/141055000000000000000000000000 : ℝ)*base68 + (113287341335451/141055000000000000000000000000 : ℝ)*base70 + (70210429314341/35263750000000000000000000000 : ℝ)*base71 + (338016316381613/141055000000000000000000000000 : ℝ)*base73 + (114946918357139/141055000000000000000000000000 : ℝ)*base75 + (256478409607707/70527500000000000000000000000 : ℝ)*base77 + (74352556901489/8815937500000000000000000000 : ℝ)*base79 + (210006532060067/141055000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (6551513/1000000000000000000000 : ℝ)*base90 + (6551513/1000000000000000000000 : ℝ)*base92 + (6551513/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214917471370905379320069/70527500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2255168113/100000000000000 : ℝ)*(base19) + (2103205133/100000000000000 : ℝ)*(base23) + (166838263/100000000000000 : ℝ)*(upper2) + (163410911/50000000000000 : ℝ)*(upper3) + (476057189/100000000000000 : ℝ)*(upper5) + (519704366206639/50000000000000 : ℝ)*(major0) + (519704366206639/50000000000000 : ℝ)*(major1) + (519704366206639/50000000000000 : ℝ)*(major2) + (2148247363/20000000000000 : ℝ)*(sp1) + (2825503759/25000000000000 : ℝ)*(sp2) + (687036900308477/50000000000000 : ℝ)*(sp4) + (687030402106013/50000000000000 : ℝ)*(sp5) + (274812079079357/20000000000000 : ℝ)*(sp6) + (704743562633391/100000000000000 : ℝ)*(sp7) + (704743562633391/100000000000000 : ℝ)*(f.failure) + (687036900308477/50000000000000 : ℝ)*(f.sum) + (396390533982881/141055000000000000000000000000 : ℝ)*base66 + (945027126336689/70527500000000000000000000000 : ℝ)*base68 + (1356899421466523/141055000000000000000000000000 : ℝ)*base70 + (131889801898231/17631875000000000000000000000 : ℝ)*base72 + (9468083197003/70527500000000000000000000000 : ℝ)*base74 + (173395218439521/17631875000000000000000000000 : ℝ)*base76 + (707704682838139/70527500000000000000000000000 : ℝ)*base78 + (185453299190211/17631875000000000000000000000 : ℝ)*base80 + (3292639306023/17631875000000000000000000000 : ℝ)*base81 + (8144641/1000000000000000000000 : ℝ)*base89 + (8144641/1000000000000000000000 : ℝ)*base91 + (8144641/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1040_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2531/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10457/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1040_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1040_s2_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-548853957/2500000000 : ℝ)*x 0 + (5531304417/10000000000 : ℝ)*x 1 + (40165737/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548853957/2500000000 : ℝ)^8233 ≤ (6644272071021/50000000000000 : ℝ)^6185 := by
    have hnat : (548853957 : ℕ)^8233*50000000000000^6185 ≤ 6644272071021^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548853957 2500000000 6644272071021 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5531304417/10000000000 : ℝ)^8233 ≤ (11366105509003/25000000000000 : ℝ)^6185 := by
    have hnat : (5531304417 : ℕ)^8233*25000000000000^6185 ≤ 11366105509003^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531304417 10000000000 11366105509003 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40165737/78125000 : ℝ)^8233 ≤ (2577939612827/6250000000000 : ℝ)^6185 := by
    have hnat : (40165737 : ℕ)^8233*6250000000000^6185 ≤ 2577939612827^6185*78125000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40165737 78125000 2577939612827 6250000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548853957/2500000000 : ℝ), (5531304417/10000000000 : ℝ), (40165737/78125000 : ℝ)] ![(6644272071021/50000000000000 : ℝ), (11366105509003/25000000000000 : ℝ), (2577939612827/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548853957/2500000000 : ℝ)|^8233 ≤ (6644272071021/50000000000000 : ℝ)^6185
        have hw : |(-548853957/2500000000 : ℝ)|=(548853957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5531304417/10000000000 : ℝ)|^8233 ≤ (11366105509003/25000000000000 : ℝ)^6185
        have hw : |(5531304417/10000000000 : ℝ)|=(5531304417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40165737/78125000 : ℝ)|^8233 ≤ (2577939612827/6250000000000 : ℝ)^6185
        have hw : |(40165737/78125000 : ℝ)|=(40165737/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s2_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2689181967/5000000000 : ℝ)*x 0 + (-23990791/100000000 : ℝ)*x 1 + (1285303537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689181967/5000000000 : ℝ)^8233 ≤ (8759757393813/20000000000000 : ℝ)^6185 := by
    have hnat : (2689181967 : ℕ)^8233*20000000000000^6185 ≤ 8759757393813^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689181967 5000000000 8759757393813 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23990791/100000000 : ℝ)^8233 ≤ (1495418121351/10000000000000 : ℝ)^6185 := by
    have hnat : (23990791 : ℕ)^8233*10000000000000^6185 ≤ 1495418121351^6185*100000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23990791 100000000 1495418121351 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1285303537/2500000000 : ℝ)^8233 ≤ (5155878974689/12500000000000 : ℝ)^6185 := by
    have hnat : (1285303537 : ℕ)^8233*12500000000000^6185 ≤ 5155878974689^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285303537 2500000000 5155878974689 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689181967/5000000000 : ℝ), (-23990791/100000000 : ℝ), (1285303537/2500000000 : ℝ)] ![(8759757393813/20000000000000 : ℝ), (1495418121351/10000000000000 : ℝ), (5155878974689/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689181967/5000000000 : ℝ)|^8233 ≤ (8759757393813/20000000000000 : ℝ)^6185
        have hw : |(2689181967/5000000000 : ℝ)|=(2689181967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23990791/100000000 : ℝ)|^8233 ≤ (1495418121351/10000000000000 : ℝ)^6185
        have hw : |(-23990791/100000000 : ℝ)|=(23990791/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1285303537/2500000000 : ℝ)|^8233 ≤ (5155878974689/12500000000000 : ℝ)^6185
        have hw : |(1285303537/2500000000 : ℝ)|=(1285303537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s2_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2689182027/5000000000 : ℝ)*x 0 + (102824281/200000000 : ℝ)*x 1 + (-239907907/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689182027/5000000000 : ℝ)^8233 ≤ (10949697067467/25000000000000 : ℝ)^6185 := by
    have hnat : (2689182027 : ℕ)^8233*25000000000000^6185 ≤ 10949697067467^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689182027 5000000000 10949697067467 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102824281/200000000 : ℝ)^8233 ≤ (20623515375467/50000000000000 : ℝ)^6185 := by
    have hnat : (102824281 : ℕ)^8233*50000000000000^6185 ≤ 20623515375467^6185*200000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102824281 200000000 20623515375467 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239907907/1000000000 : ℝ)^8233 ≤ (14954180964591/100000000000000 : ℝ)^6185 := by
    have hnat : (239907907 : ℕ)^8233*100000000000000^6185 ≤ 14954180964591^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239907907 1000000000 14954180964591 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689182027/5000000000 : ℝ), (102824281/200000000 : ℝ), (-239907907/1000000000 : ℝ)] ![(10949697067467/25000000000000 : ℝ), (20623515375467/50000000000000 : ℝ), (14954180964591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689182027/5000000000 : ℝ)|^8233 ≤ (10949697067467/25000000000000 : ℝ)^6185
        have hw : |(2689182027/5000000000 : ℝ)|=(2689182027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(102824281/200000000 : ℝ)|^8233 ≤ (20623515375467/50000000000000 : ℝ)^6185
        have hw : |(102824281/200000000 : ℝ)|=(102824281/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-239907907/1000000000 : ℝ)|^8233 ≤ (14954180964591/100000000000000 : ℝ)^6185
        have hw : |(-239907907/1000000000 : ℝ)|=(239907907/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s2_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366067011/10000000000 : ℝ)*x 0 + (4002580809/10000000000 : ℝ)*x 1 + (1190789993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366067011/10000000000 : ℝ)^8233 ≤ (8295752970477/25000000000000 : ℝ)^6185 := by
    have hnat : (4366067011 : ℕ)^8233*25000000000000^6185 ≤ 8295752970477^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366067011 10000000000 8295752970477 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4002580809/10000000000 : ℝ)^8233 ≤ (5911470073201/20000000000000 : ℝ)^6185 := by
    have hnat : (4002580809 : ℕ)^8233*20000000000000^6185 ≤ 5911470073201^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002580809 10000000000 5911470073201 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1190789993/2500000000 : ℝ)^8233 ≤ (37259637745401/100000000000000 : ℝ)^6185 := by
    have hnat : (1190789993 : ℕ)^8233*100000000000000^6185 ≤ 37259637745401^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190789993 2500000000 37259637745401 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366067011/10000000000 : ℝ), (4002580809/10000000000 : ℝ), (1190789993/2500000000 : ℝ)] ![(8295752970477/25000000000000 : ℝ), (5911470073201/20000000000000 : ℝ), (37259637745401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366067011/10000000000 : ℝ)|^8233 ≤ (8295752970477/25000000000000 : ℝ)^6185
        have hw : |(4366067011/10000000000 : ℝ)|=(4366067011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4002580809/10000000000 : ℝ)|^8233 ≤ (5911470073201/20000000000000 : ℝ)^6185
        have hw : |(4002580809/10000000000 : ℝ)|=(4002580809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1190789993/2500000000 : ℝ)|^8233 ≤ (37259637745401/100000000000000 : ℝ)^6185
        have hw : |(1190789993/2500000000 : ℝ)|=(1190789993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s2_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195551121/10000000000 : ℝ)*x 0 + (5144103277/10000000000 : ℝ)*x 1 + (5528384447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195551121/10000000000 : ℝ)^8233 ≤ (415301069471/3125000000000 : ℝ)^6185 := by
    have hnat : (2195551121 : ℕ)^8233*3125000000000^6185 ≤ 415301069471^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195551121 10000000000 415301069471 3125000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144103277/10000000000 : ℝ)^8233 ≤ (41277888730089/100000000000000 : ℝ)^6185 := by
    have hnat : (5144103277 : ℕ)^8233*100000000000000^6185 ≤ 41277888730089^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144103277 10000000000 41277888730089 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5528384447/10000000000 : ℝ)^8233 ≤ (35494122681/78125000000 : ℝ)^6185 := by
    have hnat : (5528384447 : ℕ)^8233*78125000000^6185 ≤ 35494122681^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528384447 10000000000 35494122681 78125000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195551121/10000000000 : ℝ), (5144103277/10000000000 : ℝ), (5528384447/10000000000 : ℝ)] ![(415301069471/3125000000000 : ℝ), (41277888730089/100000000000000 : ℝ), (35494122681/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195551121/10000000000 : ℝ)|^8233 ≤ (415301069471/3125000000000 : ℝ)^6185
        have hw : |(-2195551121/10000000000 : ℝ)|=(2195551121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144103277/10000000000 : ℝ)|^8233 ≤ (41277888730089/100000000000000 : ℝ)^6185
        have hw : |(5144103277/10000000000 : ℝ)|=(5144103277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5528384447/10000000000 : ℝ)|^8233 ≤ (35494122681/78125000000 : ℝ)^6185
        have hw : |(5528384447/10000000000 : ℝ)|=(5528384447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s2_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5280083029/10000000000 : ℝ)*x 0 + (-201190899/1000000000 : ℝ)*x 1 + (691048063/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280083029/10000000000 : ℝ)^8233 ≤ (10684163952831/25000000000000 : ℝ)^6185 := by
    have hnat : (5280083029 : ℕ)^8233*25000000000000^6185 ≤ 10684163952831^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280083029 10000000000 10684163952831 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201190899/1000000000 : ℝ)^8233 ≤ (5915433262963/50000000000000 : ℝ)^6185 := by
    have hnat : (201190899 : ℕ)^8233*50000000000000^6185 ≤ 5915433262963^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201190899 1000000000 5915433262963 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691048063/1250000000 : ℝ)^8233 ≤ (2839529853451/6250000000000 : ℝ)^6185 := by
    have hnat : (691048063 : ℕ)^8233*6250000000000^6185 ≤ 2839529853451^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691048063 1250000000 2839529853451 6250000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280083029/10000000000 : ℝ), (-201190899/1000000000 : ℝ), (691048063/1250000000 : ℝ)] ![(10684163952831/25000000000000 : ℝ), (5915433262963/50000000000000 : ℝ), (2839529853451/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280083029/10000000000 : ℝ)|^8233 ≤ (10684163952831/25000000000000 : ℝ)^6185
        have hw : |(5280083029/10000000000 : ℝ)|=(5280083029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201190899/1000000000 : ℝ)|^8233 ≤ (5915433262963/50000000000000 : ℝ)^6185
        have hw : |(-201190899/1000000000 : ℝ)|=(201190899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(691048063/1250000000 : ℝ)|^8233 ≤ (2839529853451/6250000000000 : ℝ)^6185
        have hw : |(691048063/1250000000 : ℝ)|=(691048063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s2_6 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132002081/250000000 : ℝ)*x 0 + (5528384351/10000000000 : ℝ)*x 1 + (-2011908913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132002081/250000000 : ℝ)^8233 ≤ (8547331616929/20000000000000 : ℝ)^6185 := by
    have hnat : (132002081 : ℕ)^8233*20000000000000^6185 ≤ 8547331616929^6185*250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132002081 250000000 8547331616929 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528384351/10000000000 : ℝ)^8233 ≤ (22716237990757/50000000000000 : ℝ)^6185 := by
    have hnat : (5528384351 : ℕ)^8233*50000000000000^6185 ≤ 22716237990757^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528384351 10000000000 22716237990757 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011908913/10000000000 : ℝ)^8233 ≤ (2957716480801/25000000000000 : ℝ)^6185 := by
    have hnat : (2011908913 : ℕ)^8233*25000000000000^6185 ≤ 2957716480801^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011908913 10000000000 2957716480801 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132002081/250000000 : ℝ), (5528384351/10000000000 : ℝ), (-2011908913/10000000000 : ℝ)] ![(8547331616929/20000000000000 : ℝ), (22716237990757/50000000000000 : ℝ), (2957716480801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132002081/250000000 : ℝ)|^8233 ≤ (8547331616929/20000000000000 : ℝ)^6185
        have hw : |(132002081/250000000 : ℝ)|=(132002081/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528384351/10000000000 : ℝ)|^8233 ≤ (22716237990757/50000000000000 : ℝ)^6185
        have hw : |(5528384351/10000000000 : ℝ)|=(5528384351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011908913/10000000000 : ℝ)|^8233 ≤ (2957716480801/25000000000000 : ℝ)^6185
        have hw : |(-2011908913/10000000000 : ℝ)|=(2011908913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s2_7 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366330789/10000000000 : ℝ)*x 0 + (2378763301/5000000000 : ℝ)*x 1 + (501034279/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366330789/10000000000 : ℝ)^8233 ≤ (829642012547/2500000000000 : ℝ)^6185 := by
    have hnat : (4366330789 : ℕ)^8233*2500000000000^6185 ≤ 829642012547^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366330789 10000000000 829642012547 2500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2378763301/5000000000 : ℝ)^8233 ≤ (37200990842951/100000000000000 : ℝ)^6185 := by
    have hnat : (2378763301 : ℕ)^8233*100000000000000^6185 ≤ 37200990842951^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2378763301 5000000000 37200990842951 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501034279/1250000000 : ℝ)^8233 ≤ (5922665727557/20000000000000 : ℝ)^6185 := by
    have hnat : (501034279 : ℕ)^8233*20000000000000^6185 ≤ 5922665727557^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501034279 1250000000 5922665727557 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366330789/10000000000 : ℝ), (2378763301/5000000000 : ℝ), (501034279/1250000000 : ℝ)] ![(829642012547/2500000000000 : ℝ), (37200990842951/100000000000000 : ℝ), (5922665727557/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366330789/10000000000 : ℝ)|^8233 ≤ (829642012547/2500000000000 : ℝ)^6185
        have hw : |(4366330789/10000000000 : ℝ)|=(4366330789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2378763301/5000000000 : ℝ)|^8233 ≤ (37200990842951/100000000000000 : ℝ)^6185
        have hw : |(2378763301/5000000000 : ℝ)|=(2378763301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501034279/1250000000 : ℝ)|^8233 ≤ (5922665727557/20000000000000 : ℝ)^6185
        have hw : |(501034279/1250000000 : ℝ)|=(501034279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10457/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2531/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1073/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16827/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10457/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2531/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10457/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2531/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10457/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2531/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10457/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2531/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10457/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2531/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10457/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2531/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2531/50000 : ℝ) ^ (1029/256 : ℝ) ≤ (123883181678261/20000000000000000000 : ℝ) := by
    have hpowers : (2531/50000 : ℝ)^1029 ≤ (123883181678261/20000000000000000000 : ℝ)^256 := by
      have hnat : (2531 : ℕ)^1029*20000000000000000000^256 ≤ 123883181678261^256*50000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2531 50000 123883181678261 20000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2531/50000 : ℝ)) (X := (123883181678261/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (10457/50000 : ℝ) ^ (1029/256 : ℝ) ≤ (46389074768098869/25000000000000000000 : ℝ) := by
    have hpowers : (10457/50000 : ℝ)^1029 ≤ (46389074768098869/25000000000000000000 : ℝ)^256 := by
      have hnat : (10457 : ℕ)^1029*25000000000000000000^256 ≤ 46389074768098869^256*50000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10457 50000 46389074768098869 25000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10457/50000 : ℝ)) (X := (46389074768098869/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000123883181678261/10000000000000000000 : ℝ) ≤ (2500007705040559/2500000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (10000123883181678261/10000000000000000000 : ℝ)^256 ≤ (2500007705040559/2500000000000000 : ℝ)^1029 := by
      have hnat : (10000123883181678261 : ℕ)^256*2500000000000000^1029 ≤ 2500007705040559^1029*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000123883181678261 10000000000000000000 2500007705040559 2500000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500007705040559/2500000000000000 : ℝ)) (X := (10000123883181678261/10000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100186175714980786781/100000000000000000000 : ℝ) ≤ (5002314270669271/5000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (100186175714980786781/100000000000000000000 : ℝ)^256 ≤ (5002314270669271/5000000000000000 : ℝ)^1029 := by
      have hnat : (100186175714980786781 : ℕ)^256*5000000000000000^1029 ≤ 5002314270669271^1029*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100186175714980786781 100000000000000000000 5002314270669271 5000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002314270669271/5000000000000000 : ℝ)) (X := (100186175714980786781/100000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12546389074768098869/12500000000000000000 : ℝ) ≤ (312788320703589/312500000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (12546389074768098869/12500000000000000000 : ℝ)^256 ≤ (312788320703589/312500000000000 : ℝ)^1029 := by
      have hnat : (12546389074768098869 : ℕ)^256*312500000000000^1029 ≤ 312788320703589^1029*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12546389074768098869 12500000000000000000 312788320703589 312500000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312788320703589/312500000000000 : ℝ)) (X := (12546389074768098869/12500000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(123883181678261/20000000000000000000 : ℝ) ≤ ((19809242654002855391/19815000000000000000 : ℝ)+2*(2298860588153/792600000000000 : ℝ)*(2531/50000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (19809242654002855391/19815000000000000000 : ℝ)+2*(2298860588153/792600000000000 : ℝ)*(2531/50000 : ℝ)=(2500007705040559/2500000000000000 : ℝ) by norm_num, show 1+2*(123883181678261/20000000000000000000 : ℝ)=(10000123883181678261/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46389074768098869/25000000000000000000 : ℝ)+(123883181678261/20000000000000000000 : ℝ) ≤ ((19809242654002855391/19815000000000000000 : ℝ)+(2298860588153/792600000000000 : ℝ)*((10457/50000 : ℝ)+(2531/50000 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (19809242654002855391/19815000000000000000 : ℝ)+(2298860588153/792600000000000 : ℝ)*((10457/50000 : ℝ)+(2531/50000 : ℝ))=(5002314270669271/5000000000000000 : ℝ) by norm_num, show 1+(46389074768098869/25000000000000000000 : ℝ)+(123883181678261/20000000000000000000 : ℝ)=(100186175714980786781/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46389074768098869/25000000000000000000 : ℝ) ≤ ((19809242654002855391/19815000000000000000 : ℝ)+2*(2298860588153/792600000000000 : ℝ)*(10457/50000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (19809242654002855391/19815000000000000000 : ℝ)+2*(2298860588153/792600000000000 : ℝ)*(10457/50000 : ℝ)=(312788320703589/312500000000000 : ℝ) by norm_num, show 1+2*(46389074768098869/25000000000000000000 : ℝ)=(12546389074768098869/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19809242654002855391/19815000000000000000 : ℝ)*(X 1 0+X 2 0)+(2298860588153/792600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2531/50000 : ℝ)) (hi := (10457/50000 : ℝ)) (c := (19809242654002855391/19815000000000000000 : ℝ)) (alpha := (2298860588153/792600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19809242654002855391/19815000000000000000 : ℝ)*(X 0 1+X 2 1)+(2298860588153/792600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2531/50000 : ℝ)) (hi := (10457/50000 : ℝ)) (c := (19809242654002855391/19815000000000000000 : ℝ)) (alpha := (2298860588153/792600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19809242654002855391/19815000000000000000 : ℝ)*(X 0 2+X 1 2)+(2298860588153/792600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2531/50000 : ℝ)) (hi := (10457/50000 : ℝ)) (c := (19809242654002855391/19815000000000000000 : ℝ)) (alpha := (2298860588153/792600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-548853957/2500000000 : ℝ)*X 0 0+(5531304417/10000000000 : ℝ)*X 0 1+(40165737/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2689181967/5000000000 : ℝ)*X 1 0+(-23990791/100000000 : ℝ)*X 1 1+(1285303537/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2689182027/5000000000 : ℝ)*X 2 0+(102824281/200000000 : ℝ)*X 2 1+(-239907907/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366067011/10000000000 : ℝ)*X 0 0+(4002580809/10000000000 : ℝ)*X 0 1+(1190789993/2500000000 : ℝ)*X 0 2+(4366067011/10000000000 : ℝ)*X 1 0+(4002580809/10000000000 : ℝ)*X 1 1+(1190789993/2500000000 : ℝ)*X 1 2+(4366067011/10000000000 : ℝ)*X 2 0+(4002580809/10000000000 : ℝ)*X 2 1+(1190789993/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2195551121/10000000000 : ℝ)*X 0 0+(5144103277/10000000000 : ℝ)*X 0 1+(5528384447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280083029/10000000000 : ℝ)*X 1 0+(-201190899/1000000000 : ℝ)*X 1 1+(691048063/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132002081/250000000 : ℝ)*X 2 0+(5528384351/10000000000 : ℝ)*X 2 1+(-2011908913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366330789/10000000000 : ℝ)*X 0 0+(2378763301/5000000000 : ℝ)*X 0 1+(501034279/1250000000 : ℝ)*X 0 2+(4366330789/10000000000 : ℝ)*X 1 0+(2378763301/5000000000 : ℝ)*X 1 1+(501034279/1250000000 : ℝ)*X 1 2+(4366330789/10000000000 : ℝ)*X 2 0+(2378763301/5000000000 : ℝ)*X 2 1+(501034279/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (415910219338180357247462541/165125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2953189/100000000000000 : ℝ)*(base1) + (479907141/100000000000000 : ℝ)*(base19) + (53710337/10000000000000 : ℝ)*(base23) + (3026097/20000000000000 : ℝ)*(upper3) + (2848673/6250000000000 : ℝ)*(upper5) + (1939155863821151/100000000000000 : ℝ)*(major0) + (1939155863821151/100000000000000 : ℝ)*(major1) + (1939155863821151/100000000000000 : ℝ)*(major2) + (640878505811627/25000000000000 : ℝ)*(sp0) + (256351788818241/10000000000000 : ℝ)*(sp1) + (128175891549309/5000000000000 : ℝ)*(sp2) + (1314790440229379/100000000000000 : ℝ)*(sp3) + (4347796231/100000000000000 : ℝ)*(sp4) + (566482303/20000000000000 : ℝ)*(sp7) + (328698318898521/25000000000000 : ℝ)*(f.failure) + (51270367361791/2000000000000 : ℝ)*(f.sum) + (30546933497833/39630000000000000000000000000 : ℝ)*base65 + (4040274826326750041/1981500000000000000000000000000000 : ℝ)*base67 + (14772427683216749959/1981500000000000000000000000000000 : ℝ)*base70 + (5294904526043249959/1981500000000000000000000000000000 : ℝ)*base72 + (188219615881273/39630000000000000000000000000 : ℝ)*base73 + (18576072946619249959/1981500000000000000000000000000000 : ℝ)*base76 + (3562226989613249959/1981500000000000000000000000000000 : ℝ)*base78 + (3838672825398749959/1981500000000000000000000000000000 : ℝ)*base80 + (93160027176737/39630000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2997271/250000000000000000000 : ℝ)*base89 + (2997271/250000000000000000000 : ℝ)*base91 + (2997271/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2990125363683248757117408633/330250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (350383989/20000000000000 : ℝ)*(base19) + (495181459/25000000000000 : ℝ)*(base23) + (221691487/100000000000000 : ℝ)*(upper3) + (48227443/100000000000000 : ℝ)*(lower4) + (8202981/4000000000000 : ℝ)*(upper5) + (1968462632309063/100000000000000 : ℝ)*(major0) + (1968462632309063/100000000000000 : ℝ)*(major1) + (1968462632309063/100000000000000 : ℝ)*(major2) + (14890929273/100000000000000 : ℝ)*(sp1) + (8344746847/50000000000000 : ℝ)*(sp2) + (1301130504513087/50000000000000 : ℝ)*(sp4) + (650561091544239/25000000000000 : ℝ)*(sp5) + (2602242338806643/100000000000000 : ℝ)*(sp6) + (1334663953787723/100000000000000 : ℝ)*(sp7) + (1334663953787723/100000000000000 : ℝ)*(f.failure) + (1301130504513087/50000000000000 : ℝ)*(f.sum) + (75850749696049/39630000000000000000000000000 : ℝ)*base65 + (7484468476412316367/1981500000000000000000000000000000 : ℝ)*base68 + (12921882950117316367/1981500000000000000000000000000000 : ℝ)*base70 + (2660989635795816367/1981500000000000000000000000000000 : ℝ)*base72 + (4705789862141/39630000000000000000000000000 : ℝ)*base74 + (101039873792316367/1981500000000000000000000000000000 : ℝ)*base76 + (1421456987369183633/1981500000000000000000000000000000 : ℝ)*base77 + (4596593969195183633/1981500000000000000000000000000000 : ℝ)*base79 + (210678022313471/39630000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3383973/1000000000000000000000 : ℝ)*base89 + (3383973/1000000000000000000000 : ℝ)*base91 + (3383973/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1040_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10457/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2531/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1073/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16827/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1040_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1040_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1073/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16827/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1040_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1040_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1040_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1073/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16827/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1040_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
