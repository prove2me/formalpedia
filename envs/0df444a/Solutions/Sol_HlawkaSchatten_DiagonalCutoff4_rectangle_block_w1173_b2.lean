-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1173_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:43.397242+00:00
-- url     : https://prove2.me/submissions/b6e530ba-07a4-4199-8b28-6b32a8a4a5c9

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
theorem support_rectangle_w1173_s6_0 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076060673/5000000000 : ℝ)*x 0 + (2696382027/5000000000 : ℝ)*x 1 + (1316487977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076060673/5000000000 : ℝ)^4183 ≤ (13080169451619/100000000000000 : ℝ)^3159 := by
    have hnat : (1076060673 : ℕ)^4183*100000000000000^3159 ≤ 13080169451619^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076060673 5000000000 13080169451619 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696382027/5000000000 : ℝ)^4183 ≤ (44144563732593/100000000000000 : ℝ)^3159 := by
    have hnat : (2696382027 : ℕ)^4183*100000000000000^3159 ≤ 44144563732593^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696382027 5000000000 44144563732593 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316487977/2500000000 : ℝ)^4183 ≤ (167090885947/390625000000 : ℝ)^3159 := by
    have hnat : (1316487977 : ℕ)^4183*390625000000^3159 ≤ 167090885947^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316487977 2500000000 167090885947 390625000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076060673/5000000000 : ℝ), (2696382027/5000000000 : ℝ), (1316487977/2500000000 : ℝ)] ![(13080169451619/100000000000000 : ℝ), (44144563732593/100000000000000 : ℝ), (167090885947/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076060673/5000000000 : ℝ)|^4183 ≤ (13080169451619/100000000000000 : ℝ)^3159
        have hw : |(-1076060673/5000000000 : ℝ)|=(1076060673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696382027/5000000000 : ℝ)|^4183 ≤ (44144563732593/100000000000000 : ℝ)^3159
        have hw : |(2696382027/5000000000 : ℝ)|=(2696382027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316487977/2500000000 : ℝ)|^4183 ≤ (167090885947/390625000000 : ℝ)^3159
        have hw : |(1316487977/2500000000 : ℝ)|=(1316487977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s6_1 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344710377/10000000000 : ℝ)*x 0 + (-138527451/625000000 : ℝ)*x 1 + (210638079/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344710377/10000000000 : ℝ)^4183 ≤ (5453055738943/12500000000000 : ℝ)^3159 := by
    have hnat : (5344710377 : ℕ)^4183*12500000000000^3159 ≤ 5453055738943^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344710377 10000000000 5453055738943 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138527451/625000000 : ℝ)^4183 ≤ (13600286558873/100000000000000 : ℝ)^3159 := by
    have hnat : (138527451 : ℕ)^4183*100000000000000^3159 ≤ 13600286558873^3159*625000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138527451 625000000 13600286558873 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210638079/400000000 : ℝ)^4183 ≤ (42775267523089/100000000000000 : ℝ)^3159 := by
    have hnat : (210638079 : ℕ)^4183*100000000000000^3159 ≤ 42775267523089^3159*400000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210638079 400000000 42775267523089 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344710377/10000000000 : ℝ), (-138527451/625000000 : ℝ), (210638079/400000000 : ℝ)] ![(5453055738943/12500000000000 : ℝ), (13600286558873/100000000000000 : ℝ), (42775267523089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344710377/10000000000 : ℝ)|^4183 ≤ (5453055738943/12500000000000 : ℝ)^3159
        have hw : |(5344710377/10000000000 : ℝ)|=(5344710377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138527451/625000000 : ℝ)|^4183 ≤ (13600286558873/100000000000000 : ℝ)^3159
        have hw : |(-138527451/625000000 : ℝ)|=(138527451/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210638079/400000000 : ℝ)|^4183 ≤ (42775267523089/100000000000000 : ℝ)^3159
        have hw : |(210638079/400000000 : ℝ)|=(210638079/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s6_2 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344710551/10000000000 : ℝ)*x 0 + (526595171/1000000000 : ℝ)*x 1 + (-443287867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344710551/10000000000 : ℝ)^4183 ≤ (4362444779213/10000000000000 : ℝ)^3159 := by
    have hnat : (5344710551 : ℕ)^4183*10000000000000^3159 ≤ 4362444779213^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344710551 10000000000 4362444779213 10000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526595171/1000000000 : ℝ)^4183 ≤ (5346908084091/12500000000000 : ℝ)^3159 := by
    have hnat : (526595171 : ℕ)^4183*12500000000000^3159 ≤ 5346908084091^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526595171 1000000000 5346908084091 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443287867/2000000000 : ℝ)^4183 ≤ (3400071881441/25000000000000 : ℝ)^3159 := by
    have hnat : (443287867 : ℕ)^4183*25000000000000^3159 ≤ 3400071881441^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443287867 2000000000 3400071881441 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344710551/10000000000 : ℝ), (526595171/1000000000 : ℝ), (-443287867/2000000000 : ℝ)] ![(4362444779213/10000000000000 : ℝ), (5346908084091/12500000000000 : ℝ), (3400071881441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344710551/10000000000 : ℝ)|^4183 ≤ (4362444779213/10000000000000 : ℝ)^3159
        have hw : |(5344710551/10000000000 : ℝ)|=(5344710551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526595171/1000000000 : ℝ)|^4183 ≤ (5346908084091/12500000000000 : ℝ)^3159
        have hw : |(526595171/1000000000 : ℝ)|=(526595171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-443287867/2000000000 : ℝ)|^4183 ≤ (3400071881441/25000000000000 : ℝ)^3159
        have hw : |(-443287867/2000000000 : ℝ)|=(443287867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s6_3 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360309969/10000000000 : ℝ)*x 0 + (2117610791/5000000000 : ℝ)*x 1 + (4489046837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360309969/10000000000 : ℝ)^4183 ≤ (33316990044311/100000000000000 : ℝ)^3159 := by
    have hnat : (4360309969 : ℕ)^4183*100000000000000^3159 ≤ 33316990044311^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360309969 10000000000 33316990044311 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117610791/5000000000 : ℝ)^4183 ≤ (16028646182383/50000000000000 : ℝ)^3159 := by
    have hnat : (2117610791 : ℕ)^4183*50000000000000^3159 ≤ 16028646182383^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117610791 5000000000 16028646182383 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489046837/10000000000 : ℝ)^4183 ≤ (1385028703231/4000000000000 : ℝ)^3159 := by
    have hnat : (4489046837 : ℕ)^4183*4000000000000^3159 ≤ 1385028703231^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489046837 10000000000 1385028703231 4000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360309969/10000000000 : ℝ), (2117610791/5000000000 : ℝ), (4489046837/10000000000 : ℝ)] ![(33316990044311/100000000000000 : ℝ), (16028646182383/50000000000000 : ℝ), (1385028703231/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360309969/10000000000 : ℝ)|^4183 ≤ (33316990044311/100000000000000 : ℝ)^3159
        have hw : |(4360309969/10000000000 : ℝ)|=(4360309969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117610791/5000000000 : ℝ)|^4183 ≤ (16028646182383/50000000000000 : ℝ)^3159
        have hw : |(2117610791/5000000000 : ℝ)|=(2117610791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489046837/10000000000 : ℝ)|^4183 ≤ (1385028703231/4000000000000 : ℝ)^3159
        have hw : |(4489046837/10000000000 : ℝ)|=(4489046837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s6_4 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67253949/312500000 : ℝ)*x 0 + (5266272107/10000000000 : ℝ)*x 1 + (269622129/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67253949/312500000 : ℝ)^4183 ≤ (32700524671/250000000000 : ℝ)^3159 := by
    have hnat : (67253949 : ℕ)^4183*250000000000^3159 ≤ 32700524671^3159*312500000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67253949 312500000 32700524671 250000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266272107/10000000000 : ℝ)^4183 ≤ (42778710922857/100000000000000 : ℝ)^3159 := by
    have hnat : (5266272107 : ℕ)^4183*100000000000000^3159 ≤ 42778710922857^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266272107 10000000000 42778710922857 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269622129/500000000 : ℝ)^4183 ≤ (44141079190569/100000000000000 : ℝ)^3159 := by
    have hnat : (269622129 : ℕ)^4183*100000000000000^3159 ≤ 44141079190569^3159*500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269622129 500000000 44141079190569 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67253949/312500000 : ℝ), (5266272107/10000000000 : ℝ), (269622129/500000000 : ℝ)] ![(32700524671/250000000000 : ℝ), (42778710922857/100000000000000 : ℝ), (44141079190569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67253949/312500000 : ℝ)|^4183 ≤ (32700524671/250000000000 : ℝ)^3159
        have hw : |(-67253949/312500000 : ℝ)|=(67253949/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266272107/10000000000 : ℝ)|^4183 ≤ (42778710922857/100000000000000 : ℝ)^3159
        have hw : |(5266272107/10000000000 : ℝ)|=(5266272107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269622129/500000000 : ℝ)|^4183 ≤ (44141079190569/100000000000000 : ℝ)^3159
        have hw : |(269622129/500000000 : ℝ)|=(269622129/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s6_5 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312509203/10000000000 : ℝ)*x 0 + (-104497423/500000000 : ℝ)*x 1 + (674055321/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312509203/10000000000 : ℝ)^4183 ≤ (43276757014151/100000000000000 : ℝ)^3159 := by
    have hnat : (5312509203 : ℕ)^4183*100000000000000^3159 ≤ 43276757014151^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312509203 10000000000 43276757014151 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104497423/500000000 : ℝ)^4183 ≤ (6291081958113/50000000000000 : ℝ)^3159 := by
    have hnat : (104497423 : ℕ)^4183*50000000000000^3159 ≤ 6291081958113^3159*500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104497423 500000000 6291081958113 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674055321/1250000000 : ℝ)^4183 ≤ (44141079060499/100000000000000 : ℝ)^3159 := by
    have hnat : (674055321 : ℕ)^4183*100000000000000^3159 ≤ 44141079060499^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674055321 1250000000 44141079060499 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312509203/10000000000 : ℝ), (-104497423/500000000 : ℝ), (674055321/1250000000 : ℝ)] ![(43276757014151/100000000000000 : ℝ), (6291081958113/50000000000000 : ℝ), (44141079060499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312509203/10000000000 : ℝ)|^4183 ≤ (43276757014151/100000000000000 : ℝ)^3159
        have hw : |(5312509203/10000000000 : ℝ)|=(5312509203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104497423/500000000 : ℝ)|^4183 ≤ (6291081958113/50000000000000 : ℝ)^3159
        have hw : |(-104497423/500000000 : ℝ)|=(104497423/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674055321/1250000000 : ℝ)|^4183 ≤ (44141079060499/100000000000000 : ℝ)^3159
        have hw : |(674055321/1250000000 : ℝ)|=(674055321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s6_6 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656254597/5000000000 : ℝ)*x 0 + (1078488511/2000000000 : ℝ)*x 1 + (-2089948489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656254597/5000000000 : ℝ)^4183 ≤ (43276756917069/100000000000000 : ℝ)^3159 := by
    have hnat : (2656254597 : ℕ)^4183*100000000000000^3159 ≤ 43276756917069^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656254597 5000000000 43276756917069 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078488511/2000000000 : ℝ)^4183 ≤ (4414107891959/10000000000000 : ℝ)^3159 := by
    have hnat : (1078488511 : ℕ)^4183*10000000000000^3159 ≤ 4414107891959^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078488511 2000000000 4414107891959 10000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089948489/10000000000 : ℝ)^4183 ≤ (12582164147409/100000000000000 : ℝ)^3159 := by
    have hnat : (2089948489 : ℕ)^4183*100000000000000^3159 ≤ 12582164147409^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089948489 10000000000 12582164147409 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656254597/5000000000 : ℝ), (1078488511/2000000000 : ℝ), (-2089948489/10000000000 : ℝ)] ![(43276756917069/100000000000000 : ℝ), (4414107891959/10000000000000 : ℝ), (12582164147409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656254597/5000000000 : ℝ)|^4183 ≤ (43276756917069/100000000000000 : ℝ)^3159
        have hw : |(2656254597/5000000000 : ℝ)|=(2656254597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078488511/2000000000 : ℝ)|^4183 ≤ (4414107891959/10000000000000 : ℝ)^3159
        have hw : |(1078488511/2000000000 : ℝ)|=(1078488511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089948489/10000000000 : ℝ)|^4183 ≤ (12582164147409/100000000000000 : ℝ)^3159
        have hw : |(-2089948489/10000000000 : ℝ)|=(2089948489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s6_7 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545039929/1250000000 : ℝ)*x 0 + (4488405531/10000000000 : ℝ)*x 1 + (2117932759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545039929/1250000000 : ℝ)^4183 ≤ (16658542894603/50000000000000 : ℝ)^3159 := by
    have hnat : (545039929 : ℕ)^4183*50000000000000^3159 ≤ 16658542894603^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545039929 1250000000 16658542894603 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488405531/10000000000 : ℝ)^4183 ≤ (8654791907141/25000000000000 : ℝ)^3159 := by
    have hnat : (4488405531 : ℕ)^4183*25000000000000^3159 ≤ 8654791907141^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488405531 10000000000 8654791907141 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117932759/5000000000 : ℝ)^4183 ≤ (32063746563693/100000000000000 : ℝ)^3159 := by
    have hnat : (2117932759 : ℕ)^4183*100000000000000^3159 ≤ 32063746563693^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117932759 5000000000 32063746563693 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545039929/1250000000 : ℝ), (4488405531/10000000000 : ℝ), (2117932759/5000000000 : ℝ)] ![(16658542894603/50000000000000 : ℝ), (8654791907141/25000000000000 : ℝ), (32063746563693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545039929/1250000000 : ℝ)|^4183 ≤ (16658542894603/50000000000000 : ℝ)^3159
        have hw : |(545039929/1250000000 : ℝ)|=(545039929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488405531/10000000000 : ℝ)|^4183 ≤ (8654791907141/25000000000000 : ℝ)^3159
        have hw : |(4488405531/10000000000 : ℝ)|=(4488405531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117932759/5000000000 : ℝ)|^4183 ≤ (32063746563693/100000000000000 : ℝ)^3159
        have hw : |(2117932759/5000000000 : ℝ)|=(2117932759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1173_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    (11387/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14073/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (71/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (71/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (71/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (71/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (71/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (71/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (71/625 : ℝ) ^ (8365/2048 : ℝ) ≤ (13858576516026981/100000000000000000000 : ℝ) := by
    have hpowers : (71/625 : ℝ)^8365 ≤ (13858576516026981/100000000000000000000 : ℝ)^2048 := by
      have hnat : (71 : ℕ)^8365*100000000000000000000^2048 ≤ 13858576516026981^2048*625^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71 625 13858576516026981 100000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71/625 : ℝ)) (X := (13858576516026981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7051/50000 : ℝ) ^ (8365/2048 : ℝ) ≤ (3351662831307033/10000000000000000000 : ℝ) := by
    have hpowers : (7051/50000 : ℝ)^8365 ≤ (3351662831307033/10000000000000000000 : ℝ)^2048 := by
      have hnat : (7051 : ℕ)^8365*10000000000000000000^2048 ≤ 3351662831307033^2048*50000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7051 50000 3351662831307033 10000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7051/50000 : ℝ)) (X := (3351662831307033/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013858576516026981/50000000000000000000 : ℝ) ≤ (10000678527072459/10000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (50013858576516026981/50000000000000000000 : ℝ)^2048 ≤ (10000678527072459/10000000000000000 : ℝ)^8365 := by
      have hnat : (50013858576516026981 : ℕ)^2048*10000000000000000^8365 ≤ 10000678527072459^8365*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013858576516026981 50000000000000000000 10000678527072459 10000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000678527072459/10000000000000000 : ℝ)) (X := (50013858576516026981/50000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047375204829097311/100000000000000000000 : ℝ) ≤ (2500289919511061/2500000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (100047375204829097311/100000000000000000000 : ℝ)^2048 ≤ (2500289919511061/2500000000000000 : ℝ)^8365 := by
      have hnat : (100047375204829097311 : ℕ)^2048*2500000000000000^8365 ≤ 2500289919511061^8365*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047375204829097311 100000000000000000000 2500289919511061 2500000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500289919511061/2500000000000000 : ℝ)) (X := (100047375204829097311/100000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003351662831307033/5000000000000000000 : ℝ) ≤ (10001640829016029/10000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (5003351662831307033/5000000000000000000 : ℝ)^2048 ≤ (10001640829016029/10000000000000000 : ℝ)^8365 := by
      have hnat : (5003351662831307033 : ℕ)^2048*10000000000000000^8365 ≤ 10001640829016029^8365*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003351662831307033 5000000000000000000 10001640829016029 10000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001640829016029/10000000000000000 : ℝ)) (X := (5003351662831307033/5000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13858576516026981/100000000000000000000 : ℝ) ≤ ((13705464385576863689/13710000000000000000 : ℝ)+2*(96230194357/54840000000000 : ℝ)*(71/625 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (13705464385576863689/13710000000000000000 : ℝ)+2*(96230194357/54840000000000 : ℝ)*(71/625 : ℝ)=(10000678527072459/10000000000000000 : ℝ) by norm_num, show 1+2*(13858576516026981/100000000000000000000 : ℝ)=(50013858576516026981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3351662831307033/10000000000000000000 : ℝ)+(13858576516026981/100000000000000000000 : ℝ) ≤ ((13705464385576863689/13710000000000000000 : ℝ)+(96230194357/54840000000000 : ℝ)*((7051/50000 : ℝ)+(71/625 : ℝ)))^(8365/2048 : ℝ) := by
    rw [show (13705464385576863689/13710000000000000000 : ℝ)+(96230194357/54840000000000 : ℝ)*((7051/50000 : ℝ)+(71/625 : ℝ))=(2500289919511061/2500000000000000 : ℝ) by norm_num, show 1+(3351662831307033/10000000000000000000 : ℝ)+(13858576516026981/100000000000000000000 : ℝ)=(100047375204829097311/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3351662831307033/10000000000000000000 : ℝ) ≤ ((13705464385576863689/13710000000000000000 : ℝ)+2*(96230194357/54840000000000 : ℝ)*(7051/50000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (13705464385576863689/13710000000000000000 : ℝ)+2*(96230194357/54840000000000 : ℝ)*(7051/50000 : ℝ)=(10001640829016029/10000000000000000 : ℝ) by norm_num, show 1+2*(3351662831307033/10000000000000000000 : ℝ)=(5003351662831307033/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13705464385576863689/13710000000000000000 : ℝ)*(X 1 0+X 2 0)+(96230194357/54840000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (71/625 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13705464385576863689/13710000000000000000 : ℝ)) (alpha := (96230194357/54840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13705464385576863689/13710000000000000000 : ℝ)*(X 0 1+X 2 1)+(96230194357/54840000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (71/625 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13705464385576863689/13710000000000000000 : ℝ)) (alpha := (96230194357/54840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13705464385576863689/13710000000000000000 : ℝ)*(X 0 2+X 1 2)+(96230194357/54840000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (71/625 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13705464385576863689/13710000000000000000 : ℝ)) (alpha := (96230194357/54840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1076060673/5000000000 : ℝ)*X 0 0+(2696382027/5000000000 : ℝ)*X 0 1+(1316487977/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344710377/10000000000 : ℝ)*X 1 0+(-138527451/625000000 : ℝ)*X 1 1+(210638079/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344710551/10000000000 : ℝ)*X 2 0+(526595171/1000000000 : ℝ)*X 2 1+(-443287867/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360309969/10000000000 : ℝ)*X 0 0+(2117610791/5000000000 : ℝ)*X 0 1+(4489046837/10000000000 : ℝ)*X 0 2+(4360309969/10000000000 : ℝ)*X 1 0+(2117610791/5000000000 : ℝ)*X 1 1+(4489046837/10000000000 : ℝ)*X 1 2+(4360309969/10000000000 : ℝ)*X 2 0+(2117610791/5000000000 : ℝ)*X 2 1+(4489046837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-67253949/312500000 : ℝ)*X 0 0+(5266272107/10000000000 : ℝ)*X 0 1+(269622129/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312509203/10000000000 : ℝ)*X 1 0+(-104497423/500000000 : ℝ)*X 1 1+(674055321/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656254597/5000000000 : ℝ)*X 2 0+(1078488511/2000000000 : ℝ)*X 2 1+(-2089948489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545039929/1250000000 : ℝ)*X 0 0+(4488405531/10000000000 : ℝ)*X 0 1+(2117932759/5000000000 : ℝ)*X 0 2+(545039929/1250000000 : ℝ)*X 1 0+(4488405531/10000000000 : ℝ)*X 1 1+(2117932759/5000000000 : ℝ)*X 1 2+(545039929/1250000000 : ℝ)*X 2 0+(4488405531/10000000000 : ℝ)*X 2 1+(2117932759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1713220925533383066051323743/228500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41182509/4000000000000 : ℝ)*(base19) + (1073908879/100000000000000 : ℝ)*(base23) + (24011371/12500000000000 : ℝ)*(lower2) + (301630303/100000000000000 : ℝ)*(upper3) + (78581079/100000000000000 : ℝ)*(lower4) + (5912740583505287/100000000000000 : ℝ)*(major0) + (5912740583505287/100000000000000 : ℝ)*(major1) + (5912740583505287/100000000000000 : ℝ)*(major2) + (7885707702814089/100000000000000 : ℝ)*(sp0) + (7885725536618843/100000000000000 : ℝ)*(sp1) + (492857843267043/6250000000000 : ℝ)*(sp2) + (1969865988915339/50000000000000 : ℝ)*(sp3) + (9431683739/50000000000000 : ℝ)*(sp4) + (22373075503/100000000000000 : ℝ)*(sp7) + (196987717545309/5000000000000 : ℝ)*(f.failure) + (7885726566181567/100000000000000 : ℝ)*(f.sum) + (19072730982901/2742000000000000000000000000 : ℝ)*base66 + (3140162807654524581/457000000000000000000000000000000 : ℝ)*base67 + (1158435609452475419/457000000000000000000000000000000 : ℝ)*base70 + (3939016005081475419/457000000000000000000000000000000 : ℝ)*base72 + (6274994233517/2742000000000000000000000000 : ℝ)*base73 + (6470978291413475419/457000000000000000000000000000000 : ℝ)*base76 + (243951939329524581/457000000000000000000000000000000 : ℝ)*base77 + (4114074004641475419/457000000000000000000000000000000 : ℝ)*base80 + (2839443833939/2742000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (611947/100000000000000000000 : ℝ)*base89 + (611947/100000000000000000000 : ℝ)*base91 + (611947/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (468109795664710069705962889/114250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4414133/625000000000 : ℝ)*(base19) + (706324631/100000000000000 : ℝ)*(base23) + (67823233/100000000000000 : ℝ)*(upper3) + (1416711/10000000000000 : ℝ)*(lower4) + (45636311/50000000000000 : ℝ)*(upper5) + (2971388272682801/50000000000000 : ℝ)*(major0) + (2971388272682801/50000000000000 : ℝ)*(major1) + (2971388272682801/50000000000000 : ℝ)*(major2) + (612890847/3125000000000 : ℝ)*(sp1) + (8719248541/50000000000000 : ℝ)*(sp2) + (1585157031550089/20000000000000 : ℝ)*(sp4) + (3962882419491031/50000000000000 : ℝ)*(sp5) + (1981441753232183/25000000000000 : ℝ)*(sp6) + (1979883898203023/50000000000000 : ℝ)*(sp7) + (1979883898203023/50000000000000 : ℝ)*(f.failure) + (1585157031550089/20000000000000 : ℝ)*(f.sum) + (1344440818319/274200000000000000000000000 : ℝ)*base66 + (933112621631820963/228500000000000000000000000000000 : ℝ)*base67 + (813470974547679037/228500000000000000000000000000000 : ℝ)*base70 + (3274953118180679037/228500000000000000000000000000000 : ℝ)*base72 + (220741270919/54840000000000000000000000 : ℝ)*base73 + (2937515006953679037/228500000000000000000000000000000 : ℝ)*base76 + (2841474770166679037/228500000000000000000000000000000 : ℝ)*base78 + (4352258006979320963/228500000000000000000000000000000 : ℝ)*base79 + (4307952526847/1371000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (8312009/1000000000000000000000 : ℝ)*base89 + (8312009/1000000000000000000000 : ℝ)*base91 + (8312009/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1173_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1173_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1173_s7_0 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152147267/10000000000 : ℝ)*x 0 + (5392484563/10000000000 : ℝ)*x 1 + (1316553541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152147267/10000000000 : ℝ)^4183 ≤ (6540189031369/50000000000000 : ℝ)^3159 := by
    have hnat : (2152147267 : ℕ)^4183*50000000000000^3159 ≤ 6540189031369^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152147267 10000000000 6540189031369 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392484563/10000000000 : ℝ)^4183 ≤ (11035383562907/25000000000000 : ℝ)^3159 := by
    have hnat : (5392484563 : ℕ)^4183*25000000000000^3159 ≤ 11035383562907^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392484563 10000000000 11035383562907 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316553541/2500000000 : ℝ)^4183 ≤ (167101904969/390625000000 : ℝ)^3159 := by
    have hnat : (1316553541 : ℕ)^4183*390625000000^3159 ≤ 167101904969^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316553541 2500000000 167101904969 390625000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152147267/10000000000 : ℝ), (5392484563/10000000000 : ℝ), (1316553541/2500000000 : ℝ)] ![(6540189031369/50000000000000 : ℝ), (11035383562907/25000000000000 : ℝ), (167101904969/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152147267/10000000000 : ℝ)|^4183 ≤ (6540189031369/50000000000000 : ℝ)^3159
        have hw : |(-2152147267/10000000000 : ℝ)|=(2152147267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392484563/10000000000 : ℝ)|^4183 ≤ (11035383562907/25000000000000 : ℝ)^3159
        have hw : |(5392484563/10000000000 : ℝ)|=(5392484563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316553541/2500000000 : ℝ)|^4183 ≤ (167101904969/390625000000 : ℝ)^3159
        have hw : |(1316553541/2500000000 : ℝ)|=(1316553541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s7_1 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344639501/10000000000 : ℝ)*x 0 + (-1108092973/5000000000 : ℝ)*x 1 + (2633107253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344639501/10000000000 : ℝ)^4183 ≤ (43623679887763/100000000000000 : ℝ)^3159 := by
    have hnat : (5344639501 : ℕ)^4183*100000000000000^3159 ≤ 43623679887763^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344639501 10000000000 43623679887763 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108092973/5000000000 : ℝ)^4183 ≤ (13598228744583/100000000000000 : ℝ)^3159 := by
    have hnat : (1108092973 : ℕ)^4183*100000000000000^3159 ≤ 13598228744583^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108092973 5000000000 13598228744583 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633107253/5000000000 : ℝ)^4183 ≤ (2673630709419/6250000000000 : ℝ)^3159 := by
    have hnat : (2633107253 : ℕ)^4183*6250000000000^3159 ≤ 2673630709419^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633107253 5000000000 2673630709419 6250000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344639501/10000000000 : ℝ), (-1108092973/5000000000 : ℝ), (2633107253/5000000000 : ℝ)] ![(43623679887763/100000000000000 : ℝ), (13598228744583/100000000000000 : ℝ), (2673630709419/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344639501/10000000000 : ℝ)|^4183 ≤ (43623679887763/100000000000000 : ℝ)^3159
        have hw : |(5344639501/10000000000 : ℝ)|=(5344639501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1108092973/5000000000 : ℝ)|^4183 ≤ (13598228744583/100000000000000 : ℝ)^3159
        have hw : |(-1108092973/5000000000 : ℝ)|=(1108092973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633107253/5000000000 : ℝ)|^4183 ≤ (2673630709419/6250000000000 : ℝ)^3159
        have hw : |(2633107253/5000000000 : ℝ)|=(2633107253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s7_2 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344640783/10000000000 : ℝ)*x 0 + (5266212583/10000000000 : ℝ)*x 1 + (-2216186787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344640783/10000000000 : ℝ)^4183 ≤ (43623693743517/100000000000000 : ℝ)^3159 := by
    have hnat : (5344640783 : ℕ)^4183*100000000000000^3159 ≤ 43623693743517^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344640783 10000000000 43623693743517 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266212583/10000000000 : ℝ)^4183 ≤ (21389035333213/50000000000000 : ℝ)^3159 := by
    have hnat : (5266212583 : ℕ)^4183*50000000000000^3159 ≤ 21389035333213^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266212583 10000000000 21389035333213 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216186787/10000000000 : ℝ)^4183 ≤ (13598235577567/100000000000000 : ℝ)^3159 := by
    have hnat : (2216186787 : ℕ)^4183*100000000000000^3159 ≤ 13598235577567^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216186787 10000000000 13598235577567 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344640783/10000000000 : ℝ), (5266212583/10000000000 : ℝ), (-2216186787/10000000000 : ℝ)] ![(43623693743517/100000000000000 : ℝ), (21389035333213/50000000000000 : ℝ), (13598235577567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344640783/10000000000 : ℝ)|^4183 ≤ (43623693743517/100000000000000 : ℝ)^3159
        have hw : |(5344640783/10000000000 : ℝ)|=(5344640783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266212583/10000000000 : ℝ)|^4183 ≤ (21389035333213/50000000000000 : ℝ)^3159
        have hw : |(5266212583/10000000000 : ℝ)|=(5266212583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2216186787/10000000000 : ℝ)|^4183 ≤ (13598235577567/100000000000000 : ℝ)^3159
        have hw : |(-2216186787/10000000000 : ℝ)|=(2216186787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s7_3 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2180161501/5000000000 : ℝ)*x 0 + (4235762263/10000000000 : ℝ)*x 1 + (140265729/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180161501/5000000000 : ℝ)^4183 ≤ (8329280477457/25000000000000 : ℝ)^3159 := by
    have hnat : (2180161501 : ℕ)^4183*25000000000000^3159 ≤ 8329280477457^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180161501 5000000000 8329280477457 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235762263/10000000000 : ℝ)^4183 ≤ (16031355806431/50000000000000 : ℝ)^3159 := by
    have hnat : (4235762263 : ℕ)^4183*50000000000000^3159 ≤ 16031355806431^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235762263 10000000000 16031355806431 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140265729/312500000 : ℝ)^4183 ≤ (17310083227281/50000000000000 : ℝ)^3159 := by
    have hnat : (140265729 : ℕ)^4183*50000000000000^3159 ≤ 17310083227281^3159*312500000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140265729 312500000 17310083227281 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180161501/5000000000 : ℝ), (4235762263/10000000000 : ℝ), (140265729/312500000 : ℝ)] ![(8329280477457/25000000000000 : ℝ), (16031355806431/50000000000000 : ℝ), (17310083227281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180161501/5000000000 : ℝ)|^4183 ≤ (8329280477457/25000000000000 : ℝ)^3159
        have hw : |(2180161501/5000000000 : ℝ)|=(2180161501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235762263/10000000000 : ℝ)|^4183 ≤ (16031355806431/50000000000000 : ℝ)^3159
        have hw : |(4235762263/10000000000 : ℝ)|=(4235762263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140265729/312500000 : ℝ)|^4183 ≤ (17310083227281/50000000000000 : ℝ)^3159
        have hw : |(140265729/312500000 : ℝ)|=(140265729/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s7_4 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-538038147/2500000000 : ℝ)*x 0 + (1053306307/2000000000 : ℝ)*x 1 + (5392165663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538038147/2500000000 : ℝ)^4183 ≤ (13080420886023/100000000000000 : ℝ)^3159 := by
    have hnat : (538038147 : ℕ)^4183*100000000000000^3159 ≤ 13080420886023^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538038147 2500000000 13080420886023 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053306307/2000000000 : ℝ)^4183 ≤ (21390750714401/50000000000000 : ℝ)^3159 := by
    have hnat : (1053306307 : ℕ)^4183*50000000000000^3159 ≤ 21390750714401^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053306307 2000000000 21390750714401 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392165663/10000000000 : ℝ)^4183 ≤ (44138077667681/100000000000000 : ℝ)^3159 := by
    have hnat : (5392165663 : ℕ)^4183*100000000000000^3159 ≤ 44138077667681^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392165663 10000000000 44138077667681 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538038147/2500000000 : ℝ), (1053306307/2000000000 : ℝ), (5392165663/10000000000 : ℝ)] ![(13080420886023/100000000000000 : ℝ), (21390750714401/50000000000000 : ℝ), (44138077667681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538038147/2500000000 : ℝ)|^4183 ≤ (13080420886023/100000000000000 : ℝ)^3159
        have hw : |(-538038147/2500000000 : ℝ)|=(538038147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053306307/2000000000 : ℝ)|^4183 ≤ (21390750714401/50000000000000 : ℝ)^3159
        have hw : |(1053306307/2000000000 : ℝ)|=(1053306307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392165663/10000000000 : ℝ)|^4183 ≤ (44138077667681/100000000000000 : ℝ)^3159
        have hw : |(5392165663/10000000000 : ℝ)|=(5392165663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s7_5 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312575583/10000000000 : ℝ)*x 0 + (-2090235133/10000000000 : ℝ)*x 1 + (5392165663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312575583/10000000000 : ℝ)^4183 ≤ (676210516319/1562500000000 : ℝ)^3159 := by
    have hnat : (5312575583 : ℕ)^4183*1562500000000^3159 ≤ 676210516319^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312575583 10000000000 676210516319 1562500000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090235133/10000000000 : ℝ)^4183 ≤ (3146112318827/25000000000000 : ℝ)^3159 := by
    have hnat : (2090235133 : ℕ)^4183*25000000000000^3159 ≤ 3146112318827^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090235133 10000000000 3146112318827 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392165663/10000000000 : ℝ)^4183 ≤ (44138077667681/100000000000000 : ℝ)^3159 := by
    have hnat : (5392165663 : ℕ)^4183*100000000000000^3159 ≤ 44138077667681^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392165663 10000000000 44138077667681 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312575583/10000000000 : ℝ), (-2090235133/10000000000 : ℝ), (5392165663/10000000000 : ℝ)] ![(676210516319/1562500000000 : ℝ), (3146112318827/25000000000000 : ℝ), (44138077667681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312575583/10000000000 : ℝ)|^4183 ≤ (676210516319/1562500000000 : ℝ)^3159
        have hw : |(5312575583/10000000000 : ℝ)|=(5312575583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090235133/10000000000 : ℝ)|^4183 ≤ (3146112318827/25000000000000 : ℝ)^3159
        have hw : |(-2090235133/10000000000 : ℝ)|=(2090235133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392165663/10000000000 : ℝ)|^4183 ≤ (44138077667681/100000000000000 : ℝ)^3159
        have hw : |(5392165663/10000000000 : ℝ)|=(5392165663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s7_6 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312575593/10000000000 : ℝ)*x 0 + (1078433131/2000000000 : ℝ)*x 1 + (-209023513/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312575593/10000000000 : ℝ)^4183 ≤ (8655494630457/20000000000000 : ℝ)^3159 := by
    have hnat : (5312575593 : ℕ)^4183*20000000000000^3159 ≤ 8655494630457^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312575593 10000000000 8655494630457 20000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078433131/2000000000 : ℝ)^4183 ≤ (44138077580969/100000000000000 : ℝ)^3159 := by
    have hnat : (1078433131 : ℕ)^4183*100000000000000^3159 ≤ 44138077580969^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078433131 2000000000 44138077580969 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209023513/1000000000 : ℝ)^4183 ≤ (12584449251391/100000000000000 : ℝ)^3159 := by
    have hnat : (209023513 : ℕ)^4183*100000000000000^3159 ≤ 12584449251391^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209023513 1000000000 12584449251391 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312575593/10000000000 : ℝ), (1078433131/2000000000 : ℝ), (-209023513/1000000000 : ℝ)] ![(8655494630457/20000000000000 : ℝ), (44138077580969/100000000000000 : ℝ), (12584449251391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312575593/10000000000 : ℝ)|^4183 ≤ (8655494630457/20000000000000 : ℝ)^3159
        have hw : |(5312575593/10000000000 : ℝ)|=(5312575593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078433131/2000000000 : ℝ)|^4183 ≤ (44138077580969/100000000000000 : ℝ)^3159
        have hw : |(1078433131/2000000000 : ℝ)|=(1078433131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209023513/1000000000 : ℝ)|^4183 ≤ (12584449251391/100000000000000 : ℝ)^3159
        have hw : |(-209023513/1000000000 : ℝ)|=(209023513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s7_7 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (436033313/1000000000 : ℝ)*x 0 + (44878669/100000000 : ℝ)*x 1 + (2118200253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436033313/1000000000 : ℝ)^4183 ≤ (8329306095793/25000000000000 : ℝ)^3159 := by
    have hnat : (436033313 : ℕ)^4183*25000000000000^3159 ≤ 8329306095793^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436033313 1000000000 8329306095793 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44878669/100000000 : ℝ)^4183 ≤ (34613666577593/100000000000000 : ℝ)^3159 := by
    have hnat : (44878669 : ℕ)^4183*100000000000000^3159 ≤ 34613666577593^3159*100000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44878669 100000000 34613666577593 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118200253/5000000000 : ℝ)^4183 ≤ (32069109013903/100000000000000 : ℝ)^3159 := by
    have hnat : (2118200253 : ℕ)^4183*100000000000000^3159 ≤ 32069109013903^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118200253 5000000000 32069109013903 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436033313/1000000000 : ℝ), (44878669/100000000 : ℝ), (2118200253/5000000000 : ℝ)] ![(8329306095793/25000000000000 : ℝ), (34613666577593/100000000000000 : ℝ), (32069109013903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436033313/1000000000 : ℝ)|^4183 ≤ (8329306095793/25000000000000 : ℝ)^3159
        have hw : |(436033313/1000000000 : ℝ)|=(436033313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44878669/100000000 : ℝ)|^4183 ≤ (34613666577593/100000000000000 : ℝ)^3159
        have hw : |(44878669/100000000 : ℝ)|=(44878669/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118200253/5000000000 : ℝ)|^4183 ≤ (32069109013903/100000000000000 : ℝ)^3159
        have hw : |(2118200253/5000000000 : ℝ)|=(2118200253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s7_8 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69282233/10000000000 : ℝ)*x 0 + (2959218931/5000000000 : ℝ)*x 1 + (591847707/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69282233/10000000000 : ℝ)^4183 ≤ (138245982691/100000000000000 : ℝ)^3159 := by
    have hnat : (69282233 : ℕ)^4183*100000000000000^3159 ≤ 138245982691^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69282233 10000000000 138245982691 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2959218931/5000000000 : ℝ)^4183 ≤ (49930658000347/100000000000000 : ℝ)^3159 := by
    have hnat : (2959218931 : ℕ)^4183*100000000000000^3159 ≤ 49930658000347^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2959218931 5000000000 49930658000347 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (591847707/1000000000 : ℝ)^4183 ≤ (49931095999823/100000000000000 : ℝ)^3159 := by
    have hnat : (591847707 : ℕ)^4183*100000000000000^3159 ≤ 49931095999823^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591847707 1000000000 49931095999823 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69282233/10000000000 : ℝ), (2959218931/5000000000 : ℝ), (591847707/1000000000 : ℝ)] ![(138245982691/100000000000000 : ℝ), (49930658000347/100000000000000 : ℝ), (49931095999823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69282233/10000000000 : ℝ)|^4183 ≤ (138245982691/100000000000000 : ℝ)^3159
        have hw : |(-69282233/10000000000 : ℝ)|=(69282233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2959218931/5000000000 : ℝ)|^4183 ≤ (49930658000347/100000000000000 : ℝ)^3159
        have hw : |(2959218931/5000000000 : ℝ)|=(2959218931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(591847707/1000000000 : ℝ)|^4183 ≤ (49931095999823/100000000000000 : ℝ)^3159
        have hw : |(591847707/1000000000 : ℝ)|=(591847707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1173_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11393/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14067/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11387/100000 : ℝ) ^ (8365/2048 : ℝ) ≤ (6996803477299427/50000000000000000000 : ℝ) := by
    have hpowers : (11387/100000 : ℝ)^8365 ≤ (6996803477299427/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11387 : ℕ)^8365*50000000000000000000^2048 ≤ 6996803477299427^2048*100000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11387 100000 6996803477299427 50000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11387/100000 : ℝ)) (X := (6996803477299427/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14073/100000 : ℝ) ^ (8365/2048 : ℝ) ≤ (2077249817191211/6250000000000000000 : ℝ) := by
    have hpowers : (14073/100000 : ℝ)^8365 ≤ (2077249817191211/6250000000000000000 : ℝ)^2048 := by
      have hnat : (14073 : ℕ)^8365*6250000000000000000^2048 ≤ 2077249817191211^2048*100000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14073 100000 2077249817191211 6250000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14073/100000 : ℝ)) (X := (2077249817191211/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006996803477299427/25000000000000000000 : ℝ) ≤ (5000342568786521/5000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (25006996803477299427/25000000000000000000 : ℝ)^2048 ≤ (5000342568786521/5000000000000000 : ℝ)^8365 := by
      have hnat : (25006996803477299427 : ℕ)^2048*5000000000000000^8365 ≤ 5000342568786521^8365*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006996803477299427 25000000000000000000 5000342568786521 5000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000342568786521/5000000000000000 : ℝ)) (X := (25006996803477299427/25000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004722960402965823/10000000000000000000 : ℝ) ≤ (2500289028644463/2500000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (10004722960402965823/10000000000000000000 : ℝ)^2048 ≤ (2500289028644463/2500000000000000 : ℝ)^8365 := by
      have hnat : (10004722960402965823 : ℕ)^2048*2500000000000000^8365 ≤ 2500289028644463^8365*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004722960402965823 10000000000000000000 2500289028644463 2500000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500289028644463/2500000000000000 : ℝ)) (X := (10004722960402965823/10000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127077249817191211/3125000000000000000 : ℝ) ≤ (5000813545791331/5000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (3127077249817191211/3125000000000000000 : ℝ)^2048 ≤ (5000813545791331/5000000000000000 : ℝ)^8365 := by
      have hnat : (3127077249817191211 : ℕ)^2048*5000000000000000^8365 ≤ 5000813545791331^8365*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127077249817191211 3125000000000000000 5000813545791331 5000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000813545791331/5000000000000000 : ℝ)) (X := (3127077249817191211/3125000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6996803477299427/50000000000000000000 : ℝ) ≤ ((26221791258997703/26230468750000000 : ℝ)+2*(47097700481/26860000000000 : ℝ)*(11387/100000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (26221791258997703/26230468750000000 : ℝ)+2*(47097700481/26860000000000 : ℝ)*(11387/100000 : ℝ)=(5000342568786521/5000000000000000 : ℝ) by norm_num, show 1+2*(6996803477299427/50000000000000000000 : ℝ)=(25006996803477299427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2077249817191211/6250000000000000000 : ℝ)+(6996803477299427/50000000000000000000 : ℝ) ≤ ((26221791258997703/26230468750000000 : ℝ)+(47097700481/26860000000000 : ℝ)*((14073/100000 : ℝ)+(11387/100000 : ℝ)))^(8365/2048 : ℝ) := by
    rw [show (26221791258997703/26230468750000000 : ℝ)+(47097700481/26860000000000 : ℝ)*((14073/100000 : ℝ)+(11387/100000 : ℝ))=(2500289028644463/2500000000000000 : ℝ) by norm_num, show 1+(2077249817191211/6250000000000000000 : ℝ)+(6996803477299427/50000000000000000000 : ℝ)=(10004722960402965823/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2077249817191211/6250000000000000000 : ℝ) ≤ ((26221791258997703/26230468750000000 : ℝ)+2*(47097700481/26860000000000 : ℝ)*(14073/100000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (26221791258997703/26230468750000000 : ℝ)+2*(47097700481/26860000000000 : ℝ)*(14073/100000 : ℝ)=(5000813545791331/5000000000000000 : ℝ) by norm_num, show 1+2*(2077249817191211/6250000000000000000 : ℝ)=(3127077249817191211/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26221791258997703/26230468750000000 : ℝ)*(X 1 0+X 2 0)+(47097700481/26860000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (26221791258997703/26230468750000000 : ℝ)) (alpha := (47097700481/26860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26221791258997703/26230468750000000 : ℝ)*(X 0 1+X 2 1)+(47097700481/26860000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (26221791258997703/26230468750000000 : ℝ)) (alpha := (47097700481/26860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26221791258997703/26230468750000000 : ℝ)*(X 0 2+X 1 2)+(47097700481/26860000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (26221791258997703/26230468750000000 : ℝ)) (alpha := (47097700481/26860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2152147267/10000000000 : ℝ)*X 0 0+(5392484563/10000000000 : ℝ)*X 0 1+(1316553541/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344639501/10000000000 : ℝ)*X 1 0+(-1108092973/5000000000 : ℝ)*X 1 1+(2633107253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344640783/10000000000 : ℝ)*X 2 0+(5266212583/10000000000 : ℝ)*X 2 1+(-2216186787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180161501/5000000000 : ℝ)*X 0 0+(4235762263/10000000000 : ℝ)*X 0 1+(140265729/312500000 : ℝ)*X 0 2+(2180161501/5000000000 : ℝ)*X 1 0+(4235762263/10000000000 : ℝ)*X 1 1+(140265729/312500000 : ℝ)*X 1 2+(2180161501/5000000000 : ℝ)*X 2 0+(4235762263/10000000000 : ℝ)*X 2 1+(140265729/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-538038147/2500000000 : ℝ)*X 0 0+(1053306307/2000000000 : ℝ)*X 0 1+(5392165663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312575583/10000000000 : ℝ)*X 1 0+(-2090235133/10000000000 : ℝ)*X 1 1+(5392165663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312575593/10000000000 : ℝ)*X 2 0+(1078433131/2000000000 : ℝ)*X 2 1+(-209023513/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436033313/1000000000 : ℝ)*X 0 0+(44878669/100000000 : ℝ)*X 0 1+(2118200253/5000000000 : ℝ)*X 0 2+(436033313/1000000000 : ℝ)*X 1 0+(44878669/100000000 : ℝ)*X 1 1+(2118200253/5000000000 : ℝ)*X 1 2+(436033313/1000000000 : ℝ)*X 2 0+(44878669/100000000 : ℝ)*X 2 1+(2118200253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-69282233/10000000000 : ℝ)*X 0 0+(2959218931/5000000000 : ℝ)*X 0 1+(591847707/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29957142121806325570650903/10492187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (265466921/25000000000000 : ℝ)*(lower2) + (4842669/10000000000000 : ℝ)*(lower3) + (92331109/50000000000000 : ℝ)*(lower4) + (1181810699/100000000000000 : ℝ)*(lower5) + (2969042992459037/50000000000000 : ℝ)*(major0) + (2969042992459037/50000000000000 : ℝ)*(major1) + (2969042992459037/50000000000000 : ℝ)*(major2) + (1979881144852217/25000000000000 : ℝ)*(sp0) + (989941184285593/12500000000000 : ℝ)*(sp1) + (3959743206284383/50000000000000 : ℝ)*(sp2) + (494576305831787/12500000000000 : ℝ)*(sp3) + (21530857989/50000000000000 : ℝ)*(sp6) + (31953724249/100000000000000 : ℝ)*(sp7) + (1223718969/25000000000000 : ℝ)*(sp8) + (247290150023659/6250000000000 : ℝ)*(f.failure) + (989941184285593/12500000000000 : ℝ)*(f.sum) + (9730840551/67150000000000000000000000 : ℝ)*base66 + (265160976204574699/20984375000000000000000000000000 : ℝ)*base68 + (344384230226206551/20984375000000000000000000000000 : ℝ)*base69 + (357276569577206551/20984375000000000000000000000000 : ℝ)*base71 + (1750521949469/671500000000000000000000000 : ℝ)*base74 + (8495877299668449/20984375000000000000000000000000 : ℝ)*base76 + (93309079358480949/20984375000000000000000000000000 : ℝ)*base78 + (142070753198262199/20984375000000000000000000000000 : ℝ)*base80 + (4107811267853/671500000000000000000000000 : ℝ)*base82 + (909997/125000000000000000000 : ℝ)*base89 + (909997/125000000000000000000 : ℝ)*base91 + (909997/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5143182658973088318477/1343000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201902237/100000000000000 : ℝ)*(lower2) + (53318429/100000000000000 : ℝ)*(lower3) + (12121413/6250000000000 : ℝ)*(lower4) + (14196707/25000000000000 : ℝ)*(lower5) + (2984076371354753/50000000000000 : ℝ)*(major0) + (2984076371354753/50000000000000 : ℝ)*(major1) + (2984076371354753/50000000000000 : ℝ)*(major2) + (632281951/20000000000000 : ℝ)*(sp0) + (25239217/3125000000000 : ℝ)*(sp3) + (795962406103647/10000000000000 : ℝ)*(sp4) + (7959628992061253/100000000000000 : ℝ)*(sp5) + (7959628992061253/100000000000000 : ℝ)*(sp6) + (994168889512183/25000000000000 : ℝ)*(sp7) + (442403757/25000000000000 : ℝ)*(sp8) + (159067054628147/4000000000000 : ℝ)*(f.failure) + (7959628992061253/100000000000000 : ℝ)*(f.sum) + (28656643231789/1343000000000000000000000000 : ℝ)*base65 + (27565841448982561/5246093750000000000000000000000 : ℝ)*base67 + (270372327889477119/20984375000000000000000000000000 : ℝ)*base69 + (30798870666767439/5246093750000000000000000000000 : ℝ)*base72 + (6931387316703/1343000000000000000000000000 : ℝ)*base74 + (2749011141482561/5246093750000000000000000000000 : ℝ)*base75 + (60764793113144253/10492187500000000000000000000000 : ℝ)*base78 + (66907294535204939/5246093750000000000000000000000 : ℝ)*base80 + (87978093697/167875000000000000000000000 : ℝ)*base82 + (1244101/80000000000000000000 : ℝ)*base89 + (1244101/80000000000000000000 : ℝ)*base91 + (1244101/80000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1173_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1173_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1173_s8_0 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-86086079/400000000 : ℝ)*x 0 + (2696212889/5000000000 : ℝ)*x 1 + (5266269879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86086079/400000000 : ℝ)^4183 ≤ (3270103988153/25000000000000 : ℝ)^3159 := by
    have hnat : (86086079 : ℕ)^4183*25000000000000^3159 ≤ 3270103988153^3159*400000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86086079 400000000 3270103988153 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696212889/5000000000 : ℝ)^4183 ≤ (44140897071083/100000000000000 : ℝ)^3159 := by
    have hnat : (2696212889 : ℕ)^4183*100000000000000^3159 ≤ 44140897071083^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696212889 5000000000 44140897071083 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266269879/10000000000 : ℝ)^4183 ≤ (42778686957837/100000000000000 : ℝ)^3159 := by
    have hnat : (5266269879 : ℕ)^4183*100000000000000^3159 ≤ 42778686957837^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266269879 10000000000 42778686957837 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86086079/400000000 : ℝ), (2696212889/5000000000 : ℝ), (5266269879/10000000000 : ℝ)] ![(3270103988153/25000000000000 : ℝ), (44140897071083/100000000000000 : ℝ), (42778686957837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86086079/400000000 : ℝ)|^4183 ≤ (3270103988153/25000000000000 : ℝ)^3159
        have hw : |(-86086079/400000000 : ℝ)|=(86086079/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696212889/5000000000 : ℝ)|^4183 ≤ (44140897071083/100000000000000 : ℝ)^3159
        have hw : |(2696212889/5000000000 : ℝ)|=(2696212889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266269879/10000000000 : ℝ)|^4183 ≤ (42778686957837/100000000000000 : ℝ)^3159
        have hw : |(5266269879/10000000000 : ℝ)|=(5266269879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s8_1 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344624891/10000000000 : ℝ)*x 0 + (-17729057/80000000 : ℝ)*x 1 + (5266269841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344624891/10000000000 : ℝ)^4183 ≤ (43623521984123/100000000000000 : ℝ)^3159 := by
    have hnat : (5344624891 : ℕ)^4183*100000000000000^3159 ≤ 43623521984123^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344624891 10000000000 43623521984123 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17729057/80000000 : ℝ)^4183 ≤ (6798895729863/50000000000000 : ℝ)^3159 := by
    have hnat : (17729057 : ℕ)^4183*50000000000000^3159 ≤ 6798895729863^3159*80000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17729057 80000000 6798895729863 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266269841/10000000000 : ℝ)^4183 ≤ (21389343274549/50000000000000 : ℝ)^3159 := by
    have hnat : (5266269841 : ℕ)^4183*50000000000000^3159 ≤ 21389343274549^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266269841 10000000000 21389343274549 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344624891/10000000000 : ℝ), (-17729057/80000000 : ℝ), (5266269841/10000000000 : ℝ)] ![(43623521984123/100000000000000 : ℝ), (6798895729863/50000000000000 : ℝ), (21389343274549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344624891/10000000000 : ℝ)|^4183 ≤ (43623521984123/100000000000000 : ℝ)^3159
        have hw : |(5344624891/10000000000 : ℝ)|=(5344624891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17729057/80000000 : ℝ)|^4183 ≤ (6798895729863/50000000000000 : ℝ)^3159
        have hw : |(-17729057/80000000 : ℝ)|=(17729057/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266269841/10000000000 : ℝ)|^4183 ≤ (21389343274549/50000000000000 : ℝ)^3159
        have hw : |(5266269841/10000000000 : ℝ)|=(5266269841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s8_2 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344624849/10000000000 : ℝ)*x 0 + (42130159/80000000 : ℝ)*x 1 + (-443226427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344624849/10000000000 : ℝ)^4183 ≤ (43623521530191/100000000000000 : ℝ)^3159 := by
    have hnat : (5344624849 : ℕ)^4183*100000000000000^3159 ≤ 43623521530191^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344624849 10000000000 43623521530191 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42130159/80000000 : ℝ)^4183 ≤ (10694671728703/25000000000000 : ℝ)^3159 := by
    have hnat : (42130159 : ℕ)^4183*25000000000000^3159 ≤ 10694671728703^3159*80000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42130159 80000000 10694671728703 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443226427/2000000000 : ℝ)^4183 ≤ (13597791540973/100000000000000 : ℝ)^3159 := by
    have hnat : (443226427 : ℕ)^4183*100000000000000^3159 ≤ 13597791540973^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443226427 2000000000 13597791540973 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344624849/10000000000 : ℝ), (42130159/80000000 : ℝ), (-443226427/2000000000 : ℝ)] ![(43623521530191/100000000000000 : ℝ), (10694671728703/25000000000000 : ℝ), (13597791540973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344624849/10000000000 : ℝ)|^4183 ≤ (43623521530191/100000000000000 : ℝ)^3159
        have hw : |(5344624849/10000000000 : ℝ)|=(5344624849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42130159/80000000 : ℝ)|^4183 ≤ (10694671728703/25000000000000 : ℝ)^3159
        have hw : |(42130159/80000000 : ℝ)|=(42130159/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-443226427/2000000000 : ℝ)|^4183 ≤ (13597791540973/100000000000000 : ℝ)^3159
        have hw : |(-443226427/2000000000 : ℝ)|=(443226427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s8_3 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360326373/10000000000 : ℝ)*x 0 + (4235876683/10000000000 : ℝ)*x 1 + (2244193849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360326373/10000000000 : ℝ)^4183 ≤ (33317156017011/100000000000000 : ℝ)^3159 := by
    have hnat : (4360326373 : ℕ)^4183*100000000000000^3159 ≤ 33317156017011^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360326373 10000000000 33317156017011 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235876683/10000000000 : ℝ)^4183 ≤ (16031929236893/50000000000000 : ℝ)^3159 := by
    have hnat : (4235876683 : ℕ)^4183*50000000000000^3159 ≤ 16031929236893^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235876683 10000000000 16031929236893 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244193849/5000000000 : ℝ)^4183 ≤ (17309492748147/50000000000000 : ℝ)^3159 := by
    have hnat : (2244193849 : ℕ)^4183*50000000000000^3159 ≤ 17309492748147^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244193849 5000000000 17309492748147 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360326373/10000000000 : ℝ), (4235876683/10000000000 : ℝ), (2244193849/5000000000 : ℝ)] ![(33317156017011/100000000000000 : ℝ), (16031929236893/50000000000000 : ℝ), (17309492748147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360326373/10000000000 : ℝ)|^4183 ≤ (33317156017011/100000000000000 : ℝ)^3159
        have hw : |(4360326373/10000000000 : ℝ)|=(4360326373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235876683/10000000000 : ℝ)|^4183 ≤ (16031929236893/50000000000000 : ℝ)^3159
        have hw : |(4235876683/10000000000 : ℝ)|=(4235876683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244193849/5000000000 : ℝ)|^4183 ≤ (17309492748147/50000000000000 : ℝ)^3159
        have hw : |(2244193849/5000000000 : ℝ)|=(2244193849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s8_4 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152156553/10000000000 : ℝ)*x 0 + (1316646599/2500000000 : ℝ)*x 1 + (215684331/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152156553/10000000000 : ℝ)^4183 ≤ (6540226398137/50000000000000 : ℝ)^3159 := by
    have hnat : (2152156553 : ℕ)^4183*50000000000000^3159 ≤ 6540226398137^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152156553 10000000000 6540226398137 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316646599/2500000000 : ℝ)^4183 ≤ (42782091540229/100000000000000 : ℝ)^3159 := by
    have hnat : (1316646599 : ℕ)^4183*100000000000000^3159 ≤ 42782091540229^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316646599 2500000000 42782091540229 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215684331/400000000 : ℝ)^4183 ≤ (5517181955169/12500000000000 : ℝ)^3159 := by
    have hnat : (215684331 : ℕ)^4183*12500000000000^3159 ≤ 5517181955169^3159*400000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215684331 400000000 5517181955169 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152156553/10000000000 : ℝ), (1316646599/2500000000 : ℝ), (215684331/400000000 : ℝ)] ![(6540226398137/50000000000000 : ℝ), (42782091540229/100000000000000 : ℝ), (5517181955169/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152156553/10000000000 : ℝ)|^4183 ≤ (6540226398137/50000000000000 : ℝ)^3159
        have hw : |(-2152156553/10000000000 : ℝ)|=(2152156553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316646599/2500000000 : ℝ)|^4183 ≤ (42782091540229/100000000000000 : ℝ)^3159
        have hw : |(1316646599/2500000000 : ℝ)|=(1316646599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215684331/400000000 : ℝ)|^4183 ≤ (5517181955169/12500000000000 : ℝ)^3159
        have hw : |(215684331/400000000 : ℝ)|=(215684331/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s8_5 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312590409/10000000000 : ℝ)*x 0 + (-261286853/1250000000 : ℝ)*x 1 + (1348026751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312590409/10000000000 : ℝ)^4183 ≤ (1352426030327/3125000000000 : ℝ)^3159 := by
    have hnat : (5312590409 : ℕ)^4183*3125000000000^3159 ≤ 1352426030327^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312590409 10000000000 1352426030327 3125000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261286853/1250000000 : ℝ)^4183 ≤ (12584925145141/100000000000000 : ℝ)^3159 := by
    have hnat : (261286853 : ℕ)^4183*100000000000000^3159 ≤ 12584925145141^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261286853 1250000000 12584925145141 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348026751/2500000000 : ℝ)^4183 ≤ (44137441865057/100000000000000 : ℝ)^3159 := by
    have hnat : (1348026751 : ℕ)^4183*100000000000000^3159 ≤ 44137441865057^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348026751 2500000000 44137441865057 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312590409/10000000000 : ℝ), (-261286853/1250000000 : ℝ), (1348026751/2500000000 : ℝ)] ![(1352426030327/3125000000000 : ℝ), (12584925145141/100000000000000 : ℝ), (44137441865057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312590409/10000000000 : ℝ)|^4183 ≤ (1352426030327/3125000000000 : ℝ)^3159
        have hw : |(5312590409/10000000000 : ℝ)|=(5312590409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261286853/1250000000 : ℝ)|^4183 ≤ (12584925145141/100000000000000 : ℝ)^3159
        have hw : |(-261286853/1250000000 : ℝ)|=(261286853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348026751/2500000000 : ℝ)|^4183 ≤ (44137441865057/100000000000000 : ℝ)^3159
        have hw : |(1348026751/2500000000 : ℝ)|=(1348026751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s8_6 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312589791/10000000000 : ℝ)*x 0 + (1348026977/2500000000 : ℝ)*x 1 + (-65321701/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312589791/10000000000 : ℝ)^4183 ≤ (43277626304179/100000000000000 : ℝ)^3159 := by
    have hnat : (5312589791 : ℕ)^4183*100000000000000^3159 ≤ 43277626304179^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312589791 10000000000 43277626304179 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348026977/2500000000 : ℝ)^4183 ≤ (2206872583173/5000000000000 : ℝ)^3159 := by
    have hnat : (1348026977 : ℕ)^4183*5000000000000^3159 ≤ 2206872583173^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348026977 2500000000 2206872583173 5000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65321701/312500000 : ℝ)^4183 ≤ (786557626251/6250000000000 : ℝ)^3159 := by
    have hnat : (65321701 : ℕ)^4183*6250000000000^3159 ≤ 786557626251^3159*312500000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65321701 312500000 786557626251 6250000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312589791/10000000000 : ℝ), (1348026977/2500000000 : ℝ), (-65321701/312500000 : ℝ)] ![(43277626304179/100000000000000 : ℝ), (2206872583173/5000000000000 : ℝ), (786557626251/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312589791/10000000000 : ℝ)|^4183 ≤ (43277626304179/100000000000000 : ℝ)^3159
        have hw : |(5312589791/10000000000 : ℝ)|=(5312589791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348026977/2500000000 : ℝ)|^4183 ≤ (2206872583173/5000000000000 : ℝ)^3159
        have hw : |(1348026977/2500000000 : ℝ)|=(1348026977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65321701/312500000 : ℝ)|^4183 ≤ (786557626251/6250000000000 : ℝ)^3159
        have hw : |(-65321701/312500000 : ℝ)|=(65321701/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s8_7 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872067263/2000000000 : ℝ)*x 0 + (4487752669/10000000000 : ℝ)*x 1 + (4236513677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872067263/2000000000 : ℝ)^4183 ≤ (6663451321693/20000000000000 : ℝ)^3159 := by
    have hnat : (872067263 : ℕ)^4183*20000000000000^3159 ≤ 6663451321693^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872067263 2000000000 6663451321693 20000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487752669/10000000000 : ℝ)^4183 ≤ (34612499961231/100000000000000 : ℝ)^3159 := by
    have hnat : (4487752669 : ℕ)^4183*100000000000000^3159 ≤ 34612499961231^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487752669 10000000000 34612499961231 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236513677/10000000000 : ℝ)^4183 ≤ (32070243411127/100000000000000 : ℝ)^3159 := by
    have hnat : (4236513677 : ℕ)^4183*100000000000000^3159 ≤ 32070243411127^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236513677 10000000000 32070243411127 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872067263/2000000000 : ℝ), (4487752669/10000000000 : ℝ), (4236513677/10000000000 : ℝ)] ![(6663451321693/20000000000000 : ℝ), (34612499961231/100000000000000 : ℝ), (32070243411127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872067263/2000000000 : ℝ)|^4183 ≤ (6663451321693/20000000000000 : ℝ)^3159
        have hw : |(872067263/2000000000 : ℝ)|=(872067263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487752669/10000000000 : ℝ)|^4183 ≤ (34612499961231/100000000000000 : ℝ)^3159
        have hw : |(4487752669/10000000000 : ℝ)|=(4487752669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236513677/10000000000 : ℝ)|^4183 ≤ (32070243411127/100000000000000 : ℝ)^3159
        have hw : |(4236513677/10000000000 : ℝ)|=(4236513677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1173_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5697/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7033/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11393/100000 : ℝ) ^ (8365/2048 : ℝ) ≤ (14023748151964541/100000000000000000000 : ℝ) := by
    have hpowers : (11393/100000 : ℝ)^8365 ≤ (14023748151964541/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11393 : ℕ)^8365*100000000000000000000^2048 ≤ 14023748151964541^2048*100000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11393 100000 14023748151964541 100000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11393/100000 : ℝ)) (X := (14023748151964541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14067/100000 : ℝ) ^ (8365/2048 : ℝ) ≤ (33178157686010393/100000000000000000000 : ℝ) := by
    have hpowers : (14067/100000 : ℝ)^8365 ≤ (33178157686010393/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14067 : ℕ)^8365*100000000000000000000^2048 ≤ 33178157686010393^2048*100000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14067 100000 33178157686010393 100000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14067/100000 : ℝ)) (X := (33178157686010393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014023748151964541/50000000000000000000 : ℝ) ≤ (2500171653288149/2500000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (50014023748151964541/50000000000000000000 : ℝ)^2048 ≤ (2500171653288149/2500000000000000 : ℝ)^8365 := by
      have hnat : (50014023748151964541 : ℕ)^2048*2500000000000000^8365 ≤ 2500171653288149^8365*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014023748151964541 50000000000000000000 2500171653288149 2500000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500171653288149/2500000000000000 : ℝ)) (X := (50014023748151964541/50000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023600952918987467/50000000000000000000 : ℝ) ≤ (78134026849107/78125000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (50023600952918987467/50000000000000000000 : ℝ)^2048 ≤ (78134026849107/78125000000000 : ℝ)^8365 := by
      have hnat : (50023600952918987467 : ℕ)^2048*78125000000000^8365 ≤ 78134026849107^8365*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023600952918987467 50000000000000000000 78134026849107 78125000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78134026849107/78125000000000 : ℝ)) (X := (50023600952918987467/50000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033178157686010393/50000000000000000000 : ℝ) ≤ (2500406065054699/2500000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (50033178157686010393/50000000000000000000 : ℝ)^2048 ≤ (2500406065054699/2500000000000000 : ℝ)^8365 := by
      have hnat : (50033178157686010393 : ℕ)^2048*2500000000000000^8365 ≤ 2500406065054699^8365*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033178157686010393 50000000000000000000 2500406065054699 2500000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500406065054699/2500000000000000 : ℝ)) (X := (50033178157686010393/50000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14023748151964541/100000000000000000000 : ℝ) ≤ ((1670697086909051569/1671250000000000000 : ℝ)+2*(4688235331/2674000000000 : ℝ)*(11393/100000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (1670697086909051569/1671250000000000000 : ℝ)+2*(4688235331/2674000000000 : ℝ)*(11393/100000 : ℝ)=(2500171653288149/2500000000000000 : ℝ) by norm_num, show 1+2*(14023748151964541/100000000000000000000 : ℝ)=(50014023748151964541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33178157686010393/100000000000000000000 : ℝ)+(14023748151964541/100000000000000000000 : ℝ) ≤ ((1670697086909051569/1671250000000000000 : ℝ)+(4688235331/2674000000000 : ℝ)*((14067/100000 : ℝ)+(11393/100000 : ℝ)))^(8365/2048 : ℝ) := by
    rw [show (1670697086909051569/1671250000000000000 : ℝ)+(4688235331/2674000000000 : ℝ)*((14067/100000 : ℝ)+(11393/100000 : ℝ))=(78134026849107/78125000000000 : ℝ) by norm_num, show 1+(33178157686010393/100000000000000000000 : ℝ)+(14023748151964541/100000000000000000000 : ℝ)=(50023600952918987467/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33178157686010393/100000000000000000000 : ℝ) ≤ ((1670697086909051569/1671250000000000000 : ℝ)+2*(4688235331/2674000000000 : ℝ)*(14067/100000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (1670697086909051569/1671250000000000000 : ℝ)+2*(4688235331/2674000000000 : ℝ)*(14067/100000 : ℝ)=(2500406065054699/2500000000000000 : ℝ) by norm_num, show 1+2*(33178157686010393/100000000000000000000 : ℝ)=(50033178157686010393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1670697086909051569/1671250000000000000 : ℝ)*(X 1 0+X 2 0)+(4688235331/2674000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (1670697086909051569/1671250000000000000 : ℝ)) (alpha := (4688235331/2674000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1670697086909051569/1671250000000000000 : ℝ)*(X 0 1+X 2 1)+(4688235331/2674000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (1670697086909051569/1671250000000000000 : ℝ)) (alpha := (4688235331/2674000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1670697086909051569/1671250000000000000 : ℝ)*(X 0 2+X 1 2)+(4688235331/2674000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (1670697086909051569/1671250000000000000 : ℝ)) (alpha := (4688235331/2674000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-86086079/400000000 : ℝ)*X 0 0+(2696212889/5000000000 : ℝ)*X 0 1+(5266269879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344624891/10000000000 : ℝ)*X 1 0+(-17729057/80000000 : ℝ)*X 1 1+(5266269841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344624849/10000000000 : ℝ)*X 2 0+(42130159/80000000 : ℝ)*X 2 1+(-443226427/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360326373/10000000000 : ℝ)*X 0 0+(4235876683/10000000000 : ℝ)*X 0 1+(2244193849/5000000000 : ℝ)*X 0 2+(4360326373/10000000000 : ℝ)*X 1 0+(4235876683/10000000000 : ℝ)*X 1 1+(2244193849/5000000000 : ℝ)*X 1 2+(4360326373/10000000000 : ℝ)*X 2 0+(4235876683/10000000000 : ℝ)*X 2 1+(2244193849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2152156553/10000000000 : ℝ)*X 0 0+(1316646599/2500000000 : ℝ)*X 0 1+(215684331/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312590409/10000000000 : ℝ)*X 1 0+(-261286853/1250000000 : ℝ)*X 1 1+(1348026751/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312589791/10000000000 : ℝ)*X 2 0+(1348026977/2500000000 : ℝ)*X 2 1+(-65321701/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872067263/2000000000 : ℝ)*X 0 0+(4487752669/10000000000 : ℝ)*X 0 1+(4236513677/10000000000 : ℝ)*X 0 2+(872067263/2000000000 : ℝ)*X 1 0+(4487752669/10000000000 : ℝ)*X 1 1+(4236513677/10000000000 : ℝ)*X 1 2+(872067263/2000000000 : ℝ)*X 2 0+(4487752669/10000000000 : ℝ)*X 2 1+(4236513677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27212775526483460926984431/5968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (968687061/100000000000000 : ℝ)*(base19) + (420091029/50000000000000 : ℝ)*(base23) + (2211797/6250000000000 : ℝ)*(lower2) + (129832229/100000000000000 : ℝ)*(upper3) + (52733601/100000000000000 : ℝ)*(upper5) + (2971750390699419/50000000000000 : ℝ)*(major0) + (2971750390699419/50000000000000 : ℝ)*(major1) + (2971750390699419/50000000000000 : ℝ)*(major2) + (3963363657856503/50000000000000 : ℝ)*(sp0) + (396337503779447/5000000000000 : ℝ)*(sp1) + (7926750204093943/100000000000000 : ℝ)*(sp2) + (1980117990573491/50000000000000 : ℝ)*(sp3) + (4745712599/20000000000000 : ℝ)*(sp4) + (1438540107/10000000000000 : ℝ)*(sp7) + (990062591637013/25000000000000 : ℝ)*(f.failure) + (7926751044276001/100000000000000 : ℝ)*(f.sum) + (558012832599/191000000000000000000000000 : ℝ)*base65 + (229824817571505227/11937500000000000000000000000000 : ℝ)*base68 + (35130018322807273/11937500000000000000000000000000 : ℝ)*base69 + (127393437957744773/11937500000000000000000000000000 : ℝ)*base71 + (86455568167/23875000000000000000000000 : ℝ)*base74 + (190853167329130227/11937500000000000000000000000000 : ℝ)*base76 + (19002321907932273/11937500000000000000000000000000 : ℝ)*base77 + (13812604586807273/11937500000000000000000000000000 : ℝ)*base79 + (543356778029/191000000000000000000000000 : ℝ)*base81 + (6976179/500000000000000000000 : ℝ)*base89 + (6976179/500000000000000000000 : ℝ)*base91 + (6976179/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59672344531985261074079643/10445312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (604007063/50000000000000 : ℝ)*(base19) + (30282779/25000000000000 : ℝ)*(base23) + (114499603/50000000000000 : ℝ)*(lower2) + (124665281/100000000000000 : ℝ)*(lower4) + (96009337/50000000000000 : ℝ)*(upper5) + (23334144378393/390625000000 : ℝ)*(major0) + (23334144378393/390625000000 : ℝ)*(major1) + (23334144378393/390625000000 : ℝ)*(major2) + (36232360893/100000000000000 : ℝ)*(sp0) + (6014243817/100000000000000 : ℝ)*(sp2) + (3983389438319707/50000000000000 : ℝ)*(sp4) + (398340695049309/5000000000000 : ℝ)*(sp5) + (7966808973625373/100000000000000 : ℝ)*(sp6) + (995066655577269/25000000000000 : ℝ)*(sp7) + (995066655577269/25000000000000 : ℝ)*(f.failure) + (3983407554500153/50000000000000 : ℝ)*(f.sum) + (13775090123629/1337000000000000000000000000 : ℝ)*base65 + (78410383876780997/10445312500000000000000000000000 : ℝ)*base67 + (142889024968265119/20890625000000000000000000000000 : ℝ)*base69 + (5157277561932633/652832031250000000000000000000 : ℝ)*base72 + (1642305893777/334250000000000000000000000 : ℝ)*base74 + (38849520534835811/5222656250000000000000000000000 : ℝ)*base75 + (1223454770097593/2611328125000000000000000000000 : ℝ)*base77 + (143434980702016131/20890625000000000000000000000000 : ℝ)*base80 + (7863785185597/1337000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (6036627/500000000000000000000 : ℝ)*base89 + (6036627/500000000000000000000 : ℝ)*base91 + (6036627/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1173_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1173_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1173_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1173_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1173_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1173_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1173_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
